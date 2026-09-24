// realdata_main.cpp
//
// Runs LS, GLS, NOMP, KNOMP, and LS+KR on one HARPS RVBank star and matches
// each method's n_known detected components to the catalog's known planets
// (nearest period, optimal one-to-one assignment by brute-force permutation
// since n_known <= ~6). Writes a JSON result file per star.
//
// Build: see Makefile in this directory.
// Usage: ./realdata_main <star_csv_path> <star_name> <P1,e1;P2,e2;...> <out_json>
//   where P_i,e_i are the known (period_days, eccentricity) pairs, comma-
//   separated per planet, semicolon-separated between planets, sorted by
//   period ascending (as extracted from harps_gt80obs_planets_orbital_parameters.csv).

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <algorithm>
#include <functional>
#include <chrono>
#include "nk_kepler.hpp"
#include "nk_optimize.hpp"
#include "nk_realdata.hpp"
#include "nk_lskr.hpp"
#include "nk_l1periodogram.hpp"
#include "json.hpp"

using nlohmann::json;
using namespace nk;

// Build the lower-triangular Cholesky factor L such that Sigma = L L^T,
// where Sigma = build_covariance(t, sigma2_n, hp). When hp.sigma_R2 == 0
// (the GP search collapsed into jitter-only -- estimate_gp_hyperparams
// returns exactly 0.0 in both the cap-path and the full-GP jitter-wins
// branch), Sigma is strictly diagonal: Sigma = diag(sigma2_n + sigma2_jit).
// Skip the O(N^3) Eigen LLT + N^2 matrix copy and build L directly as a
// diagonal matrix with L(i,i) = sqrt(sigma2_n(i) + sigma2_jit), which is
// the bit-identical result of LLT(diag).matrixL() for a positive-diagonal
// input. Downstream triangular solves (L.solve(v)) on a diagonal L are
// also bit-identical -- they reduce to per-element division v(i)/L(i,i)
// regardless of how L was constructed. Behavior-invariant.
static inline Eigen::MatrixXd cholesky_L_from_hp(const Eigen::VectorXd &t,
                                                  const Eigen::VectorXd &sigma2_n,
                                                  const GPHyperparams &hp) {
    int n = (int)t.size();
    Eigen::MatrixXd L(n, n);
    if (hp.sigma_R2 == 0.0) {
        L.setZero();
        L.diagonal() = (sigma2_n.array() + hp.sigma2_jit).sqrt();
    } else {
        Eigen::MatrixXd Sigma = build_covariance(t, sigma2_n, hp);
        Eigen::LLT<Eigen::MatrixXd> llt(Sigma);
        L = llt.matrixL();
    }
    return L;
}

// ---------------------------------------------------------------------------
// KNOMP configuration: every tunable lever and feature toggle exposed as a
// CLI flag (--flag or --flag=value), all with the previously-hardcoded
// values as defaults so existing invocations are unaffected. Parsed once in
// main() below.
struct KnompConfig {
    // detection-machinery robustness knobs
    int n_top = 5, n_multistart_e = 4;
    double exclude_tol = 0.06, bracket_frac_final = 0.10, e_hi = 0.97;
    int max_extra = 4;
    // stopping-criterion knobs
    double fap_cfar = 0.01;
    int delta_k = 4;
    bool bic_enabled = true;      // --no-bic: CFAR-only stopping (drop the BIC half of the conjunction)
    // noise-model feature toggles (KNOMP-only, per instruction; baselines never see these)
    bool jitter_enabled = true;   // --no-jitter
    bool gp_enabled = true;       // --no-gp (jitter-only if true stays on, pure sigma_n if jitter also off)
    bool warm_start = true;       // --no-warm-start: always search GP hyperparams from scratch
    int gp_tau_grid = 4, gp_rounds = 2, gp_golden_iters = 12, gp_max_n = 1500;
    double gp_tau_min = 1.0, gp_tau_max_frac = 3.0;
    // alias/sidelobe feature toggles
    bool alias_enabled = true;    // --no-alias: disable both the prospective exclusion and the swap check
    unsigned seed = 12345;
    int n_grid = 5000;

    // method selection (which of LS/GLS/NOMP/KNOMP/LSKR/L1 to actually run).
    // Default = all six (current behavior, used by the full battery). The
    // pre-whitening test only needs LS/GLS/LSKR/L1 and passes
    // --methods=LS,GLS,LSKR,L1 to skip KNOMP (saves the ~12s/HD10180 of
    // eccentric-Kepler fitting) and NOMP (it derives from LS so producing
    // it on a reduced run is meaningless). --methods= takes a CSV; --no-<m>
    // disables one method. Both are mutually compatible (applied in order
    // so the LAST one wins on the same method, mirroring most CLI tools).
    bool run_LS = true, run_GLS = true, run_NOMP = true,
         run_KNOMP = true, run_LSKR = true, run_L1 = true;

    // --prewhiten-non-knomp: dominant-mode residual whitening for the five
    // baseline methods only (LS/GLS/NOMP/LSKR/L1). KNOMP always runs on the
    // original data. Implemented in main() by finding the single strongest
    // GLS peak in [P_min, P_max], fitting (offset, A cos, B sin) via WLS at
    // that period, and subtracting from y before the baseline loops run.
    bool prewhiten_non_knomp = false;

    GPSearchConfig gp_cfg() const {
        GPSearchConfig c;
        c.gp_enabled = gp_enabled; c.jitter_enabled = jitter_enabled;
        c.n_tau_grid = gp_tau_grid; c.rounds = gp_rounds; c.golden_iters = gp_golden_iters;
        c.tau_min_days = gp_tau_min; c.tau_max_frac = gp_tau_max_frac; c.gp_max_n = gp_max_n;
        return c;
    }
};

inline KnompConfig parse_knomp_flags(int argc, char **argv, int start_idx) {
    KnompConfig c;
    for (int i = start_idx; i < argc; ++i) {
        std::string a = argv[i];
        auto val = [&](const std::string &flag) -> std::string {
            auto pos = a.find('=');
            return pos == std::string::npos ? "" : a.substr(pos + 1);
        };
        auto starts = [&](const std::string &s) { return a.rfind(s, 0) == 0; };
        if (starts("--n-top=")) c.n_top = std::atoi(val("--n-top").c_str());
        else if (starts("--n-multistart=")) c.n_multistart_e = std::atoi(val("--n-multistart").c_str());
        else if (starts("--exclude-tol=")) c.exclude_tol = std::atof(val("--exclude-tol").c_str());
        else if (starts("--bracket-frac=")) c.bracket_frac_final = std::atof(val("--bracket-frac").c_str());
        else if (starts("--e-max=")) c.e_hi = std::atof(val("--e-max").c_str());
        else if (starts("--max-extra=")) c.max_extra = std::atoi(val("--max-extra").c_str());
        else if (starts("--fap=")) c.fap_cfar = std::atof(val("--fap").c_str());
        else if (starts("--delta-k=")) c.delta_k = std::atoi(val("--delta-k").c_str());
        else if (a == "--no-bic") c.bic_enabled = false;
        else if (a == "--no-jitter") c.jitter_enabled = false;
        else if (a == "--no-gp") c.gp_enabled = false;
        else if (a == "--no-warm-start") c.warm_start = false;
        else if (a == "--no-alias") c.alias_enabled = false;
        else if (starts("--gp-tau-grid=")) c.gp_tau_grid = std::atoi(val("--gp-tau-grid").c_str());
        else if (starts("--gp-rounds=")) c.gp_rounds = std::atoi(val("--gp-rounds").c_str());
        else if (starts("--gp-golden-iters=")) c.gp_golden_iters = std::atoi(val("--gp-golden-iters").c_str());
        else if (starts("--gp-max-n=")) c.gp_max_n = std::atoi(val("--gp-max-n").c_str());
        else if (starts("--gp-tau-min=")) c.gp_tau_min = std::atof(val("--gp-tau-min").c_str());
        else if (starts("--gp-tau-max-frac=")) c.gp_tau_max_frac = std::atof(val("--gp-tau-max-frac").c_str());
        else if (starts("--seed=")) c.seed = (unsigned)std::atoll(val("--seed").c_str());
        else if (starts("--n-grid=")) c.n_grid = std::atoi(val("--n-grid").c_str());
        else if (a == "--no-ls") c.run_LS = false;
        else if (a == "--no-gls") c.run_GLS = false;
        else if (a == "--no-nomp") c.run_NOMP = false;
        else if (a == "--no-knomp") c.run_KNOMP = false;
        else if (a == "--no-lskr") c.run_LSKR = false;
        else if (a == "--no-l1") c.run_L1 = false;
        else if (a == "--prewhiten-non-knomp") c.prewhiten_non_knomp = true;
        else if (starts("--methods=")) {
            // Whitelist form: --methods=LS,GLS,LSKR,L1 -- resets all to
            // false, then enables exactly those listed. Applied AFTER any
            // --no-<m> flags so the CLI's last-flag-wins convention is
            // preserved.
            c.run_LS = c.run_GLS = c.run_NOMP = c.run_KNOMP = c.run_LSKR = c.run_L1 = false;
            std::string list = val("--methods");
            std::stringstream ss(list);
            std::string m;
            while (std::getline(ss, m, ',')) {
                if (m == "LS") c.run_LS = true;
                else if (m == "GLS") c.run_GLS = true;
                else if (m == "NOMP") c.run_NOMP = true;
                else if (m == "KNOMP") c.run_KNOMP = true;
                else if (m == "LSKR") c.run_LSKR = true;
                else if (m == "L1") c.run_L1 = true;
                else std::cerr << "warning: unknown method '" << m << "' in --methods=\n";
            }
        }
        else std::cerr << "warning: unrecognized KNOMP flag '" << a << "'\n";
    }
    return c;
}


struct KnownPlanet { double P, e; };

std::vector<KnownPlanet> parse_known(const std::string &spec) {
    std::vector<KnownPlanet> out;
    std::stringstream ss(spec);
    std::string planet;
    while (std::getline(ss, planet, ';')) {
        if (planet.empty()) continue;
        std::stringstream ps(planet);
        std::string a, b;
        std::getline(ps, a, ','); std::getline(ps, b, ',');
        out.push_back({std::stod(a), std::stod(b)});
    }
    std::sort(out.begin(), out.end(), [](const KnownPlanet &x, const KnownPlanet &y){ return x.P < y.P; });
    return out;
}

// Optimal one-to-one assignment of detected periods to known periods,
// minimizing sum of |log(P_det/P_known)|, by brute-force permutation
// (n_known is always small: <=6 for every system in this dataset).
std::vector<int> match_periods(const std::vector<double> &det, const std::vector<double> &known) {
    int n = known.size();
    // BUGFIX: the unmatched-planet penalty must correspond to a genuine
    // "no reasonable detection exists" threshold, not an arbitrary large
    // constant. The previous value (5.0 in log-space, i.e. accepting a
    // forced match up to e^5 ~= 148x off in period) let the optimizer force
    // absurd matches (e.g. a 28.2-day detection assigned to a 1.94-day known
    // planet, log-ratio 2.68, because leaving it unmatched cost "5.0" and
    // was therefore judged worse) rather than correctly reporting "not
    // detected." The penalty is now set to the log-ratio corresponding to a
    // MATCH_REL_TOL relative period error, so ANY forced match worse than
    // that tolerance costs strictly more than leaving the planet unmatched,
    // and the optimizer will never again prefer a wild mismatch over "None."
    const double MATCH_REL_TOL = 0.20; // see histogram analysis in the session notes: a natural
                                        // separation point between genuine (often imprecise, long-
                                        // baseline) detections and alias/noise-driven mismatches
    const double UNMATCHED_PENALTY = std::log(1.0 + MATCH_REL_TOL);
    std::vector<int> best_assign(n, -1);
    double best_cost = std::numeric_limits<double>::infinity();
    std::vector<int> assign(n, -1);
    std::function<void(int, std::vector<bool>&)> rec = [&](int k, std::vector<bool> &used) {
        if (k == n) {
            double cost = 0;
            for (int j = 0; j < n; ++j) {
                if (assign[j] < 0) cost += UNMATCHED_PENALTY;
                else cost += std::fabs(std::log(det[assign[j]] / known[j]));
            }
            if (cost < best_cost) { best_cost = cost; best_assign = assign; }
            return;
        }
        // option: leave known[k] unmatched
        assign[k] = -1; rec(k + 1, used);
        for (size_t i = 0; i < det.size(); ++i) {
            if (used[i]) continue;
            used[i] = true; assign[k] = (int)i;
            rec(k + 1, used);
            used[i] = false;
        }
        assign[k] = -1;
    };
    std::vector<bool> used(det.size(), false);
    rec(0, used);
    // Belt-and-suspenders: null out any individual pair that still exceeds
    // the tolerance even in the globally-optimal assignment (this can only
    // happen if forcing it was unavoidable given the cost structure of the
    // OTHER pairs; we never want to report such a pair as a "match").
    for (int j = 0; j < n; ++j) {
        if (best_assign[j] >= 0) {
            double rel_err = std::fabs(det[best_assign[j]] - known[j]) / known[j];
            if (rel_err > MATCH_REL_TOL) best_assign[j] = -1;
        }
    }
    return best_assign;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        std::cerr << "usage: realdata_main <csv> <star> <P,e;P,e;...> <out_json> [n_grid]\n";
        return 1;
    }
    std::string csv_path = argv[1], star = argv[2], known_spec = argv[3], out_path = argv[4];
    int n_grid = argc > 5 ? std::atoi(argv[5]) : 4000;
    KnompConfig kc = parse_knomp_flags(argc, argv, 6);
    // positional n_grid is the default; an explicit --n-grid= flag (parsed
    // above, since it may appear anywhere after argv[6]) still overrides it
    // -- re-parse just that one flag's presence to decide precedence.
    bool has_explicit_n_grid_flag = false;
    for (int i = 6; i < argc; ++i) if (std::string(argv[i]).rfind("--n-grid=", 0) == 0) has_explicit_n_grid_flag = true;
    if (!has_explicit_n_grid_flag) kc.n_grid = n_grid; else n_grid = kc.n_grid;

    RVDataset ds = load_harps_rvbank_csv(csv_path, star);
    if (ds.t.size() == 0) { std::cerr << "no data loaded for " << star << "\n"; return 2; }
    auto known = parse_known(known_spec);
    int m = (int)known.size();
    std::vector<double> known_P(m);
    for (int i = 0; i < m; ++i) known_P[i] = known[i].P;

    double baseline = ds.t(ds.t.size() - 1) - ds.t(0);
    double P_min = 1.2;
    double P_max = std::min(1.0e4, 2.0 * baseline);

    // (KNOMP uses its own seeded RNG, kc.seed, declared in its own block below)

    // ---------------- weights: plain (baselines) vs. jitter-inflated (KNOMP only) -------------------
    // w_plain: the ONLY weight vector LS, GLS, NOMP, LS+KR, and L1/BP ever
    // use (sigma_n from the data, nothing else). KNOMP is the only method
    // with a jitter/GP noise model, per its own Algorithm 1 -- that is a
    // KNOMP-specific algorithmic contribution, not something the baseline
    // methods' own literature includes, so giving it to them would credit
    // them with capability they don't have.
    Eigen::VectorXd w_plain = ds.sigma.array().square().inverse();
    Eigen::VectorXd sigma2_n_base = ds.sigma.array().square();
    double sigma2_jit0 = estimate_jitter(ds.y, sigma2_n_base);
    Eigen::VectorXd w_knomp0 = (sigma2_n_base.array() + sigma2_jit0).inverse();
    auto refresh_w_knomp = [&](const Eigen::VectorXd &r) {
        double s2 = estimate_jitter(r, sigma2_n_base);
        return Eigen::VectorXd((sigma2_n_base.array() + s2).inverse());
    };
    auto wsse = [&](const Eigen::VectorXd &r, const Eigen::VectorXd &wv) { return (wv.array() * r.array().square()).sum(); };

    // ---------------- per-method stopping thresholds, each from that method's OWN literature --------
    // Exact Baluev formulas (see nk_realdata.hpp), not approximations:
    //   LS/GLS/NOMP/L1 (sinusoidal-atom methods): Baluev (2008) Eq.11,
    //     FAP(z) <~ W*exp(-z)*sqrt(z), z = HALF the weighted chi-square
    //     reduction (Baluev's own convention: z=(g_H-g_K)/2).
    //   KNOMP: Baluev (2015) Eq.21/24, the EXACT Keplerian-periodogram FAP
    //     (not the sinusoidal formula -- a full atom has 2 more degrees of
    //     freedom and the paper derives a materially different, larger
    //     threshold for it), conjoined with the BIC decrease per this
    //     paper's own Algorithm 1.
    //   LS+KR: DESIGN.md Sec.3.4's own log(N) threshold form.
    // W = f_max * T_eff, computed separately per method since T_eff
    // depends on that method's own weights (plain vs. jitter-inflated).
    double f_max = 1.0 / P_min;
    double W_plain = baluev_W(f_max, baluev_Teff(ds.t, w_plain));
    const double FAP_LS = 0.01, FAP_GLS = 0.01, FAP_NOMP = 0.01, FAP_L1 = 1e-4;
    double z_thresh_ls   = solve_z_for_fap([&](double z){ return fap_sinusoidal(z, W_plain); }, FAP_LS);
    double z_thresh_gls  = solve_z_for_fap([&](double z){ return fap_sinusoidal(z, W_plain); }, FAP_GLS);
    double z_thresh_nomp = solve_z_for_fap([&](double z){ return fap_sinusoidal(z, W_plain); }, FAP_NOMP);
    double z_thresh_l1   = solve_z_for_fap([&](double z){ return fap_sinusoidal(z, W_plain); }, FAP_L1);
    double z_thresh_lskr = lskr_cfar_threshold((double)ds.t.size(), 0.01);
    const int MAX_EXTRA = 4; // cap on how far the FIVE BASELINE methods may overshoot n_known (KNOMP uses kc.max_extra)

    auto t0 = std::chrono::steady_clock::now();
    std::map<std::string, double> method_seconds;

    // ---------------- Optional dominant-mode pre-whitening for the baseline methods --------------
    // Algorithm (--prewhiten-non-knomp): find the single strongest GLS peak in [P_min, P_max]
    // on the original weighted-mean-subtracted time series, fit (offset, A cos, B sin)
    // at that peak period via weighted least-squares, subtract from y to get the residual,
    // and run LS/GLS/NOMP/LSKR/L1 on this residual. KNOMP always runs on the original ds.y
    // (intentionally -- it has its own GP/jitter-aware whitening and an internal sequential
    // pre-whitening loop, so further external pre-whitening would be redundant at best).
    Eigen::VectorXd y_for_baselines = ds.y;
    json prewhiten_log = json::array();
    if (kc.prewhiten_non_knomp) {
        auto t0p = std::chrono::steady_clock::now();
        PeriodogramPeak pk = periodogram_search(ds.t, ds.y, w_plain, P_min, P_max,
                                                 n_grid, weighted_gls_peak);
        const double om = 2 * PI / pk.period;
        Eigen::VectorXd c = (om * ds.t.array()).cos();
        Eigen::VectorXd s = (om * ds.t.array()).sin();
        Eigen::MatrixXd X(ds.t.size(), 3);
        X.col(0) = c; X.col(1) = s; X.col(2) = Eigen::VectorXd::Ones(ds.t.size());
        Eigen::MatrixXd Xw = w_plain.asDiagonal() * X;
        Eigen::Vector3d co = (X.transpose() * Xw).ldlt().solve(Xw.transpose() * ds.y);
        Eigen::VectorXd mdl = X * co;
        y_for_baselines = ds.y - mdl;
        json entry;
        entry["period"] = pk.period;
        entry["K"] = std::hypot(co(0), co(1));
        entry["phi"] = std::atan2(co(1), co(0));
        entry["offset"] = co(2);
        entry["z"] = 0.5 * (wsse(ds.y, w_plain) - wsse(y_for_baselines, w_plain));
        entry["wall_s"] = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - t0p).count();
        prewhiten_log.push_back(entry);
    }

    // ---------------- LS: sequential pre-whitening, no floating mean, no eccentricity ----------------
    auto t_ls0 = std::chrono::steady_clock::now();
    std::vector<double> ls_P, ls_K;
    if (kc.run_LS) {
    {
        Eigen::VectorXd r = y_for_baselines;
        for (int i = 0; i < m + MAX_EXTRA; ++i) {
            // NOTE: LS uses the plain per-epoch noise model (sigma_n only,
            // no jitter/GP) -- deliberately, since jitter/GP/alias-handling
            // are KNOMP's own algorithmic contributions per the paper's
            // contribution list, not part of the classical LS periodogram
            // this baseline represents. Applying them here would give this
            // baseline capabilities it does not have in its own literature.
            PeriodogramPeak pk = periodogram_search(ds.t, r, w_plain, P_min, P_max, n_grid, weighted_ls_peak,
                                                     ls_P, 0.06);
            // reconstruct model from A,B via weighted_ls_peak's convention (K,phi -> A=K cos phi, B=K sin phi)
            Eigen::VectorXd c = (2 * PI / pk.period * ds.t.array()).cos(), s = (2 * PI / pk.period * ds.t.array()).sin();
            Eigen::VectorXd mdl = pk.K * std::cos(pk.phi) * c.array() + pk.K * std::sin(pk.phi) * s.array();
            Eigen::VectorXd r_after = r - mdl;
            double z = 0.5 * (wsse(r, w_plain) - wsse(r_after, w_plain)); // Baluev convention: z = half the chi-square reduction
            if (z < z_thresh_ls) break;
            ls_P.push_back(pk.period); ls_K.push_back(pk.K);
            r = r_after;
        }
    }
    }
    method_seconds["LS"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_ls0).count();

    // ---------------- GLS: sequential pre-whitening, floating mean per atom, no eccentricity -------
    auto t_gls0 = std::chrono::steady_clock::now();
    std::vector<double> gls_P, gls_K;
    if (kc.run_GLS) {
    {
        Eigen::VectorXd r = y_for_baselines;
        for (int i = 0; i < m + MAX_EXTRA; ++i) {
            // Same plain (no jitter/GP) noise model as LS, for the same reason.
            PeriodogramPeak pk = periodogram_search(ds.t, r, w_plain, P_min, P_max, n_grid, weighted_gls_peak,
                                                     gls_P, 0.06);
            Eigen::MatrixXd X(ds.t.size(), 3);
            X.col(0) = (2 * PI / pk.period * ds.t.array()).cos();
            X.col(1) = (2 * PI / pk.period * ds.t.array()).sin();
            X.col(2) = Eigen::VectorXd::Ones(ds.t.size());
            Eigen::MatrixXd Xw = w_plain.asDiagonal() * X;
            Eigen::Vector3d co = (X.transpose() * Xw).ldlt().solve(Xw.transpose() * r);
            Eigen::VectorXd r_after = r - X * co;
            double z = 0.5 * (wsse(r, w_plain) - wsse(r_after, w_plain)); // Baluev convention: z = half the chi-square reduction
            if (z < z_thresh_gls) break;
            gls_P.push_back(pk.period); gls_K.push_back(pk.K);
            r = r_after;
        }
    }
    }
    method_seconds["GLS"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_gls0).count();

    // ---------------- NOMP: LS-type stopping-aware detection + Gauss-Seidel cyclic joint refit ------
    auto t_nomp0 = std::chrono::steady_clock::now();
    std::vector<double> nomp_P, nomp_K;
    if (kc.run_NOMP) {
    {
        nomp_P = ls_P; nomp_K = ls_K; // start from LS's own (now stopping-aware) sequential detections
        int m_nomp = (int)nomp_P.size();
        // 3 Gauss-Seidel cycles of per-planet re-detection (bracketed near
        // current estimate) against the residual of all OTHER planets,
        // mirroring nk_multiplanet.hpp::nomp_cyclic_joint_fit. Operates on
        // however many candidates NOMP's own (LS-derived) detection stage
        // actually accepted, not a fixed n_known. Plain noise model (no
        // jitter/GP), same reasoning as LS/GLS above.
        for (int cyc = 0; cyc < 3 && m_nomp > 0; ++cyc) {
            for (int j = 0; j < m_nomp; ++j) {
                Eigen::VectorXd r = y_for_baselines;
                for (int k = 0; k < m_nomp; ++k) {
                    if (k == j) continue;
                    Eigen::VectorXd c = (2 * PI / nomp_P[k] * ds.t.array()).cos(), s = (2 * PI / nomp_P[k] * ds.t.array()).sin();
                    Eigen::MatrixXd X(ds.t.size(), 2); X.col(0) = c; X.col(1) = s;
                    Eigen::MatrixXd Xw = w_plain.asDiagonal() * X;
                    Eigen::Vector2d co = (X.transpose() * Xw).ldlt().solve(Xw.transpose() * r);
                    r = r - X * co;
                }
                double lo = nomp_P[j] * 0.9, hi = nomp_P[j] * 1.1;
                lo = std::max(lo, P_min); hi = std::min(hi, P_max);
                PeriodogramPeak pk = periodogram_search(ds.t, r, w_plain, lo, hi, 800, weighted_ls_peak);
                nomp_P[j] = pk.period; nomp_K[j] = pk.K;
            }
        }
    }
    }
    method_seconds["NOMP"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_nomp0).count();

    // ---------------- KNOMP: stopping-aware eccentric detection with full GP covariance -------------
    // KNOMP is the ONLY method in this battery with a correlated-noise (GP)
    // term: per the paper's own Sec.II-C Sigma(phi) = K_act(phi) +
    // diag(sigma_n^2 + sigma_jit^2), re-estimated at every outer iteration
    // (Algorithm 1's JITTER UPDATE + GP HYPERPARAMETER UPDATE steps) from
    // the CURRENT residual, exactly as jitter alone was before -- now
    // extended to the full kernel, not just its diagonal. Detection,
    // refinement, and the CFAR+BIC statistic below all use the resulting
    // Cholesky factor L (Sigma=LL^T) to whiten by triangular solve, since a
    // non-diagonal covariance has no meaningful "weight vector."
    auto t_knomp0 = std::chrono::steady_clock::now();
    std::vector<LsKrPlanet> knomp_pl;
    if (kc.run_KNOMP) {
    {
        std::mt19937_64 rng_knomp(kc.seed);
        GPSearchConfig gcfg = kc.gp_cfg();
        double W_knomp_e = baluev_W(f_max, baluev_Teff(ds.t, w_knomp0)); // recomputed per e_hi below if needed
        Eigen::VectorXd r = ds.y;
        std::vector<double> claimed;       // periods already accepted
        std::vector<double> claimed_alias; // one-year aliases of every already-accepted period
        bool have_prev_hp = false;
        GPHyperparams prev_hp{0, 0, 1};
        for (int i = 0; i < m + kc.max_extra; ++i) {
            GPHyperparams hp = estimate_gp_hyperparams(r, ds.t, sigma2_n_base, gcfg,
                                                        (kc.warm_start && have_prev_hp) ? &prev_hp : nullptr);
            prev_hp = hp; have_prev_hp = true;
            Eigen::MatrixXd Lmat = cholesky_L_from_hp(ds.t, sigma2_n_base, hp);
            double z_thresh_knomp_cfar_i = solve_z_for_fap(
                [&](double z){ return fap_keplerian(z, W_knomp_e, kc.e_hi); }, kc.fap_cfar);

            // Exclude BOTH already-accepted periods AND their one-year
            // aliases from the coarse-grid candidate search (paper's own
            // sidelobe/alias-handling, Sec.II-D, applied prospectively) --
            // unless --no-alias disabled this KNOMP-specific feature.
            std::vector<double> exclude_all = claimed;
            if (kc.alias_enabled) exclude_all.insert(exclude_all.end(), claimed_alias.begin(), claimed_alias.end());
            WKnompFit fit = knomp_gp_detection(ds.t, r, Lmat, P_min, P_max, rng_knomp, kc.n_grid,
                                                kc.n_top, kc.n_multistart_e, exclude_all, kc.exclude_tol);
            fit.e = std::min(fit.e, kc.e_hi);

            // One-year alias check on the surviving candidate itself
            // (paper's own Eq. 11, Algorithm 1 step 3): if the candidate's
            // OWN alias achieves higher (whitened) power, swap to it.
            if (kc.alias_enabled) {
                for (double sign : {+1.0, -1.0}) {
                    double f_alias = 1.0 / fit.P + sign / 365.25;
                    if (f_alias <= 0) continue;
                    double P_alias = 1.0 / f_alias;
                    if (P_alias < P_min || P_alias > P_max) continue;
                    double wsse_candidate = knomp_circular_wsse_gp(fit.P, ds.t, Lmat.triangularView<Eigen::Lower>().solve(r), Lmat);
                    double wsse_alias = knomp_circular_wsse_gp(P_alias, ds.t, Lmat.triangularView<Eigen::Lower>().solve(r), Lmat);
                    if (wsse_alias < wsse_candidate) {
                        double alo = std::max(P_min, P_alias * 0.95), ahi = std::min(P_max, P_alias * 1.05);
                        WKnompFit alias_fit = knomp_gp_detection(ds.t, r, Lmat, alo, ahi, rng_knomp, 500, 3, kc.n_multistart_e);
                        Eigen::VectorXd f_alias_vec = f_signal_vec(ds.t, alias_fit.P, alias_fit.e, alias_fit.omega, alias_fit.M0);
                        Eigen::VectorXd r_alias_after = r - alias_fit.K * f_alias_vec;
                        Eigen::VectorXd f_orig_vec = f_signal_vec(ds.t, fit.P, fit.e, fit.omega, fit.M0);
                        Eigen::VectorXd r_orig_after = r - fit.K * f_orig_vec;
                        double wa = Lmat.triangularView<Eigen::Lower>().solve(r_alias_after).squaredNorm();
                        double wo = Lmat.triangularView<Eigen::Lower>().solve(r_orig_after).squaredNorm();
                        if (wa < wo) fit = alias_fit;
                    }
                }
            }
            Eigen::VectorXd f = f_signal_vec(ds.t, fit.P, fit.e, fit.omega, fit.M0);
            Eigen::VectorXd r_after = r - fit.K * f;
            double sse_before = Lmat.triangularView<Eigen::Lower>().solve(r).squaredNorm();
            double sse_after = Lmat.triangularView<Eigen::Lower>().solve(r_after).squaredNorm();
            double z = 0.5 * (sse_before - sse_after); // Baluev convention: z = half the chi-square reduction
            // KNOMP's own conjunctive rule (Algorithm 1 / Sec.II-H): CFAR
            // (Baluev-Keplerian) AND BIC decrease (--no-bic drops the
            // latter, leaving pure CFAR).
            if (!knomp_conjunctive_accept(z, z_thresh_knomp_cfar_i, (int)ds.t.size(), kc.delta_k, kc.bic_enabled)) break;
            claimed.push_back(fit.P);
            if (kc.alias_enabled)
                for (double sign : {+1.0, -1.0}) {
                    double f_alias = 1.0 / fit.P + sign / 365.25;
                    if (f_alias > 0) claimed_alias.push_back(1.0 / f_alias);
                }
            knomp_pl.push_back({fit.P, fit.e, fit.omega, fit.M0, fit.K});
            r = r_after;
        }
        int m_knomp = (int)knomp_pl.size();
        // "Best-case KNOMP" configuration, per handoff/01_python_reproduction/README.md's
        // tune_knomp_multiplanet.py search: exactly ONE Gauss-Seidel sweep (n_cycles=1,
        // R_c=1), NO group-cyclic step, NO final joint polish (2+ cycles or any final
        // joint polish were found to make KNOMP's multi-planet fit WORSE). The GP
        // covariance is re-estimated once more from the final combined residual
        // (warm-started from the last outer iteration's hyperparameters) and held
        // fixed through this refinement pass.
        if (m_knomp > 0) {
            Eigen::VectorXd r_all = ds.y;
            { Eigen::MatrixXd F = lskr_design(ds.t, knomp_pl); Eigen::VectorXd K = lskr_gains(F, ds.y, w_plain); r_all = ds.y - F * K; }
            GPHyperparams hp_final = estimate_gp_hyperparams(r_all, ds.t, sigma2_n_base, gcfg,
                                                              (kc.warm_start && have_prev_hp) ? &prev_hp : nullptr);
            Eigen::MatrixXd L_final = cholesky_L_from_hp(ds.t, sigma2_n_base, hp_final);
            for (int j = 0; j < m_knomp; ++j) {
                std::vector<LsKrPlanet> other;
                for (int k = 0; k < m_knomp; ++k) if (k != j) other.push_back(knomp_pl[k]);
                Eigen::VectorXd target = ds.y;
                if (!other.empty()) {
                    Eigen::MatrixXd F = lskr_design(ds.t, other);
                    Eigen::VectorXd K = lskr_gains(F, ds.y, w_plain);
                    target = ds.y - F * K;
                }
                double plo = knomp_pl[j].P * (1.0 - kc.bracket_frac_final), phi = knomp_pl[j].P * (1.0 + kc.bracket_frac_final);
                WKnompFit refit = knomp_gp_detection(ds.t, target, L_final, plo, phi, rng_knomp, 500, 3,
                                                      std::max(6, kc.n_multistart_e));
                knomp_pl[j] = {refit.P, refit.e, refit.omega, refit.M0, refit.K};
            }
        }
    }
    }
    method_seconds["KNOMP"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_knomp0).count();

    // ---------------- LS+KR: DESIGN.md loop (GLS detect + immediate joint refit), stopping-aware ----
    auto t_lskr0 = std::chrono::steady_clock::now();
    LsKrResult lskr;
    if (kc.run_LSKR) {
        lskr = lskr_run(ds.t, y_for_baselines, w_plain, P_min, P_max, m + MAX_EXTRA, n_grid, z_thresh_lskr);
    }
    method_seconds["LSKR"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_lskr0).count();

    // ---------------- L1/BP: stopping-aware weighted l1-periodogram (Hara et al. 2016) + refine -----
    auto t_l10 = std::chrono::steady_clock::now();
    std::vector<double> l1_P, l1_K;
    if (kc.run_L1) {
    {
        Eigen::VectorXd r = y_for_baselines;
        std::vector<double> claimed;
        // The l1-periodogram's own dictionary grows as O(n_grid) columns and each
        // FISTA solve is O(iterations * m * n_grid); at n_grid=5000 this is
        // materially more expensive per candidate than the other methods' cheap
        // per-point periodogram evaluations, so a somewhat coarser (but still
        // log-spaced, still exclusion-zone-aware) grid is used specifically for
        // this method's own sparse-recovery step -- the final period is then
        // polished by the same fine-grid (n_grid) local Brent refine every other
        // method uses, so the REPORTED period accuracy is not limited by this
        // dictionary's resolution, only the initial candidate selection is.
        int l1_grid = std::min(n_grid, 1500);
        for (int i = 0; i < m + MAX_EXTRA; ++i) {
            // Plain (no jitter/GP) noise model, same reasoning as LS/GLS/NOMP:
            // this is a port of Hara et al. (2016)'s own method, which does
            // not include KNOMP's jitter/GP/alias machinery.
            L1PeriodogramResult pk = l1_periodogram_peak(ds.t, r, w_plain, P_min, P_max, l1_grid,
                                                          claimed, 0.06);
            double lo = std::max(P_min, pk.period * 0.97), hi = std::min(P_max, pk.period * 1.03);
            PeriodogramPeak refined = periodogram_search(ds.t, r, w_plain, lo, hi, 800, weighted_gls_peak);
            Eigen::MatrixXd X(ds.t.size(), 3);
            X.col(0) = (2 * PI / refined.period * ds.t.array()).cos();
            X.col(1) = (2 * PI / refined.period * ds.t.array()).sin();
            X.col(2) = Eigen::VectorXd::Ones(ds.t.size());
            Eigen::MatrixXd Xw = w_plain.asDiagonal() * X;
            Eigen::Vector3d co = (X.transpose() * Xw).ldlt().solve(Xw.transpose() * r);
            Eigen::VectorXd r_after = r - X * co;
            double z = 0.5 * (wsse(r, w_plain) - wsse(r_after, w_plain)); // Baluev convention: z = half the chi-square reduction
            if (z < z_thresh_l1) break;
            claimed.push_back(pk.period);
            l1_P.push_back(refined.period); l1_K.push_back(refined.K);
            r = r_after;
        }
    }
    }
    method_seconds["L1"] = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_l10).count();


    auto t1 = std::chrono::steady_clock::now();
    double wall_s = std::chrono::duration<double>(t1 - t0).count();

    // ---------------- match each method's detections to known planets -------------------------------
    auto build_matched = [&](const std::vector<double> &det_P) {
        json arr = json::array();
        std::vector<int> assign = match_periods(det_P, known_P);
        for (int j = 0; j < m; ++j) {
            json row;
            row["known_P"] = known_P[j]; row["known_e"] = known[j].e;
            if (assign[j] >= 0) {
                row["det_P"] = det_P[assign[j]];
                row["delta_P"] = det_P[assign[j]] - known_P[j];
                row["delta_P_rel"] = (det_P[assign[j]] - known_P[j]) / known_P[j];
            } else { row["det_P"] = nullptr; row["delta_P"] = nullptr; row["delta_P_rel"] = nullptr; }
            arr.push_back(row);
        }
        return arr;
    };

    json out;
    out["star"] = star; out["n_obs"] = (int)ds.t.size(); out["baseline_days"] = baseline;
    out["n_known_planets"] = m; out["wall_seconds"] = wall_s;
    out["z_thresholds"] = {
        {"LS", z_thresh_ls}, {"GLS", z_thresh_gls}, {"NOMP", z_thresh_nomp},
        {"LSKR", z_thresh_lskr}, {"L1", z_thresh_l1}
    };
    out["method_seconds"] = method_seconds;
    out["W_plain"] = W_plain; out["sigma2_jit_initial"] = sigma2_jit0;
    out["knomp_config"] = {
        {"n_top", kc.n_top}, {"n_multistart_e", kc.n_multistart_e}, {"exclude_tol", kc.exclude_tol},
        {"bracket_frac_final", kc.bracket_frac_final}, {"e_hi", kc.e_hi}, {"max_extra", kc.max_extra},
        {"fap_cfar", kc.fap_cfar}, {"delta_k", kc.delta_k}, {"bic_enabled", kc.bic_enabled},
        {"jitter_enabled", kc.jitter_enabled}, {"gp_enabled", kc.gp_enabled}, {"warm_start", kc.warm_start},
        {"alias_enabled", kc.alias_enabled}, {"gp_tau_grid", kc.gp_tau_grid}, {"gp_rounds", kc.gp_rounds},
        {"gp_golden_iters", kc.gp_golden_iters}, {"gp_max_n", kc.gp_max_n}, {"seed", kc.seed}, {"n_grid", kc.n_grid}
    };
    out["prewhiten_non_knomp"] = prewhiten_log;     // array (always present); empty if --prewhiten-non-knomp not set
    out["n_detected"] = {
        {"LS", (int)ls_P.size()}, {"GLS", (int)gls_P.size()}, {"NOMP", (int)nomp_P.size()},
        {"KNOMP", (int)knomp_pl.size()}, {"LSKR", (int)lskr.planets.size()}, {"L1", (int)l1_P.size()}
    };
    out["LS"] = build_matched(ls_P);
    out["GLS"] = build_matched(gls_P);
    out["NOMP"] = build_matched(nomp_P);
    {
        std::vector<double> kp; for (auto &p : knomp_pl) kp.push_back(p.P);
        json arr = build_matched(kp);
        std::vector<int> assign = match_periods(kp, known_P);
        for (int j = 0; j < m; ++j)
            if (assign[j] >= 0) {
                arr[j]["det_e"] = knomp_pl[assign[j]].e;
                arr[j]["delta_e"] = knomp_pl[assign[j]].e - known[j].e;
            } else { arr[j]["det_e"] = nullptr; arr[j]["delta_e"] = nullptr; }
        out["KNOMP"] = arr;
    }
    {
        std::vector<double> kp; for (auto &p : lskr.planets) kp.push_back(p.P);
        json arr = build_matched(kp);
        std::vector<int> assign = match_periods(kp, known_P);
        for (int j = 0; j < m; ++j)
            if (assign[j] >= 0) {
                arr[j]["det_e"] = lskr.planets[assign[j]].e;
                arr[j]["delta_e"] = lskr.planets[assign[j]].e - known[j].e;
            } else { arr[j]["det_e"] = nullptr; arr[j]["delta_e"] = nullptr; }
        out["LSKR"] = arr;
    }
    out["L1"] = build_matched(l1_P);

    // Raw (pre-matching) detected periods per method, for the real-vs-
    // spurious detection metric: whether EACH raw detection lies near ANY
    // known planet, independent of the one-to-one optimal assignment used
    // for the Delta-P table above (a method that re-detects the same real
    // signal twice, or finds pure noise, shows up here even when the
    // matching above "hides" it behind a forced 1:1 pairing).
    out["LS_raw_P"] = ls_P;
    out["GLS_raw_P"] = gls_P;
    out["NOMP_raw_P"] = nomp_P;
    { std::vector<double> kp; for (auto &p : knomp_pl) kp.push_back(p.P); out["KNOMP_raw_P"] = kp; }
    { std::vector<double> kp; for (auto &p : lskr.planets) kp.push_back(p.P); out["LSKR_raw_P"] = kp; }
    out["L1_raw_P"] = l1_P;
    out["known_P_list"] = known_P;

    std::ofstream fout(out_path);
    fout << out.dump(2);
    std::cerr << "wrote " << out_path << " (" << wall_s << " s)\n";
    return 0;
}
