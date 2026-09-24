// nk_realdata.hpp
//
// Real-data extensions for the KNOMP/NOMP C++ core (nk_kepler.hpp,
// nk_optimize.hpp): weighted classical Lomb-Scargle (LS), weighted
// Generalized Lomb-Scargle (GLS, Zechmeister & Kuerster 2009 floating-mean
// form), CSV I/O for HARPS RVBank per-star files, and a simple multi-planet
// wrapper shared by the NOMP/KNOMP/LS/GLS/LS+KR real-data drivers.
//
// NOTE ON SCOPE: this header supports *validation against known catalog
// planets* (fixed number of planets = number of confirmed planets in the
// system, matched to nearest known period after the fact), not blind
// model-order selection. The full CFAR+BIC stopping rule of the paper's
// Algorithm 1 requires jitter/GP hyperparameter estimation that is out of
// scope for this pass; where a stopping decision is needed the code says so
// explicitly in comments and in the results JSON ("stopping_rule" field).
#pragma once
#include <Eigen/Dense>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <cmath>
#include <algorithm>
#include <random>
#include "nk_kepler.hpp"
#include "nk_optimize.hpp"

namespace nk {

// ------------------------------------------------------- noise model: jitter ---

// Profile log-likelihood for a single global jitter term s=sigma_jit^2,
// given current residuals r and nominal per-epoch variances sigma_n^2
// (Algorithm 1's own JITTER UPDATE step; matches the exact closed form
// used in this project's Lean formalization, JitterLikelihoodMaximizer.lean:
// ell(s) = -1/2 sum log(sigma_n^2+s) - 1/2 sum r_n^2/(sigma_n^2+s)).
// A single global term (not per-instrument) is used here since the
// per-star loader does not currently segment epochs by instrument/PROGID;
// this is a documented simplification of the full per-dataset jitter
// Algorithm 1 describes, not the complete treatment.
inline double jitter_profile_loglik(double s, const Eigen::VectorXd &r, const Eigen::VectorXd &sigma2_n) {
    double ll = 0.0;
    for (int i = 0; i < r.size(); ++i) {
        double v = sigma2_n(i) + s;
        ll += -0.5 * std::log(v) - 0.5 * (r(i) * r(i)) / v;
    }
    return ll;
}

// Coarse log-spaced grid search + golden-section polish for the profiled
// jitter MLE (the profile is not globally concave -- JitterLikelihoodMaximizer.lean
// proves exactly this -- so a grid bracket before local polish is used
// rather than a plain gradient method, matching Algorithm 1's own
// "coarse log-spaced grid... then polish" description).
inline double estimate_jitter(const Eigen::VectorXd &r, const Eigen::VectorXd &sigma2_n,
                               double max_mult = 1e3, int n_grid = 60) {
    double max_sigma2 = sigma2_n.maxCoeff();
    double lo = std::log(1e-6), hi = std::log(max_sigma2 * max_mult + 1e-6);
    double best_s = 0.0, best_ll = jitter_profile_loglik(0.0, r, sigma2_n);
    for (int i = 0; i < n_grid; ++i) {
        double s = std::exp(lo + (hi - lo) * i / (n_grid - 1));
        double ll = jitter_profile_loglik(s, r, sigma2_n);
        if (ll > best_ll) { best_ll = ll; best_s = s; }
    }
    // golden-section polish around the grid optimum
    double a = std::max(0.0, best_s * 0.3), b = best_s * 3.0 + 1e-6;
    const double gr = 0.6180339887;
    double c = b - gr * (b - a), d = a + gr * (b - a);
    for (int it = 0; it < 40; ++it) {
        if (jitter_profile_loglik(c, r, sigma2_n) < jitter_profile_loglik(d, r, sigma2_n)) a = c; else b = d;
        c = b - gr * (b - a); d = a + gr * (b - a);
    }
    double s_final = 0.5 * (a + b);
    return jitter_profile_loglik(s_final, r, sigma2_n) > best_ll ? s_final : best_s;
}

// ------------------------------------------- noise model: correlated (GP) ---
//
// KNOMP-only (per the paper's own Sec.II-C/Algorithm 1 "GP HYPERPARAMETER
// UPDATE" step): a correlated-noise kernel K_act(phi) added to the diagonal
// jitter+measurement-noise covariance, per Sec.II-C's Sigma(phi) = K_act(phi)
// + diag(sigma_n^2 + sigma_jit^2). Kernel form follows Hara et al. (2016)
// Eq.14 (already used and cited in this project): a simple exponential
// (Ornstein-Uhlenbeck) covariance R(t) = sigma_R^2 * exp(-|t|/tau), the
// standard, literature-grounded choice for stellar-activity correlated
// noise when a full quasi-periodic/multi-indicator GP (Rajpaul et al. 2015)
// is not being fit jointly with activity indicators (this project's per-
// star loader does not currently ingest FWHM/bisector/logR'HK, so the
// simpler single-kernel form is the correct, literature-consistent choice
// given that scope -- not an arbitrary simplification of a "true" answer,
// but the appropriate model given the available data).
struct GPHyperparams { double sigma2_jit, sigma_R2, tau; };

// Every lever of the GP/jitter search, CLI-configurable (see realdata_main.cpp's
// argument parsing). Defaults match what was previously hard-coded.
struct GPSearchConfig {
    bool gp_enabled = true;      // --no-gp forces sigma_R2=0 (jitter-only fallback)
    bool jitter_enabled = true;  // --no-jitter forces sigma2_jit=0 too (raw sigma_n only)
    int n_tau_grid = 4;          // --gp-tau-grid
    int rounds = 2;              // --gp-rounds (coordinate-descent rounds per tau)
    int golden_iters = 12;       // --gp-golden-iters
    double tau_min_days = 1.0;   // --gp-tau-min
    double tau_max_frac = 3.0;   // --gp-tau-max-frac (tau_max = baseline/this)
    int gp_max_n = 1500;         // --gp-max-n (O(N^3) safety cap; see below)
};

// UNSCALED correlation shape only (no sigma_R2 factor, no diagonal terms):
// C_ij(tau) = exp(-|t_i-t_j|/tau). Caching this once per tau and reusing it
// across every (sigma2_jit, sigma_R2) trial at that tau saves an O(N^2)
// pass of exp() evaluations per trial -- previously exponential_kernel()
// recomputed this from scratch on every single profile-likelihood call
// (100+ times per outer KNOMP iteration), which was pure wasted work since
// only the O(N^2) scale-and-add-diagonal step actually depends on
// (sigma2_jit, sigma_R2).
inline Eigen::MatrixXd exponential_correlation(const Eigen::VectorXd &t, double tau) {
    int n = t.size();
    Eigen::MatrixXd C(n, n);
    for (int i = 0; i < n; ++i)
        for (int j = 0; j <= i; ++j) {
            double v = std::exp(-std::fabs(t(i) - t(j)) / tau);
            C(i, j) = v; C(j, i) = v; // exploit symmetry: half the exp() calls
        }
    return C;
}

inline Eigen::MatrixXd build_covariance_from_corr(const Eigen::MatrixXd &C, const Eigen::VectorXd &sigma2_n,
                                                   double sigma2_jit, double sigma_R2) {
    Eigen::MatrixXd Sigma = sigma_R2 * C;
    for (int i = 0; i < sigma2_n.size(); ++i) Sigma(i, i) += sigma2_n(i) + sigma2_jit;
    return Sigma;
}

// Kept for external callers (e.g. the tuning harness) that want a
// covariance matrix directly without managing a cached correlation matrix
// themselves; internally just wraps the cached-correlation path once.
inline Eigen::MatrixXd build_covariance(const Eigen::VectorXd &t, const Eigen::VectorXd &sigma2_n,
                                         const GPHyperparams &hp) {
    return build_covariance_from_corr(exponential_correlation(t, hp.tau), sigma2_n, hp.sigma2_jit, hp.sigma_R2);
}

// Full Gaussian marginal log-likelihood given an ALREADY-BUILT covariance
// (caller supplies Sigma, e.g. from build_covariance_from_corr using a
// cached C): -1/2[log det Sigma + r^T Sigma^-1 r], via Cholesky (never
// forms Sigma^-1 explicitly).
inline double gp_profile_loglik_cov(const Eigen::VectorXd &r, const Eigen::MatrixXd &Sigma) {
    Eigen::LLT<Eigen::MatrixXd> llt(Sigma);
    if (llt.info() != Eigen::Success) return -1e300;
    const Eigen::MatrixXd &L = llt.matrixLLT(); // lower triangle of the factor lives here, no extra copy
    double logdet = 0; for (int i = 0; i < L.rows(); ++i) logdet += 2.0 * std::log(L(i, i));
    Eigen::VectorXd z = L.triangularView<Eigen::Lower>().solve(r);
    return -0.5 * (logdet + z.squaredNorm());
}
inline double gp_profile_loglik(const Eigen::VectorXd &r, const Eigen::VectorXd &t,
                                 const Eigen::VectorXd &sigma2_n, const GPHyperparams &hp) {
    return gp_profile_loglik_cov(r, build_covariance(t, sigma2_n, hp));
}

// GP is an O(N^3)-per-evaluation, so the search below is deliberately
// structured to minimize the NUMBER of distinct (sigma2_jit, sigma_R2, tau)
// triples evaluated, and to reuse the O(N^2) correlation matrix across
// every trial that shares a tau. For the handful of extreme-N real-data
// targets in this project's battery (e.g. tau Ceti/HD10700 at N=11632),
// even an optimized search is infeasible outright; cfg.gp_max_n draws an
// explicit, documented, CLI-overridable line above which KNOMP falls back
// to jitter-only rather than silently hanging.
//
// prev_hp: an optional warm-start from the PREVIOUS outer KNOMP iteration's
// result (nullptr if none -- e.g. the very first iteration). Since the
// residual only changes by one subtracted signal between consecutive outer
// iterations, the previous optimum is very often still close to optimal;
// it is evaluated as one additional candidate (at zero extra risk of
// correctness -- the fresh grid search still runs in full and the global
// best across BOTH is kept) and very often lets later outer iterations
// converge without needing their full grid at all when it wins outright.
inline GPHyperparams estimate_gp_hyperparams(const Eigen::VectorXd &r, const Eigen::VectorXd &t,
                                              const Eigen::VectorXd &sigma2_n,
                                              const GPSearchConfig &cfg = GPSearchConfig{},
                                              const GPHyperparams *prev_hp = nullptr) {
    if (!cfg.jitter_enabled) return {0.0, 0.0, 1.0};
    if (!cfg.gp_enabled || r.size() > cfg.gp_max_n) {
        double s_jit_only = estimate_jitter(r, sigma2_n);
        return {s_jit_only, 0.0, 1.0};
    }
    double max_sigma2 = sigma2_n.maxCoeff();
    double baseline = t.maxCoeff() - t.minCoeff();
    int n_tau_grid = std::max(1, cfg.n_tau_grid);
    std::vector<double> tau_grid(n_tau_grid);
    double tlo = std::log(cfg.tau_min_days), thi = std::log(std::max(cfg.tau_min_days * 2, baseline / cfg.tau_max_frac));
    for (int i = 0; i < n_tau_grid; ++i)
        tau_grid[i] = n_tau_grid == 1 ? cfg.tau_min_days : std::exp(tlo + (thi - tlo) * i / (n_tau_grid - 1));

    GPHyperparams best{0.0, 0.0, tau_grid[0]};
    double best_ll = -1e300;
    // NOTE ON WARM-STARTING: two attempts at warm-starting this search from
    // the previous outer KNOMP iteration's optimum were tried and both
    // rejected. (1) Skipping the full grid in favor of a narrow local
    // search around the previous optimum was FASTER but changed the
    // answer (on HD 69830, silently dropped KNOMP from 5 detections to 1 --
    // a narrowed tau bracket let the GP absorb a real signal into "noise"
    // on one iteration, which then compounded on every later iteration).
    // (2) Running the local search as an ADDITIONAL candidate alongside the
    // still-full grid was correctness-safe but pure overhead (slower than
    // no warm-start at all, since it never actually replaced any work).
    // Neither is used; (prev_hp) is accepted as a parameter for API
    // stability and potential future use but currently has no effect. The
    // real, verified-safe speedup in this function is the per-tau
    // correlation-matrix caching below, which cut this function's cost by
    // eliminating a full O(N^2) exp()-evaluation pass on every one of the
    // ~100 (jitter, sigma_R2) trials -- previously repeated from scratch
    // every time even though only the O(N^2) scale-and-add-diagonal step
    // actually depends on those two parameters, not the O(N^2) kernel shape.
    (void)prev_hp;

    for (double tau : tau_grid) {
        // Cache the O(N^2) correlation matrix ONCE for this tau; every
        // (sigma2_jit, sigma_R2) trial below reuses it, paying only the
        // O(N^2) scale-and-add-diagonal plus the (unavoidable) O(N^3)
        // Cholesky -- not a second O(N^2) pass of exp() calls.
        Eigen::MatrixXd C = exponential_correlation(t, tau);
        auto negll = [&](double s_jit, double s_R2) {
            return -gp_profile_loglik_cov(r, build_covariance_from_corr(C, sigma2_n, s_jit, s_R2));
        };
        auto golden_1d = [&](std::function<double(double)> f, double a, double b, int iters) {
            const double gr = 0.6180339887;
            double c = b - gr * (b - a), d = a + gr * (b - a);
            for (int it = 0; it < iters; ++it) {
                if (f(c) < f(d)) a = c; else b = d;
                c = b - gr * (b - a); d = a + gr * (b - a);
            }
            return 0.5 * (a + b);
        };
        double s_jit = 0.0, s_R2 = max_sigma2;
        for (int round = 0; round < cfg.rounds; ++round) {
            s_jit = golden_1d([&](double s){ return negll(s, s_R2); }, 0.0, max_sigma2 * 1e3 + 1e-6, cfg.golden_iters);
            s_R2  = golden_1d([&](double sr){ return negll(s_jit, sr); }, 0.0, max_sigma2 * 1e3 + 1e-6, cfg.golden_iters);
        }
        double ll = -negll(s_jit, s_R2);
        if (ll > best_ll) { best_ll = ll; best = {s_jit, s_R2, tau}; }
    }
    // also check the pure-jitter (sigma_R2=0) case explicitly, in case
    // correlated noise genuinely isn't present in the current residual
    {
        double s_jit_only = estimate_jitter(r, sigma2_n);
        double ll0 = gp_profile_loglik(r, t, sigma2_n, {s_jit_only, 0.0, tau_grid[0]});
        if (ll0 > best_ll) { best_ll = ll0; best = {s_jit_only, 0.0, tau_grid[0]}; }
    }
    return best;
}


struct RVDataset {
    std::string star;
    Eigen::VectorXd t;      // BJD, days, relative to t0
    Eigen::VectorXd y;      // RV, m/s, weighted-mean-subtracted per instrument if multi-instrument
    Eigen::VectorXd sigma;  // per-epoch nominal RV uncertainty, m/s
    double t0 = 0.0;        // reference BJD subtracted from raw BJD column
};

// Split a CSV line respecting the simple (no embedded commas/quotes) HARPS
// RVBank format used here.
inline std::vector<std::string> split_csv_line(const std::string &line) {
    std::vector<std::string> out;
    std::stringstream ss(line);
    std::string cell;
    while (std::getline(ss, cell, ',')) out.push_back(cell);
    return out;
}

// Load one HARPS RVBank per-star CSV (as distributed in per_star_data_filtered.zip).
// Uses RV_mlc_nzp / e_RV_mlc_nzp (night-zero-point-corrected, multi-line-component
// RVs) when present and finite; falls back to RV_mlc / e_RV_mlc otherwise.
// Per-instrument (PROGID) offsets are NOT fit here (the nzp correction already
// removes the dominant fiber/pipeline-change jumps); this is a documented
// simplification (see notes/REALDATA_SIMPLIFICATIONS.md).
inline RVDataset load_harps_rvbank_csv(const std::string &path, const std::string &star_name) {
    std::ifstream f(path);
    RVDataset out;
    out.star = star_name;
    if (!f) return out;

    std::string header_line;
    std::getline(f, header_line);
    // strip trailing \r
    if (!header_line.empty() && header_line.back() == '\r') header_line.pop_back();
    std::vector<std::string> cols = split_csv_line(header_line);
    auto idx_of = [&](const std::string &name) -> int {
        for (size_t i = 0; i < cols.size(); ++i) if (cols[i] == name) return (int)i;
        return -1;
    };
    int i_bjd = idx_of("BJD");
    int i_rv_nzp = idx_of("RV_mlc_nzp"), i_erv_nzp = idx_of("e_RV_mlc_nzp");
    int i_rv = idx_of("RV_mlc"), i_erv = idx_of("e_RV_mlc");

    std::vector<double> tv, yv, sv;
    std::string line;
    while (std::getline(f, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.empty()) continue;
        std::vector<std::string> f_ = split_csv_line(line);
        if ((int)f_.size() <= i_bjd) continue;
        auto safe_d = [&](int i) -> double {
            if (i < 0 || i >= (int)f_.size() || f_[i].empty()) return std::nan("");
            try { return std::stod(f_[i]); } catch (...) { return std::nan(""); }
        };
        double bjd = safe_d(i_bjd);
        double rv = safe_d(i_rv_nzp), erv = safe_d(i_erv_nzp);
        if (!std::isfinite(rv) || rv < -1e6 || rv > 1e6) { rv = safe_d(i_rv); erv = safe_d(i_erv); }
        if (!std::isfinite(bjd) || !std::isfinite(rv) || !std::isfinite(erv)) continue;
        if (erv <= 0) continue;
        tv.push_back(bjd); yv.push_back(rv); sv.push_back(erv);
    }
    int n = (int)tv.size();
    if (n == 0) return out;
    out.t.resize(n); out.y.resize(n); out.sigma.resize(n);
    for (int i = 0; i < n; ++i) { out.t(i) = tv[i]; out.y(i) = yv[i]; out.sigma(i) = sv[i]; }

    // sort by time
    std::vector<int> order(n);
    for (int i = 0; i < n; ++i) order[i] = i;
    std::sort(order.begin(), order.end(), [&](int a, int b) { return out.t(a) < out.t(b); });
    Eigen::VectorXd t2(n), y2(n), s2(n);
    for (int i = 0; i < n; ++i) { t2(i) = out.t(order[i]); y2(i) = out.y(order[i]); s2(i) = out.sigma(order[i]); }
    out.t0 = t2(0);
    out.t = t2.array() - out.t0;
    // weighted-mean subtraction (removes the arbitrary RV zero point, does
    // NOT remove per-instrument offsets -- see simplification note above)
    Eigen::VectorXd w = s2.array().square().inverse();
    double wmean = (w.array() * y2.array()).sum() / w.sum();
    out.y = y2.array() - wmean;
    out.sigma = s2;
    return out;
}

// ------------------------------------------------------- periodogram(s) ---

struct PeriodogramPeak {
    double period, power, K, phi;   // phi: cosine-phase, y_model = K cos(w t - phi)
};

// Weighted classical Lomb-Scargle (Scargle 1982 normalization is not used;
// we report the *power reduction* form, i.e. the same quantity as NOMP's
// projection statistic, so that LS/GLS/NOMP/KNOMP detection statistics are
// directly comparable on the same y-axis). No floating mean: the caller is
// expected to have removed a global (weighted) mean already, matching the
// classical LS assumption of a zero-mean signal.
//
// HOT PATH: rewritten to use thread-local scratch buffers + raw pointer
// access + a single fused accumulation loop. This eliminates ~8K heap
// allocations per periodogram_search call (4000 grid points x 2 vectors),
// which were the dominant cost in the Eigen-based version. The math is
// identical: same 5 weighted sums, same 2x2 solve, same K/phi/power.
inline PeriodogramPeak weighted_ls_peak(const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                         const Eigen::VectorXd &w, double P) {
    struct Scratch { std::vector<double> c, s; };
    auto& sc = *[]() -> Scratch* {
        thread_local Scratch s;
        return &s;
    }();
    const int n = (int)t.size();
    if ((int)sc.c.size() < n) { sc.c.resize(n); sc.s.resize(n); }
    const double* __restrict__ tp = t.data();
    const double* __restrict__ yp = y.data();
    const double* __restrict__ wp = w.data();
    const double om = 2 * PI / P;
    double Cc = 0, Ss = 0, Cs = 0, Cy = 0, Sy = 0;
    int i = 0;
    // Main fused loop: compute sin/cos once, accumulate weighted sums in
    // the same pass. The compiler (-O3 -march=native) auto-vectorises this
    // for AVX2/AVX512 when alignment allows (Eigen VectorXd is 32-byte
    // aligned on x86_64).
    for (; i < n; ++i) {
        const double ph = om * tp[i];
        const double c = std::cos(ph);
        const double s = std::sin(ph);
        sc.c[i] = c; sc.s[i] = s;
        const double wc = wp[i] * c;
        const double ws = wp[i] * s;
        Cc += wc * c;
        Ss += ws * s;
        Cs += wc * s;
        Cy += wc * yp[i];
        Sy += ws * yp[i];
    }
    const double det = Cc * Ss - Cs * Cs;
    double A = 0, B = 0;
    if (std::fabs(det) > 1e-300) { A = (Cy * Ss - Sy * Cs) / det; B = (Cc * Sy - Cs * Cy) / det; }
    const double power = A * Cy + B * Sy;
    PeriodogramPeak out;
    out.period = P; out.power = power; out.K = std::hypot(A, B); out.phi = std::atan2(B, A);
    return out;
}

// Weighted Generalized Lomb-Scargle (floating mean): design [cos, sin, 1].
// Same hot-path rewrite: thread-local scratch, raw pointers, fused loop.
// 3x3 normal equations are solved in closed form per grid point (no ldlt).
inline PeriodogramPeak weighted_gls_peak(const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                          const Eigen::VectorXd &w, double P) {
    struct Scratch { std::vector<double> c, s; };
    auto& sc = *[]() -> Scratch* {
        thread_local Scratch s;
        return &s;
    }();
    const int n = (int)t.size();
    if ((int)sc.c.size() < n) { sc.c.resize(n); sc.s.resize(n); }
    const double* __restrict__ tp = t.data();
    const double* __restrict__ yp = y.data();
    const double* __restrict__ wp = w.data();
    const double om = 2 * PI / P;
    double Cc = 0, Ss = 0, Cs = 0, Cy = 0, Sy = 0;
    double Co = 0, So = 0;       // sum w[i] * c[i], sum w[i] * s[i]
    double sse0 = 0;
    for (int i = 0; i < n; ++i) {
        const double ph = om * tp[i];
        const double c = std::cos(ph);
        const double s = std::sin(ph);
        sc.c[i] = c; sc.s[i] = s;
        const double wc = wp[i] * c;
        const double ws = wp[i] * s;
        Cc += wc * c;
        Ss += ws * s;
        Cs += wc * s;
        Cy += wc * yp[i];
        Sy += ws * yp[i];
        Co += wc;
        So += ws;
        sse0 += wp[i] * yp[i] * yp[i];
    }
    // Normal equations: [[Cc,Cs,Co],[Cs,Ss,So],[Co,So,Wo]] * [A,B,C]^T = [Cy,Sy,Yo]
    const double Wo = w.sum();
    const double Yo = (w.array() * y.array()).sum();
    // closed-form 3x3 inverse (numerator/denominator expansion):
    const double det = Cc * (Ss * Wo - So * So)
                     - Cs * (Cs * Wo - So * Co)
                     + Co * (Cs * So - Ss * Co);
    double A = 0, B = 0, C = 0, sse1 = sse0;
    if (std::fabs(det) > 1e-300) {
        const double inv = 1.0 / det;
        // adjugate columns (for each output index, dot with rhs vector)
        const double m00 = (Ss * Wo - So * So) * inv;
        const double m01 = -(Cs * Wo - So * Co) * inv;
        const double m02 = (Cs * So - Ss * Co) * inv;
        const double m11 = (Cc * Wo - Co * Co) * inv;
        const double m12 = -(Cc * So - Cs * Co) * inv;
        const double m22 = (Cc * Ss - Cs * Cs) * inv;
        A = m00 * Cy + m01 * Sy + m02 * Yo;
        B = m01 * Cy + m11 * Sy + m12 * Yo;
        C = m02 * Cy + m12 * Sy + m22 * Yo;
        sse1 = sse0 - (A * Cy + B * Sy + C * Yo);
        if (sse1 < 0) sse1 = 0;
    }
    PeriodogramPeak out;
    out.period = P; out.power = sse0 - sse1;
    out.K = std::hypot(A, B); out.phi = std::atan2(B, A);
    return out;
}

// Exclusion-zone helper: is trial period P within relative tolerance `tol`
// (log-period distance) of any period already claimed by an earlier
// detection in this run? Mirrors the paper's own Algorithm-1 exclusion-zone
// mechanism (Sec.II-D / Theorem III.6), applied here to keep a greedy
// sequential real-data search from re-detecting the same imperfectly
// subtracted signal (or its harmonics/aliases) at every iteration.
// Fundamental-only exclusion. NOTE: an earlier version of this function also
// excluded low-order harmonics/subharmonics (P/2, 2P, ...) of each claimed
// period, reasoning that an eccentric orbit's power leaks into harmonics of
// its orbital frequency (the paper's own Sec.I discussion). That heuristic
// was tested and REJECTED: on GJ876, planets b (P=61.12 d) and c (P=30.09 d)
// sit in a genuine 2:1 mean-motion resonance, so b's subharmonic at ~30.5 d
// falls inside the tolerance band around c's real period, and excluding
// harmonics wrongly excluded the real second planet. Compact multi-planet
// systems are commonly resonant, so blanket harmonic exclusion is unsafe in
// general; only the fundamental is excluded here. See
// notes/REALDATA_SIMPLIFICATIONS.md for the full writeup of this finding.
inline bool in_exclusion_zone(double P, const std::vector<double> &claimed, double tol = 0.03) {
    for (double c : claimed) if (std::fabs(std::log(P / c)) <= tol) return true;
    return false;
}

// Generic coarse-grid + local-refine period search over [P_min, P_max] for
// either weighted_ls_peak or weighted_gls_peak (passed as peak_fn).
// `exclude` lists periods already claimed by earlier iterations of a
// sequential multi-planet search; grid points within `exclude_tol` (log
// distance) of any of them are skipped, forcing the search to a genuinely
// new period rather than a residual sidelobe of an already-detected signal.
//
// Optimisation: log-spaced period grid is cached thread-locally keyed by
// (P_min, P_max, n_grid). RV grids are typically the same across all method
// blocks, so rebuilding 4000 exp() values per call was pure waste.
inline PeriodogramPeak periodogram_search(
    const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
    double P_min, double P_max, int n_grid,
    const std::function<PeriodogramPeak(const Eigen::VectorXd &, const Eigen::VectorXd &,
                                         const Eigen::VectorXd &, double)> &peak_fn,
    const std::vector<double> &exclude = {}, double exclude_tol = 0.06) {
    thread_local double cPmin = 0, cPmax = 0;
    thread_local int cn_grid = 0;
    thread_local std::vector<double> Pg;
    if (cPmin != P_min || cPmax != P_max || cn_grid != n_grid) {
        double lo = std::log(P_min), hi = std::log(P_max);
        Pg.assign(n_grid, 0.0);
        for (int i = 0; i < n_grid; ++i) Pg[i] = std::exp(lo + (hi - lo) * i / (n_grid - 1));
        cPmin = P_min; cPmax = P_max; cn_grid = n_grid;
    }
    double best_power = -1; int best_i = -1;
    for (int i = 0; i < n_grid; ++i) {
        if (!exclude.empty() && in_exclusion_zone(Pg[i], exclude, exclude_tol)) continue;
        double pw = peak_fn(t, y, w, Pg[i]).power;
        if (pw > best_power) { best_power = pw; best_i = i; }
    }
    if (best_i < 0) { // entire grid excluded (degenerate/tiny period range): fall back to unexcluded search
        for (int i = 0; i < n_grid; ++i) {
            double pw = peak_fn(t, y, w, Pg[i]).power;
            if (pw > best_power) { best_power = pw; best_i = i; }
        }
    }
    double Plo = Pg[std::max(0, best_i - 1)], Phi = Pg[std::min(n_grid - 1, best_i + 1)];
    auto negf = [&](double P) { return -peak_fn(t, y, w, P).power; };
    double P_hat = brent_bounded(negf, Plo, Phi, 1e-7);
    return peak_fn(t, y, w, P_hat);
}

// Vectorised LS / GLS periodogram: build (n x n_grid) cos / sin matrices in
// ONE Eigen call (SIMD-vectorised cos/sin), then reduce all grid points in
// parallel via column-wise dot products. ~10-30x faster than the per-grid-
// point peak_fn loop for n_grid >= 1000. The brent refinement at the end is
// unchanged (it's only a handful of peak evaluations).
//
// Returns the (best_period, best_power) on the coarse grid; the caller does
// brent refinement to get the final peak.
struct VectorisedPower { double period, power; };

// kind: 0 = LS (cos+sin), 1 = GLS (cos+sin+offset)
// Output `powers` is filled with the power at every grid point (excluding
// any inside an exclusion zone, which is set to -INF). Returns (best_i, peak).
inline void vectorised_periodogram_powers(
    const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
    const std::vector<double> &Pg, bool gls,
    Eigen::VectorXd &powers_out, const std::vector<double> &exclude = {},
    double exclude_tol = 0.06) {
    int n = (int)t.size();
    int G = (int)Pg.size();
    // om[j] = 2*pi / Pg[j]
    Eigen::VectorXd om(G);
    for (int j = 0; j < G; ++j) om(j) = 2 * PI / Pg[j];
    // phase[i,j] = om[j] * t[i]; build (n, G)
    Eigen::MatrixXd phase = t * om.transpose();   // outer product, SIMD
    Eigen::MatrixXd C(n, G), S(n, G);
    // sincos would be faster but Eigen's sincos is only via sin/cos pair
    C = phase.array().cos();
    S = phase.array().sin();

    // weighted y, weighted columns
    Eigen::VectorXd wy = w.array() * y.array();
    Eigen::MatrixXd Wc = w.array().matrix().asDiagonal() * C;
    Eigen::MatrixXd Ws = w.array().matrix().asDiagonal() * S;
    // Cc[j] = sum_i w[i] c[i,j]^2  =  sum_i (Wc[i,j]) * c[i,j]
    Eigen::VectorXd Cc = Wc.cwiseProduct(C).colwise().sum();
    Eigen::VectorXd Ss = Ws.cwiseProduct(S).colwise().sum();
    Eigen::VectorXd Cs = Wc.cwiseProduct(S).colwise().sum();
    Eigen::VectorXd Cy = Wc.cwiseProduct(y.replicate(1, G)).colwise().sum();
    Eigen::VectorXd Sy = Ws.cwiseProduct(y.replicate(1, G)).colwise().sum();
    // For GLS we additionally need the offset column (vector of ones).
    // Co[j] = sum_i w[i] c[i,j], So[j] = sum_i w[i] s[i,j]
    Eigen::VectorXd Co = Wc.colwise().sum();
    Eigen::VectorXd So = Ws.colwise().sum();
    double Wo = w.sum();          // scalar
    double Yo = wy.sum();         // scalar
    if (gls) {
        // 3x3 system per grid point: XtWX = [[Cc,Cs,Co],[Cs,Ss,So],[Co,So,Wo]]
        // We can vectorise the solve via a closed-form formula for the
        // 3x3 inverse (much cheaper than 3x3 ldlt per grid point).
        // Wo and Yo are scalars; broadcast into vector ops as needed.
        Eigen::VectorXd det = Cc.cwiseProduct(Ss) * Wo
                            + 2 * Cs.cwiseProduct(So.cwiseProduct(Co))
                            - Co.cwiseProduct(Ss.cwiseProduct(Co))
                            - Cc.cwiseProduct(So.cwiseProduct(So))
                            - Eigen::VectorXd::Constant(Cc.size(), Wo).cwiseProduct(Cs.cwiseProduct(Cs));
        // det can be ~0 at degenerate frequencies; clamp
        det = det.cwiseMax(1e-300);
        // adjugate-style minors for inverse
        Eigen::VectorXd Wo_v = Eigen::VectorXd::Constant(Cc.size(), Wo);
        Eigen::VectorXd m00 = Ss.cwiseProduct(Wo_v) - So.cwiseProduct(So);
        Eigen::VectorXd m01 = -(Cs.cwiseProduct(Wo_v) - So.cwiseProduct(Co));
        Eigen::VectorXd m02 = Cs.cwiseProduct(So) - Ss.cwiseProduct(Co);
        Eigen::VectorXd m10 = m01;
        Eigen::VectorXd m11 = Cc.cwiseProduct(Wo_v) - Co.cwiseProduct(Co);
        Eigen::VectorXd m12 = -(Cc.cwiseProduct(So) - Cs.cwiseProduct(Co));
        Eigen::VectorXd m20 = m02;
        Eigen::VectorXd m21 = m12;
        Eigen::VectorXd m22 = Cc.cwiseProduct(Ss) - Cs.cwiseProduct(Cs);
        Eigen::VectorXd rhs0 = Cy, rhs1 = Sy;
        Eigen::VectorXd rhs2 = Eigen::VectorXd::Constant(Cc.size(), Yo);
        Eigen::VectorXd A = (m00.cwiseProduct(rhs0) + m01.cwiseProduct(rhs1) + m02.cwiseProduct(rhs2)).cwiseQuotient(det);
        Eigen::VectorXd B = (m10.cwiseProduct(rhs0) + m11.cwiseProduct(rhs1) + m12.cwiseProduct(rhs2)).cwiseQuotient(det);
        Eigen::VectorXd Cc_co = (m20.cwiseProduct(rhs0) + m21.cwiseProduct(rhs1) + m22.cwiseProduct(rhs2)).cwiseQuotient(det);
        powers_out = A.cwiseProduct(Cy) + B.cwiseProduct(Sy) + Cc_co.cwiseProduct(rhs2);
    } else {
        // LS: det = Cc*Ss - Cs^2; A = (Cy*Ss - Sy*Cs)/det; B = (Cc*Sy - Cs*Cy)/det
        // power = A*Cy + B*Sy
        Eigen::VectorXd det = (Cc.cwiseProduct(Ss) - Cs.cwiseProduct(Cs)).cwiseMax(1e-300);
        Eigen::VectorXd A = (Cy.cwiseProduct(Ss) - Sy.cwiseProduct(Cs)).cwiseQuotient(det);
        Eigen::VectorXd B = (Cc.cwiseProduct(Sy) - Cs.cwiseProduct(Cy)).cwiseQuotient(det);
        powers_out = A.cwiseProduct(Cy) + B.cwiseProduct(Sy);
    }

    // Apply exclusion zones
    if (!exclude.empty()) {
        for (int i = 0; i < G; ++i) {
            if (in_exclusion_zone(Pg[i], exclude, exclude_tol)) powers_out(i) = -1e300;
        }
    }
}

// Fast drop-in replacement for periodogram_search() when using LS or GLS.
// Same return type, same brent refinement. Re-uses the grid cache from
// periodogram_search.
inline PeriodogramPeak vectorised_periodogram_search(
    const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
    double P_min, double P_max, int n_grid, bool gls,
    const std::vector<double> &exclude = {}, double exclude_tol = 0.06) {
    thread_local double cPmin = 0, cPmax = 0;
    thread_local int cn_grid = 0;
    thread_local std::vector<double> Pg;
    if (cPmin != P_min || cPmax != P_max || cn_grid != n_grid) {
        double lo = std::log(P_min), hi = std::log(P_max);
        Pg.assign(n_grid, 0.0);
        for (int i = 0; i < n_grid; ++i) Pg[i] = std::exp(lo + (hi - lo) * i / (n_grid - 1));
        cPmin = P_min; cPmax = P_max; cn_grid = n_grid;
    }
    Eigen::VectorXd powers;
    vectorised_periodogram_powers(t, y, w, Pg, gls, powers, exclude, exclude_tol);
    int best_i;
    double best_power = powers.maxCoeff(&best_i);
    if (best_power < -1e100) { // whole grid excluded; fall back
        Eigen::VectorXd powers2;
        vectorised_periodogram_powers(t, y, w, Pg, gls, powers2);
        best_power = powers2.maxCoeff(&best_i);
    }
    double Plo = Pg[std::max(0, best_i - 1)], Phi = Pg[std::min(n_grid - 1, best_i + 1)];
    // Brent refinement using the scalar peak function (just a few calls)
    auto peak = gls ? weighted_gls_peak : weighted_ls_peak;
    auto negf = [&](double P) { return -peak(t, y, w, P).power; };
    double P_hat = brent_bounded(negf, Plo, Phi, 1e-7);
    return peak(t, y, w, P_hat);
}

// One-year alias check (paper's own Eq. 11, Algorithm 1 step 3): if the
// candidate's alias period P_alias = (1/P +/- 1/365.25)^-1 achieves higher
// power than the candidate itself, swap to it. Returns the (possibly
// swapped) period; the caller re-evaluates amplitude/phase at the returned
// period. This directly implements the sidelobe/alias-handling the paper
// itself specifies as part of the algorithm, not an optional add-on.
inline double alias_swap_period(
    const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
    double P_candidate, double candidate_power,
    const std::function<PeriodogramPeak(const Eigen::VectorXd &, const Eigen::VectorXd &,
                                         const Eigen::VectorXd &, double)> &peak_fn) {
    double best_P = P_candidate, best_power = candidate_power;
    for (double sign : {+1.0, -1.0}) {
        double f_alias = 1.0 / P_candidate + sign / 365.25;
        if (f_alias <= 0) continue;
        double P_alias = 1.0 / f_alias;
        if (P_alias < 1.0 || P_alias > 1.0e5) continue;
        PeriodogramPeak pk = peak_fn(t, y, w, P_alias);
        if (pk.power > best_power) { best_power = pk.power; best_P = P_alias; }
    }
    return best_P;
}



// ------------------------------------------- exact Baluev FAP formulas ---
//
// These replace an earlier, incorrect hand-built approximation
// (N_eff/sqrt(2pi) * sqrt(z) * exp(-z/2)) that matched neither Baluev
// (2008)'s sinusoidal formula nor Baluev (2015)'s Keplerian one -- wrong
// exponential decay rate AND wrong prefactor structure. What follows is
// transcribed directly from the two source papers, not re-derived or
// approximated further.
//
// Both papers define z = (g_H - g_K)/2, i.e. HALF the reduction in
// chi-square (chi-square computed with weights w_i = 1/sigma_i^2, exactly
// this project's convention) from adding the candidate signal -- NOT the
// full reduction. Every z passed to the functions below must already be
// halved by the caller.

// T_eff, W: shared by both formulas (Baluev 2008 Eq. 11; Baluev 2015 Eq. 21
// reuses the identical W). T_eff = sqrt(4*pi*(t2bar - tbar^2)), with tbar,
// t2bar the WEIGHTED means of t and t^2 (weights = the same w_i used in the
// chi-square/z above) -- "weighted averages of observation times taken
// with the weights appearing in the chi-square function" (Baluev 2008).
inline double baluev_Teff(const Eigen::VectorXd &t, const Eigen::VectorXd &w) {
    double wsum = w.sum();
    double tbar = (w.array() * t.array()).sum() / wsum;
    double t2bar = (w.array() * t.array().square()).sum() / wsum;
    return std::sqrt(4 * PI * std::max(1e-30, t2bar - tbar * tbar));
}
inline double baluev_W(double f_max, double T_eff) { return f_max * T_eff; }

// Baluev (2008) Eq. 11, sinusoidal/Lomb-Scargle-family periodogram, free
// frequency: FAP(z) <~ W * exp(-z) * sqrt(z). Used for LS, GLS, NOMP, L1/BP
// (all sinusoidal-atom methods in this project's battery).
inline double fap_sinusoidal(double z, double W) {
    if (z <= 0) return 1.0;
    return std::min(1.0, W * std::exp(-z) * std::sqrt(z));
}

// Baluev (2015) Eq. 21 (free-frequency case) + Eq. 24's semi-empiric X, Y
// fits, EXACT Keplerian-periodogram FAP -- KNOMP's own literature-correct
// stopping criterion, not a sinusoidal proxy:
//   FAP(z) <~ W*exp(-z)*sqrt(z) * [ 2z*X(e_max) + Y(e_max)*sqrt(pi*z) ]
// with beta = e_max/(1+sqrt(1-e_max^2)), epsilon = 2*beta/(1-beta^2), and
//   X(e) = 0.5*eps^2 + 0.0350*eps^6 + 0.3334*eps^3.86 + 0.0774*eps^5.03
//   Y(e) = eps + 0.3125*eps^6 + 2.3725*eps^3.05 + 0.9868*eps^4.86
inline void baluev_keplerian_XY(double e_max, double &X, double &Y) {
    double eta = std::sqrt(std::max(0.0, 1.0 - e_max * e_max));
    double beta = e_max / (1.0 + eta);
    double eps = 2.0 * beta / (1.0 - beta * beta);
    X = 0.5 * std::pow(eps, 2) + 0.0350 * std::pow(eps, 6) + 0.3334 * std::pow(eps, 3.86) + 0.0774 * std::pow(eps, 5.03);
    Y = eps + 0.3125 * std::pow(eps, 6) + 2.3725 * std::pow(eps, 3.05) + 0.9868 * std::pow(eps, 4.86);
}
inline double fap_keplerian(double z, double W, double e_max) {
    if (z <= 0) return 1.0;
    double X, Y; baluev_keplerian_XY(e_max, X, Y);
    double bracket = 2.0 * z * X + Y * std::sqrt(PI * z);
    return std::min(1.0, W * std::exp(-z) * std::sqrt(z) * bracket);
}

// Bisection inverse of a monotonically-decreasing-in-z FAP function.
inline double solve_z_for_fap(const std::function<double(double)> &fap_fn,
                               double target_fap, double lo = 1e-3, double hi = 400.0) {
    for (int iter = 0; iter < 200; ++iter) {
        double mid = 0.5 * (lo + hi);
        if (fap_fn(mid) > target_fap) lo = mid; else hi = mid;
    }
    return 0.5 * (lo + hi);
}

// LS+KR's OWN threshold form, per DESIGN.md Sec.3.4 (distinct in functional
// form from the Baluev extreme-value approximations above -- log(N), not
// exp(-z)*sqrt(z)):
//   tau_asymptotic = sigma^2 [ log N - log log(1/(1-Pfa)) ]
// in the same weighted chi-square (z, halved) units as everywhere else.
inline double lskr_cfar_threshold(double N, double Pfa) {
    return std::log((double)N) - std::log(-std::log(1.0 - Pfa));
}

// KNOMP's OWN stopping rule, per Algorithm 1 / Sec.II-H of the paper: a
// CONJUNCTION of the exact Baluev-Keplerian CFAR check above AND a BIC
// decrease (Schwarz 1978): z > Delta_k/2 * ln(N) (the factor 1/2 carries
// through because z here is Baluev's halved chi-square reduction, while
// the paper's Delta_BIC = Delta_k*ln(N) - 2z is stated in FULL
// chi-square/likelihood-ratio units -- see Sec.II-H). Delta_k=4 for one
// full Keplerian atom's nonlinear parameters (P,u,v,M0); the gain is
// linear and profiled out, so not counted.
inline bool knomp_conjunctive_accept(double z_half, double z_half_cfar_threshold, int N, int delta_k = 4,
                                      bool bic_enabled = true) {
    if (!bic_enabled) return z_half >= z_half_cfar_threshold;
    double bic_term_half = 0.5 * delta_k * std::log((double)N);
    return z_half >= z_half_cfar_threshold && z_half > bic_term_half;
}

// ---------------------------------------------------- weighted KNOMP fit ---

// Weighted KNOMP single-planet detection: circular coarse grid (log-spaced)
// + multi-start eccentric LM refine, with inverse-variance weights. Mirrors
// nk_knomp.hpp::knomp_detection_search but (a) weighted and (b) log-spaced
// grid appropriate for real multi-decade period ranges.
struct WKnompFit { double P, e, omega, M0, K, wsse; };

inline double knomp_circular_wsse(double P, const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                   const Eigen::VectorXd &w) {
    double om = 2 * PI / P;
    Eigen::MatrixXd X(t.size(), 2);
    X.col(0) = (om * t.array()).cos();
    X.col(1) = (om * t.array()).sin();
    Eigen::MatrixXd Xw = w.asDiagonal() * X;
    Eigen::Vector2d coeffs = (X.transpose() * Xw).ldlt().solve(Xw.transpose() * y);
    Eigen::VectorXd resid = y - X * coeffs;
    return (w.array() * resid.array().square()).sum();
}

inline Eigen::VectorXd knomp_weighted_residual(const Eigen::VectorXd &theta, const Eigen::VectorXd &t,
                                                const Eigen::VectorXd &y, const Eigen::VectorXd &sqrtw) {
    double P = theta(0), e = std::min(std::max(theta(1), 0.0), 0.97);
    double omega = theta(2), M0 = theta(3);
    Eigen::VectorXd f = f_signal_vec(t, P, e, omega, M0);
    double fw = (sqrtw.array().square() * f.array() * f.array()).sum();
    double num = (sqrtw.array().square() * f.array() * y.array()).sum();
    double K = num / fw;
    return sqrtw.array() * (y - K * f).array();
}

inline WKnompFit knomp_weighted_detection(const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                           const Eigen::VectorXd &w, double P_min, double P_max,
                                           std::mt19937_64 &rng, int n_grid = 4000, int n_top = 5,
                                           int n_multistart_e = 4,
                                           const std::vector<double> &exclude = {},
                                           double exclude_tol = 0.06) {
    double lo = std::log(P_min), hi = std::log(P_max);
    std::vector<double> Pg(n_grid), sse(n_grid);
    for (int i = 0; i < n_grid; ++i) {
        Pg[i] = std::exp(lo + (hi - lo) * i / (n_grid - 1));
        sse[i] = knomp_circular_wsse(Pg[i], t, y, w);
    }
    std::vector<int> order(n_grid);
    for (int i = 0; i < n_grid; ++i) order[i] = i;
    std::sort(order.begin(), order.end(), [&](int a, int b) { return sse[a] < sse[b]; });
    std::vector<double> chosen;
    for (int idx : order) {
        double Pc = Pg[idx];
        if (!exclude.empty() && in_exclusion_zone(Pc, exclude, exclude_tol)) continue;
        bool ok = true;
        for (double c : chosen) if (std::fabs(std::log(Pc / c)) <= 0.02) { ok = false; break; }
        if (ok) chosen.push_back(Pc);
        if ((int)chosen.size() >= n_top) break;
    }
    if (chosen.empty()) // whole top-order excluded: fall back to best unexcluded single point
        for (int idx : order) { chosen.push_back(Pg[idx]); break; }
    Eigen::VectorXd sqrtw = w.array().sqrt();
    std::uniform_real_distribution<double> unif01(0.0, 1.0);
    WKnompFit best; best.wsse = std::numeric_limits<double>::infinity(); best.P = -1;
    for (double Pc : chosen) {
        for (int s = 0; s < n_multistart_e; ++s) {
            double e0 = unif01(rng) * 0.7;
            double omega0 = unif01(rng) * 2 * PI, M00 = unif01(rng) * 2 * PI;
            Eigen::VectorXd loB(4), hiB(4), x0(4);
            loB << Pc * 0.95, 0.0, -PI, -2 * PI;
            hiB << Pc * 1.05, 0.97, 3 * PI, 4 * PI;
            x0 << Pc, e0, omega0, M00;
            for (int i = 0; i < 4; ++i) x0(i) = std::min(std::max(x0(i), loB(i)), hiB(i));
            auto resid = [&](const Eigen::VectorXd &th) { return knomp_weighted_residual(th, t, y, sqrtw); };
            static thread_local Eigen::VectorXd resid_buf;
            auto resid_ref = [&](const Eigen::VectorXd &th) -> const Eigen::VectorXd& { resid_buf = resid(th); return resid_buf; };
            LMResult res = levenberg_marquardt_bounded(resid_ref, x0, loB, hiB, 1e-10, 1e-10, 80);
            if (res.cost < best.wsse) {
                best.P = res.x(0); best.e = std::min(std::max(res.x(1), 0.0), 0.97);
                best.omega = res.x(2); best.M0 = res.x(3); best.wsse = res.cost;
            }
        }
    }
    Eigen::VectorXd f = f_signal_vec(t, best.P, best.e, best.omega, best.M0);
    double fw = (w.array() * f.array() * f.array()).sum();
    best.K = (w.array() * f.array() * y.array()).sum() / fw;
    return best;
}

// ------------------------------------ GP-aware (full-covariance) KNOMP fit ---
//
// Exact analogues of knomp_circular_wsse / knomp_weighted_residual /
// knomp_weighted_detection above, but using a full covariance Sigma
// (diagonal weighting is the special case Sigma=diag(1/w)) via its
// Cholesky factor L (Sigma=LL^T), whitening every quantity by a
// triangular solve L^-1(.) rather than an elementwise multiply. This is
// what KNOMP's own GP/correlated noise term (Sec.II-C's Sigma(phi),
// Algorithm 1's "GP HYPERPARAMETER UPDATE" step) requires: once K_act(phi)
// is non-diagonal, "weight" is no longer a per-point scalar.
inline double knomp_circular_wsse_gp(double P, const Eigen::VectorXd &t,
                                      const Eigen::VectorXd &yw,
                                      const Eigen::MatrixXd &Lmat) {
    // Hot-path rewrite: thread-local scratch for c, s; raw pointer access;
    // precompute y' = L*yw once... wait, yw IS the pre-whitened signal,
    // we only need L*X (the design in whitened space). Use Eigen's
    // triangular solver on a stacked (c | s) Matrix without re-allocating
    // per grid point.
    const int n = (int)t.size();
    thread_local Eigen::MatrixXd X;
    if ((int)X.rows() != n || (int)X.cols() != 2) X.resize(n, 2);
    thread_local Eigen::MatrixXd Xw;
    if ((int)Xw.rows() != n || (int)Xw.cols() != 2) Xw.resize(n, 2);
    const double om = 2 * PI / P;
    Eigen::ArrayXd phase = om * t.array();
    X.col(0) = phase.cos();
    X.col(1) = phase.sin();
    // Triangular solve on 2 columns in one call (Eigen handles this efficiently).
    Xw = Lmat.triangularView<Eigen::Lower>().solve(X);
    // 2x2 weighted least squares: minimize ||yw - Xw * coeffs||^2
    Eigen::Matrix2d XtWX = Xw.transpose() * Xw;
    Eigen::Vector2d XtWy = Xw.transpose() * yw;
    Eigen::Vector2d coeffs = XtWX.ldlt().solve(XtWy);
    Eigen::Vector2d diff = XtWy - XtWX * coeffs;
    // ||yw - Xw*c||^2 = ||yw||^2 - 2*c'X'yw + c'X'Xc = ||yw||^2 - c'(X'yw + (X'X-X'X)c)
    // Simplest path: full residual
    return (yw - Xw * coeffs).squaredNorm();
}

inline Eigen::VectorXd knomp_gp_residual(const Eigen::VectorXd &theta, const Eigen::VectorXd &t,
                                          const Eigen::VectorXd &y, const Eigen::MatrixXd &Lmat,
                                          const Eigen::VectorXd &yw_pre) {
    double P = theta(0), e = std::min(std::max(theta(1), 0.0), 0.97);
    double omega = theta(2), M0 = theta(3);
    Eigen::VectorXd f = f_signal_vec(t, P, e, omega, M0);
    Eigen::VectorXd fw = Lmat.triangularView<Eigen::Lower>().solve(f);
    // yw_pre is the pre-whitened y; reused across all LM iterations of one
    // knomp_gp_detection call (caller is responsible for passing it).
    double K = fw.dot(yw_pre) / fw.squaredNorm();
    return yw_pre - K * fw;
}

inline WKnompFit knomp_gp_detection(const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                     const Eigen::MatrixXd &Lmat, double P_min, double P_max,
                                     std::mt19937_64 &rng, int n_grid = 4000, int n_top = 5,
                                     int n_multistart_e = 4,
                                     const std::vector<double> &exclude = {},
                                     double exclude_tol = 0.06) {
    // Cached log-spaced period grid: rebuilt only when (P_min, P_max,
    // n_grid) changes. Eliminates 4000 std::exp() evaluations per call.
    thread_local double cPmin = 0, cPmax = 0;
    thread_local int cn_grid = 0;
    thread_local std::vector<double> Pg;
    if (cPmin != P_min || cPmax != P_max || cn_grid != n_grid) {
        double lo = std::log(P_min), hi = std::log(P_max);
        Pg.assign(n_grid, 0.0);
        for (int i = 0; i < n_grid; ++i) Pg[i] = std::exp(lo + (hi - lo) * i / (n_grid - 1));
        cPmin = P_min; cPmax = P_max; cn_grid = n_grid;
    }
    std::vector<double> sse(n_grid);
    Eigen::VectorXd yw = Lmat.triangularView<Eigen::Lower>().solve(y);
    for (int i = 0; i < n_grid; ++i) {
        sse[i] = knomp_circular_wsse_gp(Pg[i], t, yw, Lmat);
    }
    std::vector<int> order(n_grid);
    for (int i = 0; i < n_grid; ++i) order[i] = i;
    std::sort(order.begin(), order.end(), [&](int a, int b) { return sse[a] < sse[b]; });
    std::vector<double> chosen;
    for (int idx : order) {
        double Pc = Pg[idx];
        if (!exclude.empty() && in_exclusion_zone(Pc, exclude, exclude_tol)) continue;
        bool ok = true;
        for (double c : chosen) if (std::fabs(std::log(Pc / c)) <= 0.02) { ok = false; break; }
        if (ok) chosen.push_back(Pc);
        if ((int)chosen.size() >= n_top) break;
    }
    if (chosen.empty())
        for (int idx : order) { chosen.push_back(Pg[idx]); break; }
    std::uniform_real_distribution<double> unif01(0.0, 1.0);
    WKnompFit best; best.wsse = std::numeric_limits<double>::infinity(); best.P = -1;
    for (double Pc : chosen) {
        for (int s = 0; s < n_multistart_e; ++s) {
            double e0 = unif01(rng) * 0.7;
            double omega0 = unif01(rng) * 2 * PI, M00 = unif01(rng) * 2 * PI;
            Eigen::VectorXd loB(4), hiB(4), x0(4);
            loB << Pc * 0.95, 0.0, -PI, -2 * PI;
            hiB << Pc * 1.05, 0.97, 3 * PI, 4 * PI;
            x0 << Pc, e0, omega0, M00;
            for (int i = 0; i < 4; ++i) x0(i) = std::min(std::max(x0(i), loB(i)), hiB(i));
            auto resid = [&](const Eigen::VectorXd &th) { return knomp_gp_residual(th, t, y, Lmat, yw); };
            static thread_local Eigen::VectorXd resid_buf2;
            auto resid_ref = [&](const Eigen::VectorXd &th) -> const Eigen::VectorXd& { resid_buf2 = resid(th); return resid_buf2; };
            LMResult res = levenberg_marquardt_bounded(resid_ref, x0, loB, hiB, 1e-10, 1e-10, 80);
            if (res.cost < best.wsse) {
                best.P = res.x(0); best.e = std::min(std::max(res.x(1), 0.0), 0.97);
                best.omega = res.x(2); best.M0 = res.x(3); best.wsse = res.cost;
            }
        }
    }
    Eigen::VectorXd f = f_signal_vec(t, best.P, best.e, best.omega, best.M0);
    Eigen::VectorXd fw = Lmat.triangularView<Eigen::Lower>().solve(f);
    best.K = fw.dot(yw) / fw.squaredNorm();
    return best;
}

} // namespace nk
