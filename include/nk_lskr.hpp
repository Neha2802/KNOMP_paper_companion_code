// nk_lskr.hpp
//
// Weighted C++ implementation of the LS+KR benchmark of DESIGN.md
// ("Iterative Lomb-Scargle + Keplerian Refinement"): detect via
// (generalized) Lomb-Scargle periodogram peak -> initialize a circular
// orbit at that peak -> globally re-fit ALL currently-detected planets'
// Keplerian parameters jointly by Levenberg-Marquardt -> repeat until the
// periodogram no longer clears a CFAR-style threshold or max_planets is hit.
//
// This mirrors DESIGN.md Section 4 pseudocode exactly, generalized to
// inverse-variance weights (DESIGN.md's Eq. in Sec.3.1/3.3 assumes i.i.d.
// sigma^2; real HARPS data is heteroskedastic, so every sum-of-squares in
// this file is a *weighted* sum of squares, weight = 1/sigma_n^2).
#pragma once
#include <Eigen/Dense>
#include <chrono>
#include <cstdio>
#include <vector>
#include "nk_kepler.hpp"
#include "nk_optimize.hpp"
#include "nk_realdata.hpp"

namespace nk {

// Per-call LSKR sub-stage timing accumulator. Thread-local so multi-threaded
// callers (none currently) wouldn't collide; populated only when the env
// var NK_LSKR_PROFILE=1 is set so production runs are unaffected.
struct LsKrProfile {
    int n_outer_iters = 0;
    int total_lm_iters = 0;
    int total_lm_iters_actual = 0;       // sum of actual LM iterations used
    int max_lm_iters_actual = 0;         // largest single LM call
    int total_lm_residual_evals = 0;
    int total_lm_jacobian_evals = 0;     // each FD pair is 2 residual calls
    double t_total_periodogram = 0;
    double t_total_design = 0;
    double t_total_gains = 0;
    double t_total_lm_other = 0;
    void print(const char* tag) const {
        std::fprintf(stderr,
                     "[LSKR_PROFILE %s] outer=%d lm_calls=%d lm_iters_actual(total)=%d "
                     "(max_single=%d) residual_evals=%d jac_evals=%d "
                     "periodogram=%.3fs design=%.3fs gains=%.3fs "
                     "lm_other=%.3fs\n",
                     tag, n_outer_iters, total_lm_iters, total_lm_iters_actual,
                     max_lm_iters_actual,
                     total_lm_residual_evals, total_lm_jacobian_evals,
                     t_total_periodogram, t_total_design, t_total_gains,
                     t_total_lm_other);
    }
};
inline LsKrProfile& lskr_profile_slot() {
    static thread_local LsKrProfile p;
    return p;
}

struct LsKrPlanet { double P, e, omega, M0, K; };

// Joint weighted design matrix for m Keplerian atoms (unit amplitude each).
inline Eigen::MatrixXd lskr_design(const Eigen::VectorXd &t, const std::vector<LsKrPlanet> &pl) {
    auto t0 = std::chrono::steady_clock::now();
    Eigen::MatrixXd F(t.size(), pl.size());
    const int n = (int)t.size();
    for (size_t l = 0; l < pl.size(); ++l)
        f_signal_vec_into(F.col(l).data(), t, pl[l].P, pl[l].e, pl[l].omega, pl[l].M0);
    lskr_profile_slot().t_total_design +=
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return F;
}

// Linear (weighted) amplitude solve for fixed nonlinear parameters (DESIGN.md 3.3: K = pinv(F) y).
inline Eigen::VectorXd lskr_gains(const Eigen::MatrixXd &F, const Eigen::VectorXd &y,
                                   const Eigen::VectorXd &w) {
    auto t0 = std::chrono::steady_clock::now();
    Eigen::MatrixXd Fw = w.asDiagonal() * F;
    Eigen::VectorXd K = (F.transpose() * Fw).ldlt().solve(Fw.transpose() * y);
    lskr_profile_slot().t_total_gains +=
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return K;
}

// Stack (P,e,omega,M0) of all planets into one Theta vector for the LM solver.
inline Eigen::VectorXd lskr_pack(const std::vector<LsKrPlanet> &pl) {
    Eigen::VectorXd th(4 * pl.size());
    for (size_t l = 0; l < pl.size(); ++l) { th(4*l)=pl[l].P; th(4*l+1)=pl[l].e; th(4*l+2)=pl[l].omega; th(4*l+3)=pl[l].M0; }
    return th;
}
inline std::vector<LsKrPlanet> lskr_unpack(const Eigen::VectorXd &th) {
    std::vector<LsKrPlanet> pl(th.size() / 4);
    for (size_t l = 0; l < pl.size(); ++l) { pl[l].P=th(4*l); pl[l].e=th(4*l+1); pl[l].omega=th(4*l+2); pl[l].M0=th(4*l+3); }
    return pl;
}

// Hot-path scratch for LSKR residual: a single thread-local design matrix
// + gains + residual buffer that's resized (not re-allocated) as m grows.
// A full LSKR run on HD10180 evaluates this residual ~45K times -- the
// previous per-call Eigen::MatrixXd / VectorXd allocations dominated
// runtime (over 9 GB of churn in the Eigen heap). On first call, allocate
// to a generous size; on subsequent calls, .conservativeResize() reuses
// the buffer if it's already big enough.
//
// Layout: each scratch cell holds (F: n_obs x m_max), (Fw: n_obs x m_max),
// (FtWF: m_max x m_max), (residual: n_obs), (w: n_obs). m_max grows
// monotonically across the outer iteration loop, so the buffer is sized
// once to the largest needed (n_planets = 10 in practice) and reused.
struct LsKrResidualScratch {
    Eigen::MatrixXd F;          // n_obs x m_max
    Eigen::MatrixXd Fw;         // n_obs x m_max
    Eigen::MatrixXd FtWF;       // m_max x m_max  (F^T W F) -- LLT in-place
    Eigen::MatrixXd M_inv;      // m_max x m_max  (cached inverse of FtWF)
    Eigen::VectorXd w;          // n_obs
    Eigen::VectorXd residual;   // n_obs
    Eigen::VectorXd W_y;        // n_obs, w * y
    Eigen::VectorXd K;          // m_max
    Eigen::VectorXd FK;         // n_obs, F*K (computed once per residual call)
    // Analytic-Jacobian scratch (per-atom partials + intermediates)
    Eigen::VectorXd c_dP;       // n_obs
    Eigen::VectorXd c_de;       // n_obs
    Eigen::VectorXd c_domega;   // n_obs
    Eigen::VectorXd c_dM0;      // n_obs
    Eigen::VectorXd Wc;         // n_obs, scratch for (w .* c)
    Eigen::VectorXd s_l_j;      // m_max, F^T (W c) for one (l,j)
    Eigen::VectorXd dK_l_j;     // m_max, scratch for (db - dM K) and dK
    Eigen::VectorXd F_dK;       // n_obs, F @ dK_l_j
    int n = 0;
    int m = 0;
};
inline LsKrResidualScratch& lskr_residual_scratch(int n, int m) {
    static thread_local LsKrResidualScratch s;
    if (s.n < n || s.F.cols() < m) {
        s.F       = Eigen::MatrixXd::Zero(n, m);
        s.Fw      = Eigen::MatrixXd::Zero(n, m);
        s.FtWF    = Eigen::MatrixXd::Zero(m, m);
        s.M_inv   = Eigen::MatrixXd::Zero(m, m);
        s.w       = Eigen::VectorXd::Zero(n);
        s.residual= Eigen::VectorXd::Zero(n);
        s.W_y     = Eigen::VectorXd::Zero(n);
        s.K       = Eigen::VectorXd::Zero(m);
        s.FK      = Eigen::VectorXd::Zero(n);
        s.c_dP    = Eigen::VectorXd::Zero(n);
        s.c_de    = Eigen::VectorXd::Zero(n);
        s.c_domega= Eigen::VectorXd::Zero(n);
        s.c_dM0   = Eigen::VectorXd::Zero(n);
        s.Wc      = Eigen::VectorXd::Zero(n);
        s.s_l_j   = Eigen::VectorXd::Zero(m);
        s.dK_l_j  = Eigen::VectorXd::Zero(m);
        s.F_dK    = Eigen::VectorXd::Zero(n);
        s.n = n;
        s.m = m;
    }
    return s;
}

// Weighted residual for the joint LM refit -- HOT PATH (45K+ calls per
// LSKR run on HD10180). Pre-allocates F, Fw, w, residual into thread-local
// scratch; writes into them in place; returns a const-ref Eigen view of
// the scratch residual buffer so the LM can read .squaredNorm() etc.
inline const Eigen::VectorXd& lskr_joint_residual(const Eigen::VectorXd &theta, const Eigen::VectorXd &t,
                                                   const Eigen::VectorXd &y, const Eigen::VectorXd &sqrtw) {
    lskr_profile_slot().total_lm_residual_evals++;
    const int n = (int)t.size();
    const int m = (int)theta.size() / 4;
    auto& sc = lskr_residual_scratch(n, m);
    // Decode theta into a thread-local planet list (resized, not reallocated,
    // across calls). For m <= 64 we use a fixed-size stack array to avoid the
    // heap allocation entirely; only unusual callers (e.g. lskr_cfar_main
    // with --max-planets > 64) hit the heap-vector fallback.
    static thread_local std::vector<LsKrPlanet> pl_tl;
    LsKrPlanet pl_local[64];
    LsKrPlanet* pl = pl_local;
    if (m > 64) {
        pl_tl.resize(m);
        pl = pl_tl.data();
    }
    for (int l = 0; l < m; ++l) {
        pl[l].P     = theta(4*l);
        pl[l].e     = theta(4*l+1);
        pl[l].omega = theta(4*l+2);
        pl[l].M0    = theta(4*l+3);
    }
    for (int l = 0; l < m; ++l)
        f_signal_vec_into(sc.F.col(l).data(), t, pl[l].P,
                          pl[l].e, pl[l].omega, pl[l].M0);
    Eigen::Map<Eigen::VectorXd> w_map(sc.w.data(), n);
    w_map = sqrtw.array().square();
    for (int l = 0; l < m; ++l) sc.Fw.col(l) = sc.w.array() * sc.F.col(l).array();
    sc.FtWF.noalias() = sc.F.transpose() * sc.Fw;
    Eigen::Map<Eigen::VectorXd> Wy_map(sc.W_y.data(), n);
    Wy_map = sc.w.array() * y.array();
    sc.K = sc.FtWF.ldlt().solve(sc.F.transpose() * sc.W_y);
    Eigen::Map<Eigen::VectorXd> r_map(sc.residual.data(), n);
    r_map = sqrtw.array() * (y.array() - (sc.F * sc.K).array());
    return sc.residual;
}

// Adapter signature for levenberg_marquardt_jac's jacobian_fn callback.
using LmJacFn = std::function<void(const Eigen::VectorXd &, Eigen::MatrixXd &)>;

// Analytic Jacobian of the joint weighted residual r = sqrtw (y - F K),
// K = (F^T W F)^-1 F^T W y, W = diag(w).
//
// Math (one entry per (atom l, param j in {P, e, omega, M0})):
//   dr/dtheta_l^j = -sqrtw .* (K_l c_l^j + F dK_l^j)
// where
//   c_l^j  = df_l/dtheta_l^j                         (n-vector)
//   s_l^j  = F^T (W c_l^j)                           (m-vector)
//   dK_l^j = M^-1 (db - dM K)
//     db = (c_l^j)^T W y                              (only entry l nonzero)
//     (dM K)_l    = (c_l^j)^T W (F K) + (F_l)^T (W c_l^j) K_l
//     (dM K)_{a!=l} = -F_a^T (W c_l^j) K_l           = -K_l * (s_l^j)_a
//   So:
//     (db - dM K)_l    = (c_l^j)^T W y - (c_l^j)^T W (F K) - K_l (F_l^T W c_l^j)
//     (db - dM K)_{a!=l} = -K_l (s_l^j)_a
//   Then dK_l^j = M^-1 (db - dM K) and J[:, 4l+j] = -sqrtw .* (K_l c + F dK).
//
// Hot-path: reuses F/Fw/FtWF/M_inv/W_y/K/FK from lskr_residual_scratch.
// The residual is also written into scratch so that the LM's residual_fn
// callback can read it on the next iteration.
inline void lskr_joint_residual_and_jac(const Eigen::VectorXd &theta,
                                         const Eigen::VectorXd &t,
                                         const Eigen::VectorXd &y,
                                         const Eigen::VectorXd &sqrtw,
                                         Eigen::MatrixXd &J_out) {
    auto& prof = lskr_profile_slot();
    prof.total_lm_residual_evals++;
    prof.total_lm_jacobian_evals++;
    const int n = (int)t.size();
    const int m = (int)theta.size() / 4;
    auto& sc = lskr_residual_scratch(n, m);

    // 1. Decode theta into a planet list (stack array for m<=64,
    //    thread-local heap vector otherwise). Same scheme as
    //    lskr_joint_residual.
    static thread_local std::vector<LsKrPlanet> pl_tl;
    LsKrPlanet pl_local[64];
    LsKrPlanet* pl = pl_local;
    if (m > 64) { pl_tl.resize(m); pl = pl_tl.data(); }
    for (int l = 0; l < m; ++l) {
        pl[l].P     = theta(4*l);
        pl[l].e     = theta(4*l+1);
        pl[l].omega = theta(4*l+2);
        pl[l].M0    = theta(4*l+3);
    }

    // 2. We need both F and the per-atom partials. Use f_and_partials_into
    //    so the kepler solve is shared. The function writes both F.col(l)
    //    AND the four partials (c_dP, c_de, c_domega, c_dM0) for atom l.
    Eigen::Map<Eigen::VectorXd> w_map(sc.w.data(), n);
    w_map = sqrtw.array().square();
    Eigen::Map<Eigen::VectorXd> Wy_map(sc.W_y.data(), n);
    Wy_map = sc.w.array() * y.array();

    Eigen::VectorXd* c_arr[4] = {&sc.c_dP, &sc.c_de, &sc.c_domega, &sc.c_dM0};
    for (int l = 0; l < m; ++l) {
        f_and_partials_into(sc.F.col(l).data(),
                             sc.c_dP.data(), sc.c_de.data(),
                             sc.c_domega.data(), sc.c_dM0.data(),
                             t, pl[l].P, pl[l].e,
                             pl[l].omega, pl[l].M0);
    }

    // 3. Fw, FtWF, K, residual -- same as lskr_joint_residual.
    for (int l = 0; l < m; ++l)
        sc.Fw.col(l) = sc.w.array() * sc.F.col(l).array();
    sc.FtWF.noalias() = sc.F.transpose() * sc.Fw;
    Eigen::LLT<Eigen::MatrixXd> M_llt;
    M_llt.compute(sc.FtWF);
    sc.K = M_llt.solve(sc.F.transpose() * sc.W_y);
    sc.FK.noalias() = sc.F * sc.K;
    Eigen::Map<Eigen::VectorXd> r_map(sc.residual.data(), n);
    r_map = sqrtw.array() * (y.array() - sc.FK.array());

    // 4. M_inv = FtWF^-1.
    Eigen::MatrixXd I = Eigen::MatrixXd::Identity(m, m);
    sc.M_inv = M_llt.solve(I);

    // 5. Jacobian columns. The partials are already computed (and stored in
    //    sc.c_dP/de/domega/dM0 from step 2), so we just project them.
    for (int l = 0; l < m; ++l) {
        const double K_l = sc.K(l);
        for (int j = 0; j < 4; ++j) {
            Eigen::VectorXd &c = *(c_arr[j]);
            // Wc = w .* c
            sc.Wc = sc.w.array() * c.array();
            // s_l_j = F^T (Wc)        (m-vector)
            sc.s_l_j.noalias() = sc.F.transpose() * sc.Wc;
            // Scalar products we need:
            //   b_dot    = (Wc)^T y
            //   M_dot_K  = (Wc)^T (F K)
            //   F_lWc    = (s_l_j)_l  (column-l entry of F^T Wc)
            const double b_dot   = sc.Wc.dot(y);
            const double M_dot_K = sc.Wc.dot(sc.FK);
            const double s_l     = sc.s_l_j(l);
            // (db - dM K) m-vector:
            //   entry l:    b_dot - M_dot_K - K_l * s_l
            //   entry a!=l: -K_l * (s_l_j)_a
            sc.dK_l_j = -K_l * sc.s_l_j;
            sc.dK_l_j(l) = b_dot - M_dot_K - K_l * s_l;
            // dK_l^j = M_inv @ (db - dM K)   -- write into dK_l_j
            sc.dK_l_j = sc.M_inv * sc.dK_l_j;
            // F_dK = F @ dK_l^j
            sc.F_dK.noalias() = sc.F * sc.dK_l_j;
            // J[:, 4*l + j] = -sqrtw .* (K_l * c + F_dK)
            J_out.col(4*l + j) = -sqrtw.array() * (K_l * c.array() + sc.F_dK.array());
        }
    }
}

// One "Global Keplerian refit" step of DESIGN.md Sec.2/Sec.4 line 12-27:
// joint bounded LM over all currently-detected planets' (P,e,omega,M0),
// amplitudes profiled out at every LM trial step (variable projection).
inline std::vector<LsKrPlanet> lskr_global_refit(const Eigen::VectorXd &t, const Eigen::VectorXd &y,
                                                  const Eigen::VectorXd &w,
                                                  std::vector<LsKrPlanet> pl,
                                                  double bracket_frac = 0.08, int lm_max_iter = 100) {
    int m = pl.size();
    Eigen::VectorXd lo(4*m), hi(4*m), x0 = lskr_pack(pl);
    for (int l = 0; l < m; ++l) {
        lo(4*l) = pl[l].P * (1 - bracket_frac); hi(4*l) = pl[l].P * (1 + bracket_frac);
        lo(4*l+1) = 0.0; hi(4*l+1) = 0.97;
        lo(4*l+2) = -PI; hi(4*l+2) = 3 * PI;
        lo(4*l+3) = -2 * PI; hi(4*l+3) = 4 * PI;
    }
    Eigen::VectorXd sqrtw = w.array().sqrt();
    auto resid = [&](const Eigen::VectorXd &th) -> const Eigen::VectorXd& {
        return lskr_joint_residual(th, t, y, sqrtw);
    };
    LmJacFn jac_fn = [&](const Eigen::VectorXd &x, Eigen::MatrixXd &J) {
        lskr_joint_residual_and_jac(x, t, y, sqrtw, J);
    };
    auto t_lm0 = std::chrono::steady_clock::now();
    LMResult res = levenberg_marquardt_jac(resid, jac_fn, x0, lo, hi, 1e-11, 1e-11, lm_max_iter);
    auto t_lm1 = std::chrono::steady_clock::now();
    auto& prof = lskr_profile_slot();
    double t_lm = std::chrono::duration<double>(t_lm1 - t_lm0).count();
    prof.t_total_lm_other += t_lm - prof.t_total_design - prof.t_total_gains;
    prof.total_lm_iters += 1;
    prof.total_lm_iters_actual += res.iters_used;
    if (res.iters_used > prof.max_lm_iters_actual) prof.max_lm_iters_actual = res.iters_used;
    auto out = lskr_unpack(res.x);
    Eigen::MatrixXd F = lskr_design(t, out);
    Eigen::VectorXd K = lskr_gains(F, y, w);
    for (int l = 0; l < m; ++l) out[l].K = K(l);
    return out;
}

struct LsKrResult { std::vector<LsKrPlanet> planets; int n_detected; };

// Full LS+KR loop, DESIGN.md Section 4, weighted, with a fixed n_planets
// target (see nk_realdata.hpp scope note: this validates recovery of known
// catalog planets rather than performing blind CFAR-thresholded stopping).
// If cfar_tau > 0 is supplied, detection additionally stops early when the
// residual GLS peak falls below it (closer to the literal DESIGN.md loop).
inline LsKrResult lskr_run(const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
                            double P_min, double P_max, int n_planets, int n_grid = 4000,
                            double cfar_tau = -1.0) {
    auto& prof = lskr_profile_slot();
    prof = LsKrProfile{};
    std::vector<LsKrPlanet> pl;
    std::vector<double> claimed;
    Eigen::VectorXd r = y;
    for (int iter = 0; iter < n_planets; ++iter) {
        prof.n_outer_iters++;
        auto t_pg0 = std::chrono::steady_clock::now();
        PeriodogramPeak pk = periodogram_search(t, r, w, P_min, P_max, n_grid, weighted_gls_peak,
                                                 claimed, 0.06);
        prof.t_total_periodogram +=
            std::chrono::duration<double>(std::chrono::steady_clock::now() - t_pg0).count();
        if (cfar_tau > 0 && pk.power < cfar_tau) break;
        claimed.push_back(pk.period);
        LsKrPlanet np{pk.period, 0.0, pk.phi, 0.0, pk.K};
        pl.push_back(np);
        pl = lskr_global_refit(t, y, w, pl);
        claimed.back() = pl.back().P;
        Eigen::MatrixXd F = lskr_design(t, pl);
        Eigen::VectorXd K = lskr_gains(F, y, w);
        r = y - F * K;
    }
    if (std::getenv("NK_LSKR_PROFILE")) prof.print("lskr_run");
    LsKrResult out; out.planets = pl; out.n_detected = (int)pl.size();
    return out;
}

} // namespace nk
