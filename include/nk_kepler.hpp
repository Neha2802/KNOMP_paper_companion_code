// nk_kepler.hpp
// Kepler's equation solver (Danby-Halley, matches lib/kepler.py exactly in
// formula), the Keplerian RV atom, and its exact analytic partial
// derivatives (Lemma 4.1 of the paper). Header-only for simplicity.
#pragma once
#include <cmath>
#include <vector>
#include <Eigen/Dense>

namespace nk {

constexpr double PI = 3.14159265358979323846;

// Solve M = E - e*sin(E) for E. Danby-Burkardt starting guess + safeguarded
// Halley (cubic) iteration -- robust up to e ~ 0.999, matches
// lib/kepler.py::solve_kepler exactly in method and tolerance.
inline double solve_kepler(double M, double e, int iters = 100, double tol = 1e-14) {
    double Mm = std::fmod(M + PI, 2 * PI) - PI;
    if (Mm < -PI) Mm += 2 * PI;
    double E = Mm + (std::sin(Mm) >= 0 ? 1.0 : -1.0) * 0.85 * e;
    for (int i = 0; i < iters; ++i) {
        double sE = std::sin(E), cE = std::cos(E);
        double f = E - e * sE - Mm;
        double fp = 1 - e * cE;
        double fpp = e * sE;
        double fppp = e * cE;
        double d1 = -f / fp;
        double d2 = -f / (fp + 0.5 * d1 * fpp);
        double d3 = -f / (fp + 0.5 * d2 * fpp + (1.0 / 6.0) * d2 * d2 * fppp);
        E += d3;
        if (std::fabs(d3) < tol) break;
    }
    return E + (M - Mm);
}

inline void true_anomaly(double M, double e, double &nu, double &E) {
    E = solve_kepler(M, e);
    nu = 2 * std::atan2(std::sqrt(1 + e) * std::sin(E / 2), std::sqrt(1 - e) * std::cos(E / 2));
}

inline double dnu_dM(double E, double e) {
    double d = 1 - e * std::cos(E);
    return std::sqrt(1 - e * e) / (d * d);
}

inline double dnu_de(double E, double e) {
    double s = std::sin(E);
    double d = 1 - e * std::cos(E);
    return s * (2 - e * e - e * std::cos(E)) / (std::sqrt(1 - e * e) * d * d);
}

inline double mean_anomaly(double t, double P, double M0, double t_ref = 0.0) {
    double n = 2 * PI / P;
    return M0 + n * (t - t_ref);
}

// Unit-amplitude Keplerian RV atom, Eq. (1).
inline double f_signal(double t, double P, double e, double omega, double M0, double t_ref = 0.0) {
    double M = mean_anomaly(t, P, M0, t_ref);
    double nu, E;
    true_anomaly(M, e, nu, E);
    return std::cos(nu + omega) + e * std::cos(omega);
}

inline Eigen::VectorXd f_signal_vec(const Eigen::VectorXd &t, double P, double e, double omega,
                                     double M0, double t_ref = 0.0) {
    Eigen::VectorXd out(t.size());
    for (int i = 0; i < t.size(); ++i) out(i) = f_signal(t(i), P, e, omega, M0, t_ref);
    return out;
}

// Same as f_signal_vec but writes into a pre-allocated raw buffer. No
// allocation, no Eigen expression-template overhead. Used in the LSKR
// residual hot path where this function is called m times per residual
// evaluation, and a full LSKR run on HD10180 issues ~45K residual evals.
inline void f_signal_vec_into(double* __restrict__ out, const Eigen::VectorXd &t,
                              double P, double e, double omega, double M0,
                              double t_ref = 0.0) {
    const int n = (int)t.size();
    const double* __restrict__ tp = t.data();
    const double n_per = 2 * PI / P;
    for (int i = 0; i < n; ++i) {
        const double M = M0 + n_per * (tp[i] - t_ref);
        double nu, E;
        true_anomaly(M, e, nu, E);
        out[i] = std::cos(nu + omega) + e * std::cos(omega);
    }
}

struct KeplerianPartials {
    double f, dK, dP, de, domega, dM0, nu, E;
};

// Exact Jacobian of mu(t)=K*f(t;P,e,omega,M0) w.r.t. (K,P,e,omega,M0), Lemma 4.1.
inline KeplerianPartials keplerian_partials(double t, double P, double e, double omega, double M0,
                                             double K = 1.0, double t_ref = 0.0) {
    double n = 2 * PI / P;
    double M = M0 + n * (t - t_ref);
    double nu, E;
    true_anomaly(M, e, nu, E);
    double s_nu = std::sin(nu + omega);
    double dnu_dM_v = dnu_dM(E, e);
    double dnu_de_v = dnu_de(E, e);

    KeplerianPartials out;
    out.f = std::cos(nu + omega) + e * std::cos(omega);
    out.nu = nu; out.E = E;
    out.dK = out.f;
    out.dM0 = -K * s_nu * dnu_dM_v;
    out.dP = K * s_nu * dnu_dM_v * (M - M0) / P;
    out.domega = K * (-s_nu - e * std::sin(omega));
    out.de = K * (-s_nu * dnu_de_v + std::cos(omega));
    return out;
}

// Fills four n_obs buffers with the partials of f_atom(t; P, e, omega, M0)
// w.r.t. (P, e, omega, M0). All four partials share the same Kepler's-equation
// solve per epoch -- the inner loop reuses E, nu, sin(nu+omega), dnu_dM,
// dnu_de across the four derivative computations. Caller-allocated buffers
// (no Eigen allocation). Used by the LSKR analytic-Jacobian path.
inline void keplerian_partials_vec_into(double* __restrict__ out_dP,
                                         double* __restrict__ out_de,
                                         double* __restrict__ out_domega,
                                         double* __restrict__ out_dM0,
                                         const Eigen::VectorXd &t,
                                         double P, double e, double omega, double M0,
                                         double t_ref = 0.0) {
    const int n = (int)t.size();
    const double* __restrict__ tp = t.data();
    const double n_per = 2 * PI / P;
    const double sqrt_1me2 = std::sqrt(1 - e * e);
    const double cos_omega = std::cos(omega);
    const double sin_omega = std::sin(omega);
    for (int i = 0; i < n; ++i) {
        const double M = M0 + n_per * (tp[i] - t_ref);
        // Mirror solve_kepler exactly so the partials match what
        // keplerian_partials() would produce point-by-point.
        double Mm = std::fmod(M + PI, 2 * PI) - PI;
        if (Mm < -PI) Mm += 2 * PI;
        double E = Mm + (std::sin(Mm) >= 0 ? 1.0 : -1.0) * 0.85 * e;
        for (int it = 0; it < 100; ++it) {
            const double sE = std::sin(E), cE = std::cos(E);
            const double f  = E - e * sE - Mm;
            const double fp = 1 - e * cE;
            const double fpp = e * sE;
            const double fppp = e * cE;
            const double d1 = -f / fp;
            const double d2 = -f / (fp + 0.5 * d1 * fpp);
            const double d3 = -f / (fp + 0.5 * d2 * fpp + (1.0 / 6.0) * d2 * d2 * fppp);
            E += d3;
            if (std::fabs(d3) < 1e-14) break;
        }
        E += (M - Mm);
        const double nu = 2 * std::atan2(std::sqrt(1 + e) * std::sin(E / 2),
                                          std::sqrt(1 - e) * std::cos(E / 2));
        const double cn = std::cos(nu), sn = std::sin(nu);
        const double sin_nu_plus_omega = sn * cos_omega + cn * sin_omega;
        const double d1_minus_e_cE = 1 - e * std::cos(E);
        const double dnu_dM_v = sqrt_1me2 / (d1_minus_e_cE * d1_minus_e_cE);
        const double dnu_de_v = std::sin(E) * (2 - e * e - e * std::cos(E))
                              / (sqrt_1me2 * d1_minus_e_cE * d1_minus_e_cE);
        out_dP[i]     = sin_nu_plus_omega * dnu_dM_v * (M - M0) / P;
        out_de[i]     = -sin_nu_plus_omega * dnu_de_v + cos_omega;
        out_domega[i] = -sin_nu_plus_omega - e * sin_omega;
        out_dM0[i]    = -sin_nu_plus_omega * dnu_dM_v;
    }
}

// Fills (f, df/dP, df/de, df/domega, df/dM0) in a SINGLE kepler-solve pass
// per epoch. Combines f_signal_vec_into + keplerian_partials_vec_into so
// that the design matrix F and its per-atom Jacobian partials are computed
// together. Halves the kepler-solve work in the analytic-J hot path -- the
// residual-call that previously did m `f_signal_vec_into` + m
// `keplerian_partials_vec_into` now does only m `f_and_partials_into`
// calls, each ~1 kepler solve per epoch instead of 2.
inline void f_and_partials_into(double* __restrict__ out_f,
                                 double* __restrict__ out_dP,
                                 double* __restrict__ out_de,
                                 double* __restrict__ out_domega,
                                 double* __restrict__ out_dM0,
                                 const Eigen::VectorXd &t,
                                 double P, double e, double omega, double M0,
                                 double t_ref = 0.0) {
    const int n = (int)t.size();
    const double* __restrict__ tp = t.data();
    const double n_per = 2 * PI / P;
    const double sqrt_1me2 = std::sqrt(1 - e * e);
    const double sqrt_1pe = std::sqrt(1 + e);
    const double sqrt_1me = std::sqrt(1 - e);
    const double cos_omega = std::cos(omega);
    const double sin_omega = std::sin(omega);
    const double e_cos_omega = e * cos_omega;
    for (int i = 0; i < n; ++i) {
        const double M = M0 + n_per * (tp[i] - t_ref);
        double Mm = std::fmod(M + PI, 2 * PI) - PI;
        if (Mm < -PI) Mm += 2 * PI;
        double E = Mm + (std::sin(Mm) >= 0 ? 1.0 : -1.0) * 0.85 * e;
        for (int it = 0; it < 100; ++it) {
            const double sE = std::sin(E), cE = std::cos(E);
            const double f  = E - e * sE - Mm;
            const double fp = 1 - e * cE;
            const double fpp = e * sE;
            const double fppp = e * cE;
            const double d1 = -f / fp;
            const double d2 = -f / (fp + 0.5 * d1 * fpp);
            const double d3 = -f / (fp + 0.5 * d2 * fpp + (1.0 / 6.0) * d2 * d2 * fppp);
            E += d3;
            if (std::fabs(d3) < 1e-14) break;
        }
        E += (M - Mm);
        const double sin_half_E = std::sin(E / 2);
        const double cos_half_E = std::cos(E / 2);
        const double nu = 2 * std::atan2(sqrt_1pe * sin_half_E,
                                          sqrt_1me * cos_half_E);
        const double cn = std::cos(nu), sn = std::sin(nu);
        const double sin_nu_plus_omega = sn * cos_omega + cn * sin_omega;
        const double f_atom = cn + e_cos_omega;   // cos(nu + omega) + e cos(omega)
        const double d1_minus_e_cE = 1 - e * std::cos(E);
        const double dnu_dM_v = sqrt_1me2 / (d1_minus_e_cE * d1_minus_e_cE);
        const double dnu_de_v = std::sin(E) * (2 - e * e - e * std::cos(E))
                              / (sqrt_1me2 * d1_minus_e_cE * d1_minus_e_cE);
        out_f[i]       = f_atom;
        out_dP[i]      = sin_nu_plus_omega * dnu_dM_v * (M - M0) / P;
        out_de[i]      = -sin_nu_plus_omega * dnu_de_v + cos_omega;
        out_domega[i]  = -sin_nu_plus_omega - e * sin_omega;
        out_dM0[i]     = -sin_nu_plus_omega * dnu_dM_v;
    }
}

} // namespace nk
