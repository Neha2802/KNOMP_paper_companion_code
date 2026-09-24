// nk_l1periodogram.hpp
//
// C++ port of the l1-periodogram of Hara, Boue, Laskar & Correia 2016
// (MNRAS 464, 1220; the paper's own reference [3], already cited for its
// "Basis Pursuit on RV data" contribution). This is a weighted Basis
// Pursuit Denoising (BPDN) periodogram: discretize a cos/sin dictionary
// over a frequency grid, solve a weighted L1-regularized least squares
// problem to get a sparse amplitude spectrum, smooth it with a moving
// average (the paper's Eq. 18-19), and read off candidate periods exactly
// like the other periodogram-based methods in this project.
//
// SOLVER NOTE: the original paper solves the constrained Basis Pursuit
// Denoising form via SPGL1; the current public l1periodogram code
// (github.com/nathanchara/l1periodogram) instead offers LARS (Efron,
// Hastie, Johnston & Tibshirani 2004) or a Fortran group-lasso routine
// (Yang & Zou 2014). None of these three solvers is a good fit here: LARS
// and SPGL1 are nontrivial to port correctly from scratch in this pass,
// and the dictionary here (up to ~10,000 columns at n_grid=5000) is too
// large for a dense linear solve at every ADMM step. Instead this port
// uses FISTA (Beck & Teboulle 2009), the standard proximal-gradient method
// for the Lagrangian form of the same problem (min 0.5||Ax-y||^2 +
// lambda||x||_1): it needs only matrix-vector products, no factorization,
// and converges at the same solution set as the constrained BPDN form for
// an appropriately chosen lambda (Rockafellar 1970's equivalence, cited in
// the paper itself as justification for using the Lagrangian form
// interchangeably). This is a different solver for the identical convex
// problem, not a different method.
#pragma once
#include <Eigen/Dense>
#include <vector>
#include <cmath>
#include "nk_kepler.hpp"
#include "nk_optimize.hpp"
#include "nk_realdata.hpp"

namespace nk {

// Build the (unweighted) cos/sin dictionary on a log-spaced period grid,
// matching the periodogram grids used elsewhere in this project so the
// l1-periodogram's candidate periods are directly comparable to LS/GLS/
// NOMP/KNOMP's.
inline Eigen::MatrixXd l1_dictionary(const Eigen::VectorXd &t, const std::vector<double> &periods) {
    int n = periods.size();
    Eigen::MatrixXd A(t.size(), 2 * n);
    for (int k = 0; k < n; ++k) {
        double om = 2 * PI / periods[k];
        A.col(2 * k) = (om * t.array()).cos();
        A.col(2 * k + 1) = (om * t.array()).sin();
    }
    return A;
}

struct FistaResult { Eigen::VectorXd x; int iters; };

// FISTA for min_x 0.5||Ax-b||_2^2 + lambda||x||_1. `Lip` is an upper bound
// on the largest eigenvalue of A^T A (power iteration, cheap relative to
// the main loop since it is itself just repeated mat-vecs).
inline double power_iteration_L(const Eigen::MatrixXd &A, int iters = 30) {
    Eigen::VectorXd v = Eigen::VectorXd::Random(A.cols());
    v.normalize();
    double lambda_est = 1.0;
    for (int i = 0; i < iters; ++i) {
        Eigen::VectorXd Av = A * v;
        Eigen::VectorXd AtAv = A.transpose() * Av;
        lambda_est = AtAv.norm();
        if (lambda_est > 1e-300) v = AtAv / lambda_est;
    }
    return lambda_est;
}

inline FistaResult fista_lasso(const Eigen::MatrixXd &A, const Eigen::VectorXd &b,
                                double lambda, int max_iter = 400, double tol = 1e-8) {
    int n = A.cols();
    double L = power_iteration_L(A) * 1.05; // small safety margin
    Eigen::VectorXd x = Eigen::VectorXd::Zero(n), x_prev = x, y = x;
    double t = 1.0;
    auto soft = [](double v, double th) {
        if (v > th) return v - th;
        if (v < -th) return v + th;
        return 0.0;
    };
    for (int k = 0; k < max_iter; ++k) {
        Eigen::VectorXd grad = A.transpose() * (A * y - b);
        Eigen::VectorXd x_new(n);
        for (int i = 0; i < n; ++i) x_new(i) = soft(y(i) - grad(i) / L, lambda / L);
        double t_new = 0.5 * (1.0 + std::sqrt(1.0 + 4 * t * t));
        y = x_new + ((t - 1.0) / t_new) * (x_new - x);
        double rel = (x_new - x).norm() / (x.norm() + 1e-12);
        x = x_new; t = t_new;
        if (rel < tol) return {x, k + 1};
    }
    return {x, max_iter};
}

struct L1PeriodogramResult { double period, K, phi, power; };

// Weighted l1-periodogram (Sec. 2-3 of Hara et al. 2016) on a log-spaced
// period grid, with column normalization (paper Sec. 3.4) and a universal-
// threshold-style lambda (Donoho & Johnstone 1994 form, sigma=1 after
// column normalization and weighting -- a simplification of the paper's
// own chi-square/FAP-calibrated tolerance epsilon of Eq. 15-17, chosen for
// tractability; see notes/REALDATA_SIMPLIFICATIONS.md). Returns the
// smoothed-spectrum peak (paper Eq. 18-19: sum nearby grid coefficients in
// a window of half-width eta, then take the resulting amplitude), matching
// candidates to the same "known" exclusion-zone mechanism used elsewhere.
inline L1PeriodogramResult l1_periodogram_peak(
    const Eigen::VectorXd &t, const Eigen::VectorXd &y, const Eigen::VectorXd &w,
    double P_min, double P_max, int n_grid, const std::vector<double> &exclude = {},
    double exclude_tol = 0.06) {

    std::vector<double> periods(n_grid);
    double lo = std::log(P_min), hi = std::log(P_max);
    for (int i = 0; i < n_grid; ++i) periods[i] = std::exp(lo + (hi - lo) * i / (n_grid - 1));

    Eigen::MatrixXd A = l1_dictionary(t, periods);
    Eigen::VectorXd sqrtw = w.array().sqrt();
    Eigen::MatrixXd Aw = sqrtw.asDiagonal() * A;
    Eigen::VectorXd bw = sqrtw.asDiagonal() * y;

    // Normalize columns to unit norm (paper Sec. 3.4); remember norms to
    // rescale the solution back to physical amplitude units afterward.
    Eigen::VectorXd colnorm(Aw.cols());
    for (int j = 0; j < Aw.cols(); ++j) {
        colnorm(j) = Aw.col(j).norm();
        if (colnorm(j) > 1e-300) Aw.col(j) /= colnorm(j);
    }

    double lambda = std::sqrt(2.0 * std::log(2.0 * n_grid)); // universal threshold, sigma=1
    FistaResult fr = fista_lasso(Aw, bw, lambda, 400, 1e-7);
    Eigen::VectorXd x = fr.x;
    for (int j = 0; j < x.size(); ++j) if (colnorm(j) > 1e-300) x(j) /= colnorm(j);

    // Moving-average smoothing (Eq. 18-19): sum (A,B) over a frequency
    // window of half-width eta = 2*pi/(3*Tobs) around each grid point, then
    // read off the amplitude. Implemented directly on the period grid via
    // an angular-frequency window rather than re-gridding in frequency.
    double Tobs = t(t.size() - 1) - t(0);
    double eta = 2 * PI / (3.0 * Tobs);
    std::vector<double> omega(n_grid);
    for (int i = 0; i < n_grid; ++i) omega[i] = 2 * PI / periods[i];

    double best_power = -1; int best_i = -1; double best_A = 0, best_B = 0;
    for (int i = 0; i < n_grid; ++i) {
        if (!exclude.empty() && in_exclusion_zone(periods[i], exclude, exclude_tol)) continue;
        double sumA = 0, sumB = 0;
        // omega is monotonically decreasing in i (periods increasing), so
        // the window in i is contiguous; find it by linear scan outward
        // from i (grid is smooth/log-spaced so this stays cheap in practice
        // for reasonable n_grid; a binary search would be the production
        // form if this were performance-critical beyond what it already is).
        for (int j = i; j >= 0 && std::fabs(omega[j] - omega[i]) <= eta; --j) {
            sumA += x(2 * j); sumB += x(2 * j + 1);
        }
        for (int j = i + 1; j < n_grid && std::fabs(omega[j] - omega[i]) <= eta; ++j) {
            sumA += x(2 * j); sumB += x(2 * j + 1);
        }
        double amp = std::hypot(sumA, sumB);
        if (amp > best_power) { best_power = amp; best_i = i; best_A = sumA; best_B = sumB; }
    }
    if (best_i < 0) { // whole grid excluded: fall back to unexcluded best
        for (int i = 0; i < n_grid; ++i) {
            double amp = std::hypot(x(2 * i), x(2 * i + 1));
            if (amp > best_power) { best_power = amp; best_i = i; best_A = x(2*i); best_B = x(2*i+1); }
        }
    }
    L1PeriodogramResult out;
    out.period = periods[best_i]; out.K = best_power; out.phi = std::atan2(best_B, best_A);
    out.power = best_power;
    return out;
}

} // namespace nk
