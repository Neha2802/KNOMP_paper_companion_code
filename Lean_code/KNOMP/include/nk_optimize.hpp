// nk_optimize.hpp
// Generic optimizers used throughout: Brent's method for bounded scalar
// minimization (matches scipy.optimize.minimize_scalar(method='bounded')),
// and a bounded (projected) Levenberg-Marquardt solver for small nonlinear
// least-squares problems (matches the converged optimum of
// scipy.optimize.least_squares(method='trf') for these well-conditioned,
// good-initial-guess problems, though the iterative path differs).
#pragma once
#include <functional>
#include <cmath>
#include <algorithm>
#include <Eigen/Dense>

namespace nk {

// Brent's method for bounded 1D minimization of f over [lo,hi].
// Standard algorithm (golden-section + parabolic interpolation).
inline double brent_bounded(const std::function<double(double)> &f, double lo, double hi,
                             double xatol = 1e-8, int max_iter = 200) {
    const double golden = 0.3819660112501051;
    double a = lo, b = hi;
    double x = a + golden * (b - a), w = x, v = x;
    double fx = f(x), fw = fx, fv = fx;
    double d = 0.0, e = 0.0;

    for (int iter = 0; iter < max_iter; ++iter) {
        double m = 0.5 * (a + b);
        double tol1 = xatol * std::fabs(x) + 1e-12;
        double tol2 = 2 * tol1;
        if (std::fabs(x - m) <= tol2 - 0.5 * (b - a)) break;

        bool use_golden = true;
        if (std::fabs(e) > tol1) {
            double r = (x - w) * (fx - fv);
            double q = (x - v) * (fx - fw);
            double p = (x - v) * q - (x - w) * r;
            q = 2 * (q - r);
            if (q > 0) p = -p;
            q = std::fabs(q);
            double etemp = e;
            e = d;
            if (std::fabs(p) < std::fabs(0.5 * q * etemp) && p > q * (a - x) && p < q * (b - x)) {
                d = p / q;
                double u = x + d;
                if (u - a < tol2 || b - u < tol2) d = (m - x >= 0) ? tol1 : -tol1;
                use_golden = false;
            }
        }
        if (use_golden) {
            e = (x >= m) ? (a - x) : (b - x);
            d = golden * e;
        }
        double u = (std::fabs(d) >= tol1) ? (x + d) : (x + (d >= 0 ? tol1 : -tol1));
        double fu = f(u);
        if (fu <= fx) {
            if (u >= x) a = x; else b = x;
            v = w; fv = fw; w = x; fw = fx; x = u; fx = fu;
        } else {
            if (u < x) a = u; else b = u;
            if (fu <= fw || w == x) { v = w; fv = fw; w = u; fw = fu; }
            else if (fu <= fv || v == x || v == w) { v = u; fv = fu; }
        }
    }
    return x;
}

// Bounded (projected) Levenberg-Marquardt for small nonlinear least-squares:
// minimize ||r(x)||^2 subject to lo <= x <= hi. Central finite-difference
// Jacobian. Converges to the same local optimum as scipy's TRF for these
// well-behaved, good-initial-guess bracketed problems.
struct LMResult {
    Eigen::VectorXd x;
    double cost;
    int nfev;
    int iters_used = 0;
};

inline LMResult levenberg_marquardt_bounded(
    const std::function<const Eigen::VectorXd&(const Eigen::VectorXd &)> &residual_fn,
    Eigen::VectorXd x0, const Eigen::VectorXd &lo, const Eigen::VectorXd &hi,
    double xtol = 1e-12, double ftol = 1e-12, int max_iter = 200) {

    int n = x0.size();
    for (int i = 0; i < n; ++i) x0(i) = std::min(std::max(x0(i), lo(i)), hi(i));

    Eigen::VectorXd x = x0;
    Eigen::VectorXd r = residual_fn(x);
    double cost = r.squaredNorm();
    double lambda = 1e-3;
    int nfev = 1;
    int lm_iters_used = 0;

    for (int iter = 0; iter < max_iter; ++iter) {
        lm_iters_used++;
        // finite-difference Jacobian. NB: residual_fn may write into a
        // thread-local scratch buffer that gets overwritten on each call
        // (see nk_lskr.hpp::lskr_joint_residual). We therefore do NOT keep
        // a const-ref to any residual output across residual_fn calls;
        // each result is copied out into a local Eigen::VectorXd before
        // the next call overwrites the scratch.
        Eigen::MatrixXd J(r.size(), n);
        Eigen::VectorXd r_for_Jtr = r;   // snapshot before FD overwrites scratch
        for (int j = 0; j < n; ++j) {
            double h = std::max(1e-7, 1e-7 * std::fabs(x(j)));
            Eigen::VectorXd xp = x, xm = x;
            xp(j) = std::min(xp(j) + h, hi(j));
            xm(j) = std::max(xm(j) - h, lo(j));
            double denom = xp(j) - xm(j);
            if (denom <= 0) { J.col(j).setZero(); continue; }
            Eigen::VectorXd rp = residual_fn(xp);  // copy out (scratch will be reused)
            Eigen::VectorXd rm = residual_fn(xm);  // copy out
            J.col(j) = (rp - rm) / denom;
            nfev += 2;
        }

        Eigen::MatrixXd JtJ = J.transpose() * J;
        Eigen::VectorXd Jtr = J.transpose() * r_for_Jtr;
        bool improved = false;

        for (int tries = 0; tries < 20; ++tries) {
            Eigen::MatrixXd A = JtJ;
            for (int d = 0; d < n; ++d) A(d, d) += lambda * std::max(JtJ(d, d), 1e-12);
            Eigen::VectorXd delta = A.ldlt().solve(-Jtr);
            Eigen::VectorXd x_new = x + delta;
            for (int i = 0; i < n; ++i) x_new(i) = std::min(std::max(x_new(i), lo(i)), hi(i));

            Eigen::VectorXd r_new = residual_fn(x_new);  // copy out
            nfev++;
            double cost_new = r_new.squaredNorm();

            if (cost_new < cost) {
                double rel_step = (x_new - x).norm() / (x.norm() + 1e-12);
                double rel_cost = std::fabs(cost - cost_new) / (cost + 1e-12);
                x = x_new; r = r_new; cost = cost_new;
                lambda = std::max(lambda * 0.5, 1e-12);
                improved = true;
                if (rel_step < xtol || rel_cost < ftol) {
                    LMResult res{x, cost, nfev};
                    res.iters_used = lm_iters_used;
                    return res;
                }
                break;
            } else {
                lambda *= 3.0;
            }
        }
        if (!improved) break;
    }
    LMResult res{x, cost, nfev};
    res.iters_used = lm_iters_used;
    return res;
}

// Bounded Levenberg-Marquardt with a user-supplied analytic Jacobian.
// Mathematically equivalent to the FD version above when the analytic
// Jacobian is exact (the FD version converges to the same optimum, since
// it computes the same J^T J + lambda*I normal equations, just with J from
// finite differences instead of analytic derivatives). Behaviour-preserving
// optimization: same trust-region update, same convergence tests, same
// lambda initialization, same trial-step acceptance. The only difference
// is how J is computed -- one function call vs 2*n residual evaluations.
//
// Signature:
//   residual_fn(x)              -> const VectorXd&  (the residual vector)
//   jacobian_fn(x, J_out)       -> void              (fills J_out in place,
//                                                     shape n_residual x n_x)
inline LMResult levenberg_marquardt_jac(
    const std::function<const Eigen::VectorXd&(const Eigen::VectorXd &)> &residual_fn,
    const std::function<void(const Eigen::VectorXd &, Eigen::MatrixXd &)> &jacobian_fn,
    Eigen::VectorXd x0, const Eigen::VectorXd &lo, const Eigen::VectorXd &hi,
    double xtol = 1e-12, double ftol = 1e-12, int max_iter = 200) {

    int n = x0.size();
    for (int i = 0; i < n; ++i) x0(i) = std::min(std::max(x0(i), lo(i)), hi(i));

    Eigen::VectorXd x = x0;
    Eigen::VectorXd r = residual_fn(x);
    int n_res = (int)r.size();
    double cost = r.squaredNorm();
    double lambda = 1e-3;
    int nfev = 1;
    int lm_iters_used = 0;

    Eigen::MatrixXd J(n_res, n);
    Eigen::VectorXd r_for_Jtr = r;

    for (int iter = 0; iter < max_iter; ++iter) {
        lm_iters_used++;
        jacobian_fn(x, J);

        Eigen::MatrixXd JtJ = J.transpose() * J;
        Eigen::VectorXd Jtr = J.transpose() * r_for_Jtr;
        bool improved = false;

        for (int tries = 0; tries < 20; ++tries) {
            Eigen::MatrixXd A = JtJ;
            for (int d = 0; d < n; ++d) A(d, d) += lambda * std::max(JtJ(d, d), 1e-12);
            Eigen::VectorXd delta = A.ldlt().solve(-Jtr);
            Eigen::VectorXd x_new = x + delta;
            for (int i = 0; i < n; ++i) x_new(i) = std::min(std::max(x_new(i), lo(i)), hi(i));

            Eigen::VectorXd r_new = residual_fn(x_new);
            nfev++;
            double cost_new = r_new.squaredNorm();

            if (cost_new < cost) {
                double rel_step = (x_new - x).norm() / (x.norm() + 1e-12);
                double rel_cost = std::fabs(cost - cost_new) / (cost + 1e-12);
                x = x_new; r = r_new; r_for_Jtr = r_new; cost = cost_new;
                lambda = std::max(lambda * 0.5, 1e-12);
                improved = true;
                if (rel_step < xtol || rel_cost < ftol) {
                    LMResult res{x, cost, nfev};
                    res.iters_used = lm_iters_used;
                    return res;
                }
                break;
            } else {
                lambda *= 3.0;
            }
        }
        if (!improved) break;
    }
    LMResult res{x, cost, nfev};
    res.iters_used = lm_iters_used;
    return res;
}

} // namespace nk
