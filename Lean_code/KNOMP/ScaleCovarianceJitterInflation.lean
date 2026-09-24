/-
KNOMP/ScaleCovarianceJitterInflation.lean

Source: Section 18, "Scale-Covariance of the Detection Statistic and Exact
Inflation Under Jitter Misspecification": Lemma `scale-covariance`,
Theorem `jitter-inflation`.

STATUS: PROVED (see README disclaimer).

Strategy note: rather than computing `(c • A)⁻¹` symbolically (which would
need `Matrix.det_smul` plus an adjugate-scaling identity), we characterize
`betaHat X (c•W) y` via the cancellation lemma `eq_inv_mulVec_of_mulVec_eq`
from `Common.lean`: showing `betaHat X W y` already satisfies the
`(c•W)`-weighted normal equations is enough to identify it as
`betaHat X (c•W) y`, since that system has a unique solution. This is
shorter than the paper's own two-line "the two factors of `c` cancel"
argument to state, but proves the identical fact.
-/
import KNOMP.Common

namespace KNOMP

open Matrix

variable {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ)
  (y f : Fin N → ℝ) (c : ℝ)

/-- `XᵀWX` scaled by `c` is invertible whenever the original is and `c ≠ 0`. -/
theorem scaled_XtWX_det_isUnit (hinv : IsUnit (Xᵀ * W * X).det) (hc : c ≠ 0) :
    IsUnit (Xᵀ * (c • W) * X).det := by
  have heq : Xᵀ * (c • W) * X = c • (Xᵀ * W * X) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [heq, Matrix.det_smul, Fintype.card_fin]
  exact (hc.isUnit.pow p).mul hinv

/-- **Lemma `scale-covariance`, `β̂` part.** `β̂(cW) = β̂(W)` for every `c > 0`:
uniform rescaling of the weight matrix leaves the weighted least-squares
fit unchanged. -/
theorem betaHat_scale_invariant (hinv : IsUnit (Xᵀ * W * X).det) (hc : c ≠ 0) :
    betaHat X (c • W) y = betaHat X W y := by
  have hinv' := scaled_XtWX_det_isUnit X W c hinv hc
  have hnorm := normalEq_betaHat X W y hinv
  have hscaled_eq : (Xᵀ * (c • W) * X).mulVec (betaHat X W y) = (Xᵀ * (c • W)).mulVec y := by
    have hL : Xᵀ * (c • W) * X = c • (Xᵀ * W * X) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have hR : Xᵀ * (c • W) = c • (Xᵀ * W) := by
      rw [Matrix.mul_smul]
    rw [hL, hR, Matrix.smul_mulVec, Matrix.smul_mulVec, hnorm]
  have := eq_inv_mulVec_of_mulVec_eq (Xᵀ * (c • W) * X) hinv'
    (betaHat X W y) ((Xᵀ * (c • W)).mulVec y) hscaled_eq
  rw [this]
  unfold betaHat
  rw [Matrix.mulVec_mulVec y Xᵀ (c • W)]

/-- **Lemma `scale-covariance`, residual and `f_perp` parts.** `r(cW) =
r(W)` and `f_perp(cW) = f_perp(W)`. -/
theorem residual_scale_invariant (hinv : IsUnit (Xᵀ * W * X).det) (hc : c ≠ 0) :
    residual X (c • W) y = residual X W y := by
  unfold residual
  rw [betaHat_scale_invariant X W y c hinv hc]

theorem fPerp_scale_invariant (hinv : IsUnit (Xᵀ * W * X).det) (hc : c ≠ 0) :
    fPerp X (c • W) f = fPerp X W f := by
  rw [fPerp_eq_residual, fPerp_eq_residual, residual_scale_invariant X W f c hinv hc]

/-- Pure algebra, isolated so the matrix bookkeeping above never has to
mix with a case split: `(cb)²/(ca) = c(b²/a)` for any real `a, b` and any
`c ≠ 0` (true even when `a = 0`, by Lean/Mathlib's `x / 0 = 0` convention). -/
theorem scale_ratio_identity (c a b : ℝ) (hc : c ≠ 0) :
    (c * b) ^ 2 / (c * a) = c * (b ^ 2 / a) := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  · field_simp

/-- **Lemma `scale-covariance`, main statement.** `ρ_{cW}(f) = c · ρ_W(f)`
exactly, for every `c > 0`. -/
theorem rhoW_scale_covariant (hinv : IsUnit (Xᵀ * W * X).det) (hc : 0 < c) :
    rhoW X (c • W) y f = c * rhoW X W y f := by
  have hc' := ne_of_gt hc
  unfold rhoW weightedSqNorm
  rw [residual_scale_invariant X W y c hinv hc', fPerp_scale_invariant X W f c hinv hc',
      Matrix.smul_mulVec, dotProduct_smul,
      Matrix.smul_mulVec, dotProduct_smul]
  exact scale_ratio_identity c
    (dotProduct (fPerp X W f) (W.mulVec (fPerp X W f)))
    (dotProduct f (W.mulVec (residual X W y))) hc'

/-- **Theorem `jitter-inflation`.** If the model ignores a jitter term that
is the *same* fraction `α` of the nominal variance at every point, the
model's weight is `(1+α)` times the true weight, and hence — by scale
covariance — the jitter-blind detection statistic is inflated by exactly
`(1+α)`, with no distributional assumption on the noise. -/
theorem jitter_inflation
    (Wtrue Wmodel : Matrix (Fin N) (Fin N) ℝ) (α : ℝ) (hα : 0 < 1 + α)
    (hW : Wmodel = (1 + α) • Wtrue)
    (hinv : IsUnit (Xᵀ * Wtrue * X).det) :
    rhoW X Wmodel y f = (1 + α) * rhoW X Wtrue y f := by
  rw [hW]
  exact rhoW_scale_covariant X Wtrue y f (1 + α) hinv hα

end KNOMP
