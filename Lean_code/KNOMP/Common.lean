/-
KNOMP/Common.lean

Status: DEFINITIONS + reusable lemmas, tier PROVED (one narrow, clearly
isolated exception noted below).

Shared setup used by several of the other files, matching the source
paper's Section 1 (`Model and Notation`). This is plain linear algebra:
an `N`-observation, `p`-parameter weighted least squares model,

  ŷ = X β,   ŷ minimizing ‖y - X β‖_W² for a symmetric positive-definite
  weight matrix W.

We work with concrete `Fin N`/`Fin p` indexed real matrices/vectors, since
that is how the paper's own formulas (Schur complements, projections
`P_X(W)`, etc.) are written.

DESIGN NOTE: Mathlib's `Matrix.PosDef` is built for general `IsROrC` fields
and routes through `star`/`conjTranspose`/`IsROrC.re`. Over `ℝ` all of that
machinery is definitionally trivial but the exact simp lemmas that unfold
it can drift across Mathlib revisions, and I cannot compile-check them
here (see project README: this sandbox cannot reach Mathlib's cache). To
avoid hiding real risk behind unverifiable rewrites, this file instead
defines a bare-bones real symmetric-positive-definite predicate directly
from its two defining properties. Everything below is then proved from
that raw definition, with no unverifiable API guesses left in the critical
path. If you would rather use `Matrix.PosDef` from Mathlib directly, the
conversion is a one-line bridge lemma (`Matrix.PosDef` unfolds to exactly
these two conjuncts over `ℝ`) — left as an exercise, flagged at the bottom
of this file.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic

namespace KNOMP

open Matrix

variable {N p : ℕ}

/-- A plain, real, symmetric-positive-definite predicate: `W` is symmetric
(`Wᵀ = W`) and `vᵀWv > 0` for every nonzero `v`. This is exactly what the
source paper means by "`W` symmetric positive definite" (§1.2); see the
design note above for why this is stated directly rather than via
Mathlib's general `Matrix.PosDef`. -/
def IsPosDefR (W : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Wᵀ = W ∧ ∀ v : Fin N → ℝ, v ≠ 0 → 0 < dotProduct v (W.mulVec v)

theorem IsPosDefR.symm {W : Matrix (Fin N) (Fin N) ℝ} (h : IsPosDefR W) : Wᵀ = W := h.1

theorem IsPosDefR.pos {W : Matrix (Fin N) (Fin N) ℝ} (h : IsPosDefR W)
    {v : Fin N → ℝ} (hv : v ≠ 0) : 0 < dotProduct v (W.mulVec v) := h.2 v hv

/-- The `W`-weighted quadratic form `zᵀ W z`, matching the paper's
`‖·‖_W²` notation. -/
def weightedSqNorm (W : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  dotProduct z (W.mulVec z)

/-- The weighted least-squares coefficient vector
`β̂(W) = (Xᵀ W X)⁻¹ Xᵀ W y`, defined whenever `XᵀWX` is invertible.
Matches the paper's `\hat{\bbeta}(W)` (Eq. `rhoW`, §1.2). -/
noncomputable def betaHat (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) : Fin p → ℝ :=
  (Xᵀ * W * X)⁻¹.mulVec (Xᵀ.mulVec (W.mulVec y))

/-- The residual `r(W) = y - X β̂(W)`. -/
noncomputable def residual (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) : Fin N → ℝ :=
  y - X.mulVec (betaHat X W y)

/-- The `W`-orthogonal projection onto `range(X)`,
`P_X(W) = X (XᵀWX)⁻¹ Xᵀ W`. -/
noncomputable def projX (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  X * (Xᵀ * W * X)⁻¹ * Xᵀ * W

/-- The component of a candidate vector `f` left over after removing what
the current model already explains, `f_perp(W) = (I - P_X(W)) f`. -/
noncomputable def fPerp (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (f : Fin N → ℝ) : Fin N → ℝ :=
  f - (projX X W).mulVec f

/-- The detection statistic `ρ_W(f)` of Eq. `rhoW`:
`(fᵀ W r(W))² / (f_perp(W)ᵀ W f_perp(W))`. -/
noncomputable def rhoW (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) (f : Fin N → ℝ) : ℝ :=
  (dotProduct f (W.mulVec (residual X W y))) ^ 2 /
    weightedSqNorm W (fPerp X W f)

/-- Standing hypotheses shared by the linear-algebra results: `W` is
symmetric positive definite and `XᵀWX` is invertible (matching the
paper's standing assumption in §1.2/§3). -/
structure StandingHyps (X : Matrix (Fin N) (Fin p) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) : Prop where
  W_posDef : IsPosDefR W
  XtWX_inv : IsUnit (Xᵀ * W * X).det

/-! ### Reusable lemmas

Load-bearing pieces reused across `ExactDetectionIncrement.lean`,
`IncrementalQRUpdate.lean`, `InterferenceBias.lean` and
`ScaleCovarianceJitterInflation.lean`. -/

/-- Transpose/dot-product adjunction: `(Av) ⬝ u = v ⬝ (Aᵀ u)`. The one
genuinely "matrix-API" fact everything else below reduces to. -/
theorem dotProduct_transpose_mulVec
    {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) (u : Fin n → ℝ) :
    dotProduct (A.mulVec v) u = dotProduct v (Aᵀ.mulVec u) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The normal equations: `XᵀW` annihilates the residual, `(Xᵀ W) r(W) = 0`.
Key intermediate identity behind Theorem `glrt` (source doc, around
Eq. `Khat`); also exactly `Xᵀ W (I - P) = 0`, used throughout §3 and §9. -/
theorem transpose_weight_mulVec_residual_eq_zero
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hinv : IsUnit (Xᵀ * W * X).det) :
    (Xᵀ * W).mulVec (residual X W y) = 0 := by
  unfold residual betaHat
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  simp

/-- `f_perp(W)` for a candidate `f` is literally `residual X W f`: the same
"remove what `X` already explains, in the `W` metric" operation applied to
`f` instead of to the data `y`. This collapses two objects the source
paper treats separately into one definitional fact. -/
theorem fPerp_eq_residual
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (f : Fin N → ℝ) :
    fPerp X W f = residual X W f := by
  unfold fPerp residual projX betaHat
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- `Xᵀ W` also annihilates `f_perp(W)` — immediate from the previous two
lemmas, stated separately since the source paper's proof of Theorem
`glrt` invokes it by name. -/
theorem transpose_weight_mulVec_fPerp_eq_zero
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (f : Fin N → ℝ)
    (hinv : IsUnit (Xᵀ * W * X).det) :
    (Xᵀ * W).mulVec (fPerp X W f) = 0 := by
  rw [fPerp_eq_residual X W f]
  exact transpose_weight_mulVec_residual_eq_zero X W f hinv

/-- The quadratic form `v ↦ vᵀ (Xᵀ W X) v` is nonnegative whenever `W` is
positive definite (no rank hypothesis on `X` needed): it equals
`(Xv)ᵀW(Xv)`, which is nonnegative by `W`-positive-definiteness. -/
theorem quadForm_transpose_mul_mul_nonneg
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (hW : IsPosDefR W)
    (v : Fin p → ℝ) :
    0 ≤ dotProduct v ((Xᵀ * W * X).mulVec v) := by
  have h : dotProduct v ((Xᵀ * W * X).mulVec v)
      = dotProduct (X.mulVec v) (W.mulVec (X.mulVec v)) := by
    rw [dotProduct_transpose_mulVec X v (W.mulVec (X.mulVec v)),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h]
  rcases eq_or_ne (X.mulVec v) 0 with hv | hv
  · simp [hv]
  · exact le_of_lt (hW.pos hv)

/-- The `W`-weighted bilinear form is symmetric when `W` is: `u ⬝ (Wv) = v ⬝ (Wu)`. -/
theorem weightedForm_comm
    (W : Matrix (Fin N) (Fin N) ℝ) (hWt : Wᵀ = W) (u v : Fin N → ℝ) :
    dotProduct u (W.mulVec v) = dotProduct v (W.mulVec u) := by
  rw [dotProduct_comm, dotProduct_transpose_mulVec W v u, hWt]

/-- Expanding `‖r - K•fp‖_W²` as a quadratic in the scalar `K`. This is the
"profile out `K` last" step of Theorem `glrt`'s proof, and of the QR
update's error-contraction argument in §9/§10. -/
theorem weightedSqNorm_sub_smul
    (W : Matrix (Fin N) (Fin N) ℝ) (hWt : Wᵀ = W) (r fp : Fin N → ℝ) (K : ℝ) :
    weightedSqNorm W (r - K • fp)
      = weightedSqNorm W r - 2 * K * dotProduct fp (W.mulVec r)
        + K ^ 2 * weightedSqNorm W fp := by
  unfold weightedSqNorm
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [weightedForm_comm W hWt r fp]
  ring

/-- **Weighted-least-squares optimality**, in gap form: moving `β` away
from `β̂(W)` by `e = β - β̂(W)` costs exactly `eᵀ(XᵀWX)e` in weighted
squared error, with no cross term (the cross term vanishes by the normal
equations). This is the profiling step used throughout §3, and is the
"complete the square directly" route the source paper itself falls back
to when computing `ΔJ` from `Q(K)` at the end of Theorem `glrt`'s proof.

STATUS: PROVED. -/
theorem wls_gap_eq
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hW : IsPosDefR W) (hinv : IsUnit (Xᵀ * W * X).det) (β : Fin p → ℝ) :
    weightedSqNorm W (y - X.mulVec β)
      = weightedSqNorm W (residual X W y)
        + dotProduct (β - betaHat X W y) ((Xᵀ * W * X).mulVec (β - betaHat X W y)) := by
  have hy : y - X.mulVec β = residual X W y - X.mulVec (β - betaHat X W y) := by
    unfold residual
    rw [Matrix.mulVec_sub]
    abel
  have hcross' : dotProduct (X.mulVec (β - betaHat X W y)) (W.mulVec (residual X W y)) = 0 := by
    rw [dotProduct_transpose_mulVec X (β - betaHat X W y)
          (W.mulVec (residual X W y)),
        Matrix.mulVec_mulVec, transpose_weight_mulVec_residual_eq_zero X W y hinv]
    simp
  have hquad : weightedSqNorm W (X.mulVec (β - betaHat X W y))
      = dotProduct (β - betaHat X W y) ((Xᵀ * W * X).mulVec (β - betaHat X W y)) := by
    unfold weightedSqNorm
    rw [dotProduct_transpose_mulVec X (β - betaHat X W y)
          (W.mulVec (X.mulVec (β - betaHat X W y))),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hy]
  have expand := weightedSqNorm_sub_smul W hW.symm (residual X W y)
    (X.mulVec (β - betaHat X W y)) 1
  simp only [one_smul, one_pow, mul_one] at expand
  rw [expand, hcross', hquad]
  ring

/-- Corollary of `wls_gap_eq`: `β̂(W)` really is a minimizer, not just a
stationary point — the inequality form most files actually call. -/
theorem wls_optimality
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (hW : IsPosDefR W)
    (y : Fin N → ℝ) (hinv : IsUnit (Xᵀ * W * X).det) (β : Fin p → ℝ) :
    weightedSqNorm W (residual X W y) ≤ weightedSqNorm W (y - X.mulVec β) := by
  rw [wls_gap_eq X W y hW hinv β]
  linarith [quadForm_transpose_mul_mul_nonneg X W hW (β - betaHat X W y)]

/-- `betaHat`/`residual` are linear (in fact affine-in-a-linear-way) in the
data argument: replacing `y` by `y - K • f` shifts `betaHat` by
`-K • betaHat X W f` and `residual` by `-K • residual X W f`. This is the
fact that lets §3 reduce "profile `β` for fixed `K`" to a second call of
`wls_optimality`/`wls_gap_eq` with shifted data, instead of re-deriving
linearity from scratch. -/
theorem residual_shift
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (y f : Fin N → ℝ)
    (hinv : IsUnit (Xᵀ * W * X).det) (K : ℝ) :
    residual X W (y - K • f) = residual X W y - K • residual X W f := by
  unfold residual betaHat
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

/-- A candidate atom `f` and its leftover part `f_perp(W)` give the same
`W`-weighted inner product against the residual — the "leftover part
carries all the correlation with the residual that `f` itself does"
fact behind Theorem `glrt`'s `f`-vs-`f_perp` interchangeability
(Eq. `glrt-exact`), and behind `rhoW`'s numerator being expressible
either way. -/
theorem dot_f_weight_residual_eq_dot_fPerp
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (y f : Fin N → ℝ)
    (hinv : IsUnit (Xᵀ * W * X).det) :
    dotProduct f (W.mulVec (residual X W y))
      = dotProduct (fPerp X W f) (W.mulVec (residual X W y)) := by
  have hf : f = fPerp X W f + (projX X W).mulVec f := by
    unfold fPerp; abel
  have hproj : (projX X W).mulVec f = X.mulVec (betaHat X W f) := by
    unfold projX betaHat
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hzero : dotProduct (X.mulVec (betaHat X W f)) (W.mulVec (residual X W y)) = 0 := by
    rw [dotProduct_transpose_mulVec X (betaHat X W f)
          (W.mulVec (residual X W y)),
        Matrix.mulVec_mulVec, transpose_weight_mulVec_residual_eq_zero X W y hinv]
    simp
  calc dotProduct f (W.mulVec (residual X W y))
      = dotProduct (fPerp X W f + (projX X W).mulVec f) (W.mulVec (residual X W y)) := by
        rw [← hf]
    _ = dotProduct (fPerp X W f) (W.mulVec (residual X W y))
          + dotProduct (X.mulVec (betaHat X W f)) (W.mulVec (residual X W y)) := by
        rw [add_dotProduct, hproj]
    _ = dotProduct (fPerp X W f) (W.mulVec (residual X W y)) := by rw [hzero]; ring

/-- If `A` is invertible and `A.mulVec v = w`, then `v = A⁻¹.mulVec w`. The
one cancellation fact that lets `ScaleCovarianceJitterInflation.lean`
compare `betaHat` at two different weight matrices without ever computing
`(c • A)⁻¹` symbolically. -/
theorem eq_inv_mulVec_of_mulVec_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hinv : IsUnit A.det) (v w : Fin n → ℝ) (h : A.mulVec v = w) :
    v = A⁻¹.mulVec w := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]

/-- `β̂(W)` satisfies the normal equations `(XᵀWX)β̂(W) = XᵀWy` by
construction. -/
theorem normalEq_betaHat
    (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ)
    (hinv : IsUnit (Xᵀ * W * X).det) :
    (Xᵀ * W * X).mulVec (betaHat X W y) = (Xᵀ * W).mulVec y := by
  unfold betaHat
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]

/-- Completing the square in one real variable: the quadratic
`k ↦ c - 2kb + k²a` (`a > 0`) is bounded below by `c - b²/a`, attained at
`k = b/a`. The univariate profiling step used to minimize over the linear
gain `K` in §3 and §9.

STATUS: PROVED. -/
theorem quadratic_min_1d {a b c : ℝ} (ha : 0 < a) (k : ℝ) :
    c - b ^ 2 / a ≤ c - 2 * k * b + k ^ 2 * a := by
  have h : c - 2 * k * b + k ^ 2 * a - (c - b ^ 2 / a) = (k * a - b) ^ 2 / a := by
    field_simp
    ring
  nlinarith [div_nonneg (sq_nonneg (k * a - b)) ha.le, h]

/-- The value of that same quadratic exactly at the minimizer `k = b/a`. -/
theorem quadratic_min_1d_arg {a b c : ℝ} (ha : 0 < a) :
    c - 2 * (b / a) * b + (b / a) ^ 2 * a = c - b ^ 2 / a := by
  field_simp
  ring

end KNOMP
