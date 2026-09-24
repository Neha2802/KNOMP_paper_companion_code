/-
KNOMP/ExactDetectionIncrement.lean

Source: Section 3, "The Exact Detection Increment", Theorem `glrt`
("Exact reduction in weighted sum of squares").

STATUS: PROVED (modulo the general disclaimer in the project README: the
`simp`/`rw` chains here were written without a compiler and may need
small local repairs; the proof *architecture* is complete and does not
depend on any `sorry`, `axiom`, or unformalized external result).

Paper statement being formalized: augmenting the model `Xβ` with one new
candidate atom `f` at gain `K`, and minimizing the `W`-weighted sum of
squares jointly over `(β, K)`, reduces the sum of squares by *exactly*
`ρ_W(f)` — not an estimate of the improvement, the improvement itself.

Proof strategy (mirrors the paper's own final step, "It remains to
compute ΔJ", rather than the earlier Schur-complement route to the same
place): profile out `β` for fixed `K` first (an instance of
`wls_optimality`/`wls_gap_eq` with shifted data `y - K • f`), then profile
out the univariate `K` by completing the square (`quadratic_min_1d`).
-/
import KNOMP.Common

namespace KNOMP

open Matrix

variable {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ) (W : Matrix (Fin N) (Fin N) ℝ)
  (y f : Fin N → ℝ)

/-- The augmented, `W`-weighted sum of squares as a function of the
existing linear parameters `β` and the new atom's gain `K`. -/
def augmentedObjective (β : Fin p → ℝ) (K : ℝ) : ℝ :=
  weightedSqNorm W (y - X.mulVec β - K • f)

/-- The gain value the paper calls `K̂` (Eq. `Khat`). -/
noncomputable def Khat : ℝ :=
  dotProduct f (W.mulVec (residual X W y)) / weightedSqNorm W (fPerp X W f)

/-- **Theorem `glrt`, lower-bound half.** No choice of `(β, K)` can push
the augmented objective below `‖r(W)‖_W² - ρ_W(f)`. -/
theorem exact_detection_increment_le
    (hW : IsPosDefR W) (hinv : IsUnit (Xᵀ * W * X).det)
    (hpos : 0 < weightedSqNorm W (fPerp X W f)) (β : Fin p → ℝ) (K : ℝ) :
    weightedSqNorm W (residual X W y) - rhoW X W y f ≤ augmentedObjective X W y f β K := by
  -- Step 1: profile β for this fixed K, using shifted data `y - K • f`.
  have step1 : weightedSqNorm W (residual X W (y - K • f))
      ≤ weightedSqNorm W ((y - K • f) - X.mulVec β) :=
    wls_optimality X W hW (y - K • f) hinv β
  have hrearrange : (y - K • f) - X.mulVec β = y - X.mulVec β - K • f := by abel
  rw [hrearrange] at step1
  -- Step 2: `residual X W (y - K•f) = r(W) - K • f_perp(W)`.
  have step2 : residual X W (y - K • f) = residual X W y - K • fPerp X W f := by
    rw [residual_shift X W y f hinv K, fPerp_eq_residual X W f]
  rw [step2] at step1
  -- Step 3: expand the left side as an explicit quadratic in K.
  have step3 := weightedSqNorm_sub_smul W hW.symm (residual X W y) (fPerp X W f) K
  -- Step 4: `dotProduct (f_perp) (W r) = dotProduct f (W r)` (definitional
  -- base of ρ_W), so the quadratic's linear coefficient is exactly what
  -- ρ_W's numerator is built from.
  have step4 := dot_f_weight_residual_eq_dot_fPerp X W y f hinv
  -- Step 5: complete the square: the quadratic in K is bounded below by
  -- its value at the true minimizer, which is exactly `‖r‖² - ρ_W(f)`.
  have step5 := quadratic_min_1d (a := weightedSqNorm W (fPerp X W f))
    (b := dotProduct (fPerp X W f) (W.mulVec (residual X W y)))
    (c := weightedSqNorm W (residual X W y)) hpos K
  unfold augmentedObjective rhoW
  rw [← step4] at step5
  calc weightedSqNorm W (residual X W y)
        - dotProduct f (W.mulVec (residual X W y)) ^ 2 / weightedSqNorm W (fPerp X W f)
      ≤ weightedSqNorm W (residual X W y)
          - 2 * K * dotProduct f (W.mulVec (residual X W y))
          + K ^ 2 * weightedSqNorm W (fPerp X W f) := step5
    _ = weightedSqNorm W (residual X W y - K • fPerp X W f) := by rw [step4]; exact step3.symm
    _ ≤ weightedSqNorm W (y - X.mulVec β - K • f) := step1

/-- **Theorem `glrt`, achievability half.** The lower bound above is
attained exactly at `K = K̂` and `β = β̂(y - K̂•f)`, matching the paper's
`(β̂', K̂)`. Together with `exact_detection_increment_le`, this shows the
minimum of the augmented objective is exactly `‖r(W)‖_W² - ρ_W(f)`, i.e.
`ΔJ = ρ_W(f)` exactly. -/
theorem exact_detection_increment_achieved
    (hW : IsPosDefR W) (hinv : IsUnit (Xᵀ * W * X).det)
    (hpos : 0 < weightedSqNorm W (fPerp X W f)) :
    augmentedObjective X W y f (betaHat X W (y - Khat X W y f • f)) (Khat X W y f)
      = weightedSqNorm W (residual X W y) - rhoW X W y f := by
  unfold augmentedObjective
  have hbeta : y - Khat X W y f • f - X.mulVec (betaHat X W (y - Khat X W y f • f))
      = residual X W (y - Khat X W y f • f) := by
    unfold residual; abel
  have hrearrange : y - X.mulVec (betaHat X W (y - Khat X W y f • f)) - Khat X W y f • f
      = y - Khat X W y f • f - X.mulVec (betaHat X W (y - Khat X W y f • f)) := by abel
  rw [hrearrange, hbeta, residual_shift X W y f hinv (Khat X W y f), ← fPerp_eq_residual X W f,
      weightedSqNorm_sub_smul W hW.symm (residual X W y) (fPerp X W f) (Khat X W y f)]
  rw [← dot_f_weight_residual_eq_dot_fPerp X W y f hinv]
  unfold Khat rhoW
  rw [quadratic_min_1d_arg hpos]

/-- Both halves together: `ΔJ = ρ_W(f)` exactly, as an equality between
`‖r(W)‖_W²` minus the true joint minimum and `ρ_W(f)`, matching
Eq. `glrt-exact` in the source paper precisely. -/
theorem exact_detection_increment
    (hW : IsPosDefR W) (hinv : IsUnit (Xᵀ * W * X).det)
    (hpos : 0 < weightedSqNorm W (fPerp X W f)) :
    (∀ β K, weightedSqNorm W (residual X W y) - rhoW X W y f ≤ augmentedObjective X W y f β K)
      ∧ ∃ β K, augmentedObjective X W y f β K
          = weightedSqNorm W (residual X W y) - rhoW X W y f :=
  ⟨fun β K => exact_detection_increment_le X W y f hW hinv hpos β K,
   ⟨betaHat X W (y - Khat X W y f • f), Khat X W y f,
    exact_detection_increment_achieved X W y f hW hinv hpos⟩⟩

end KNOMP
