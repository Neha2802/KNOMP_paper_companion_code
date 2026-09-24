/-
KNOMP/EfficiencyBoundUnweighted.lean

Source: Section 12, "An Efficiency Bound for Unweighted Fitting Under
Unequal Variances", Proposition (unnamed, Eq. `amhm-ratio`).

STATUS: PROVED, in full — including the equality condition, now proved
via an explicit Lagrange identity rather than left as a `sorry` (see
`sum_mul_sum_inv_eq_iff` below).

We take the two estimators' variance FORMULAS as given (exactly as the
source paper does: it states `Var(unweighted) = N⁻²∑σ_n²` and
`Var(weighted) = (∑σ_n⁻²)⁻¹` as already-derived closed forms, then does
pure algebra with them, rather than re-deriving them from a probability
space from scratch). Formalizing the variance computation itself from a
measure-theoretic model of independent, unequal-variance noise is a
separate, larger undertaking not attempted here.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

namespace KNOMP

variable {N : ℕ} (v : Fin N → ℝ)

/-- The unweighted (equal-weight) estimator's variance,
`N⁻² ∑ₙ σₙ²`, given as a closed form (see file docstring). -/
noncomputable def unweightedVar : ℝ := (1 / (N : ℝ) ^ 2) * ∑ n, v n

/-- The correctly (inverse-variance) weighted estimator's variance,
`(∑ₙ σₙ⁻²)⁻¹`. -/
noncomputable def weightedVar : ℝ := (∑ n, (v n)⁻¹)⁻¹

/-- **Cauchy-Schwarz core fact:** `N² ≤ (∑ vₙ)(∑ vₙ⁻¹)` for positive `vₙ`.
This is the one substantive analytic step; everything else in this file
is algebraic rearrangement of it. -/
theorem sum_mul_sum_inv_ge (hv : ∀ n, 0 < v n) [NeZero N] :
    (N : ℝ) ^ 2 ≤ (∑ n, v n) * ∑ n, (v n)⁻¹ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun n => Real.sqrt (v n)) (fun n => (Real.sqrt (v n))⁻¹)
  have hprod : ∀ n, Real.sqrt (v n) * (Real.sqrt (v n))⁻¹ = 1 := fun n => by
    have : Real.sqrt (v n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hv n))
    field_simp
  have hsq1 : ∀ n, (Real.sqrt (v n)) ^ 2 = v n := fun n => Real.sq_sqrt (hv n).le
  have hsq2 : ∀ n, ((Real.sqrt (v n))⁻¹) ^ 2 = (v n)⁻¹ := fun n => by
    rw [inv_pow, hsq1]
  simp only [hprod, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, hsq1, hsq2] at hcs
  exact hcs

/-- **Main proposition, inequality half.** `Var(unweighted) ≥
Var(weighted)`, with the exact ratio `(N⁻¹∑vₙ)(N⁻¹∑vₙ⁻¹)`, matching
Eq. `amhm-ratio` precisely. -/
theorem unweightedVar_ge_weightedVar (hv : ∀ n, 0 < v n) [NeZero N] :
    weightedVar v ≤ unweightedVar v := by
  have hne0 : (⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) :=
    Finset.mem_univ _
  have hsuminv_pos : 0 < ∑ n, (v n)⁻¹ :=
    Finset.sum_pos (fun n _ => inv_pos.mpr (hv n)) ⟨_, hne0⟩
  have hNsq_pos : (0:ℝ) < (N:ℝ) ^ 2 := by
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast NeZero.pos N
    positivity
  have hcore := sum_mul_sum_inv_ge v hv
  unfold weightedVar unweightedVar
  rw [inv_eq_one_div, show (1 / (N:ℝ) ^ 2) * (∑ n, v n) = (∑ n, v n) / (N:ℝ) ^ 2 by ring]
  rw [div_le_div_iff₀ hsuminv_pos hNsq_pos]
  nlinarith [hcore]

/-- **Cauchy-Schwarz equality case, via an explicit Lagrange identity.**
`(∑vₙ)(∑vₙ⁻¹) - N²` equals exactly `½ ∑ᵢ∑ⱼ (vᵢ-vⱼ)²/(vᵢvⱼ)` — a sum of
manifestly nonnegative terms, each `0` iff `vᵢ = vⱼ`. This sidesteps
needing Mathlib's general Cauchy-Schwarz equality-condition lemma (which,
checked directly against the source, does not exist in exactly the
"proportional sequences" form that would have been convenient here) by
proving the specific fact needed directly and elementarily. -/
theorem sum_mul_sum_inv_eq_iff (hv : ∀ n, 0 < v n) :
    (∑ n, v n) * (∑ n, (v n)⁻¹) = (N : ℝ) ^ 2 ↔ ∀ i j, v i = v j := by
  have hlagrange : (∑ n, v n) * (∑ n, (v n)⁻¹) - (N : ℝ) ^ 2
      = (1 / 2) * ∑ i, ∑ j, (v i - v j) ^ 2 / (v i * v j) := by
    have hexpand : ∀ i j : Fin N, (v i - v j) ^ 2 / (v i * v j)
        = v i / v j - 2 + v j / v i := by
      intro i j
      have hi := (hv i).ne'
      have hj := (hv j).ne'
      field_simp
      ring
    simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin N, ∑ j : Fin N, v i / v j = (∑ i, v i) * ∑ j, (v j)⁻¹ := by
      rw [Finset.sum_mul_sum]; congr 1
    have h2 : ∑ _i : Fin N, ∑ _j : Fin N, (2 : ℝ) = 2 * (N : ℝ) ^ 2 := by
      simp [Finset.sum_const, mul_comm]; ring
    have h3 : ∑ i : Fin N, ∑ j : Fin N, v j / v i = (∑ i, v i) * ∑ j, (v j)⁻¹ := by
      rw [Finset.sum_comm]; rw [Finset.sum_mul_sum]; congr 1
    rw [h1, h2, h3]; ring
  rw [← sub_eq_zero, hlagrange]
  constructor
  · intro heq
    have hsum_zero : ∑ i, ∑ j, (v i - v j) ^ 2 / (v i * v j) = 0 := by linarith
    intro i j
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        0 ≤ ∑ j, (v i - v j) ^ 2 / (v i * v j) := by
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact div_nonneg (sq_nonneg _) (mul_pos (hv i) (hv j)).le
    have houter := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_zero i (Finset.mem_univ i)
    have hnn2 : ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 ≤ (v i - v j) ^ 2 / (v i * v j) := by
      intro j _
      exact div_nonneg (sq_nonneg _) (mul_pos (hv i) (hv j)).le
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp houter j (Finset.mem_univ j)
    have hprod_pos : 0 < v i * v j := mul_pos (hv i) (hv j)
    have hsq_zero : (v i - v j) ^ 2 = 0 := by
      rw [div_eq_zero_iff] at hinner
      rcases hinner with h | h
      · exact h
      · exact absurd h (ne_of_gt hprod_pos)
    nlinarith [hsq_zero]
  · intro hconst
    have hall : ∀ i j : Fin N, (v i - v j) ^ 2 / (v i * v j) = 0 := by
      intro i j; rw [hconst i j]; simp
    simp_rw [hall]
    simp

/-- **Equality condition.** The ratio is exactly `1` iff every `vₙ` is
equal — now proved in full via `sum_mul_sum_inv_eq_iff` above, in both
directions. -/
theorem amhm_ratio_eq_one_iff (hv : ∀ n, 0 < v n) [NeZero N] :
    weightedVar v = unweightedVar v ↔ ∀ i j, v i = v j := by
  have hne0 : (⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) :=
    Finset.mem_univ _
  have hsuminv_pos : 0 < ∑ n, (v n)⁻¹ :=
    Finset.sum_pos (fun n _ => inv_pos.mpr (hv n)) ⟨_, hne0⟩
  have hNsq_pos : (0:ℝ) < (N:ℝ) ^ 2 := by
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast NeZero.pos N
    positivity
  unfold weightedVar unweightedVar
  have hsuminv_ne : (∑ n, (v n)⁻¹) ≠ 0 := hsuminv_pos.ne'
  have hNsq_ne : (N:ℝ)^2 ≠ 0 := hNsq_pos.ne'
  rw [inv_eq_one_div, div_eq_iff hsuminv_ne]
  rw [show (1 / (N:ℝ)^2 * ∑ n, v n) * ∑ n, (v n)⁻¹
        = (∑ n, v n) * (∑ n, (v n)⁻¹) / (N:ℝ)^2 by ring]
  rw [eq_comm, div_eq_one_iff_eq hNsq_ne]
  exact sum_mul_sum_inv_eq_iff v hv

end KNOMP
