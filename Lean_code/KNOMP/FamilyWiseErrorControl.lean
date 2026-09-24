/-
KNOMP/FamilyWiseErrorControl.lean

Source: Section 17, "Family-Wise False-Acceptance Control", Theorem
"Union-bound family-wise error control".

STATUS: PROVED (see README disclaimer).

Paper statement: if each of `Kmax` sequential detection stages has its own
false-acceptance probability capped at `α_fam/Kmax`, the probability of a
false acceptance at *some* stage is at most `α_fam` — with no independence
or disjointness assumption on the stages (exactly Boole's inequality /
the union bound).

We use Mathlib's measure-theoretic union bound directly: the family-wise
event is `⋃ k, A k` for per-stage "false acceptance at stage k" events
`A k`, and the paper's proof *is* `measure_iUnion_le` plus summing equal
per-stage budgets — nothing else is needed. -/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace KNOMP

open MeasureTheory

/-- **Theorem `family-wise`.** With per-stage false-acceptance events
`A : Fin Kmax → Set Ω`, each budgeted at `α_fam / Kmax`, the probability
of at least one false acceptance across all `Kmax` stages is at most
`α_fam`. No hypothesis on the dependence structure between the `A k` is
needed (matching the paper's own remark that the union bound requires
none). -/
theorem family_wise_error_control {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Kmax : ℕ) (hKmax : 0 < Kmax) (A : Fin Kmax → Set Ω)
    (alphaFam : ℝ) (hnonneg : 0 ≤ alphaFam)
    (hper : ∀ k, μ (A k) ≤ ENNReal.ofReal (alphaFam / Kmax)) :
    μ (⋃ k, A k) ≤ ENNReal.ofReal alphaFam := by
  have hKmaxR : (0:ℝ) < (Kmax : ℝ) := by exact_mod_cast hKmax
  calc μ (⋃ k, A k)
      ≤ ∑' k, μ (A k) := measure_iUnion_le A
    _ = ∑ k, μ (A k) := tsum_fintype _
    _ ≤ ∑ _k : Fin Kmax, ENNReal.ofReal (alphaFam / Kmax) := Finset.sum_le_sum (fun k _ => hper k)
    _ = (Kmax : ℕ) • ENNReal.ofReal (alphaFam / Kmax) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal ((Kmax : ℝ) * (alphaFam / Kmax)) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (Kmax : ℕ),
            ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal alphaFam := by
        congr 1
        field_simp

end KNOMP
