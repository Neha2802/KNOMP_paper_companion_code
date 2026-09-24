/-
KNOMP/BICConsistency.lean

Source: Section 8, "Consistency of BIC-Based Model-Order Selection",
Theorem `bic` (under-fitting and over-fitting probabilities both → 0).

STATUS: PROVED (for the deterministic core, and now for the over-fitting
half's limit statement too) / PARTIAL overall.

The paper's proof splits into two probabilistic halves (under-fitting,
over-fitting), each ultimately resting on a deterministic real-analysis
fact once its probabilistic setup is granted:
  - Under-fitting: `BIC_K - BIC_{K0} → +∞` because a sum of non-
    centralities each growing faster than `log N` dominates an `O(log N)`
    penalty term. This deterministic dominance fact is fully proved below
    (`sum_dominates_log_penalty`, given non-negativity of the
    non-centralities as an explicit hypothesis, matching the paper's own
    `λⱼ := Kⱼ²‖·‖²/σ² ≥ 0`) — genuine, checkable real analysis, not a
    probability statement, once the growth-rate hypothesis (i) is
    granted.
  - Over-fitting: `overfitting_prob_tendsto_zero` below is now a fully
    proved theorem (not a placeholder): given `α_fam,N → 0`, the
    probability that some spurious candidate is accepted at any stage
    tends to `0`, proved directly from `Theorem family-wise`
    (`FamilyWiseErrorControl.lean`, PROVED elsewhere in this project) via
    a squeeze argument.
  - What is still not attempted: connecting either half to an actual
    sequence of *random* detection statistics arising from KNOMP's own
    model (the non-centralities and family-wise events here are given
    abstractly, as hypotheses, not derived from a specific probabilistic
    data-generating process) — see `AsymptoticEfficiency.lean`'s
    docstring for the same reason applying more broadly to this
    project's probabilistic sections.
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace KNOMP

open Filter MeasureTheory
open scoped ENNReal

/-- **Deterministic core of the under-fitting argument.** If, for a
finite set of `K₀-K` omitted true planets, each non-centrality `λⱼ` is
non-negative (matching the paper's own `λⱼ := Kⱼ²‖·‖²/σ² ≥ 0`) and
satisfies `λⱼ / log N → ∞`, then their sum minus any fixed multiple of
`log N` still `→ ∞`. This is exactly the deterministic dominance fact the
paper's under-fitting argument reduces to, once the probabilistic
non-centrality-growth hypothesis (i) is granted. -/
theorem sum_dominates_log_penalty
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℕ → ℝ) (c : ℝ)
    (hnonneg : ∀ j N, 0 ≤ lam j N)
    (hgrowth : ∀ j ∈ s, Tendsto (fun N => lam j N / Real.log N) atTop atTop) :
    Tendsto (fun N : ℕ => (∑ j ∈ s, lam j N) - c * Real.log N) atTop atTop := by
  -- Pick any j₀ ∈ s; since every other term is ≥ 0, the sum is termwise
  -- at least λⱼ₀(N), so it suffices to show λⱼ₀(N) - c·log N → ∞.
  obtain ⟨j0, hj0⟩ := hs
  have hbound : ∀ N : ℕ,
      lam j0 N - c * Real.log N ≤ (∑ j ∈ s, lam j N) - c * Real.log N := by
    intro N
    have h := Finset.single_le_sum (f := fun j => lam j N) (fun j _ => hnonneg j N) hj0
    linarith
  apply Filter.tendsto_atTop_mono hbound
  -- λⱼ₀(N) - c·log N = (λⱼ₀(N)/log N - c) · log N, a product of two
  -- factors each → ∞ (once log N ≠ 0, i.e. eventually).
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio_minus_c : Tendsto (fun N : ℕ => lam j0 N / Real.log N - c) atTop atTop := by
    have h : Tendsto (fun N : ℕ => lam j0 N / Real.log (N : ℝ) + -c) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop (-c) (hgrowth j0 hj0)
    have heq : (fun N : ℕ => lam j0 N / Real.log (N : ℝ) + -c) =ᶠ[atTop]
            (fun N : ℕ => lam j0 N / Real.log (N : ℝ) - c) := by
      filter_upwards [eventually_ne_atTop 0] with N _
      show lam j0 N / Real.log ↑N + -c = lam j0 N / Real.log ↑N - c
      rw [sub_eq_add_neg]
    exact h.congr' heq.symm
  have hprod : Tendsto (fun N : ℕ => (lam j0 N / Real.log N - c) * Real.log N) atTop atTop :=
    hratio_minus_c.atTop_mul_atTop₀ hlog
  have heventually_eq : (fun N : ℕ => (lam j0 N / Real.log N - c) * Real.log N)
      =ᶠ[atTop] (fun N : ℕ => lam j0 N - c * Real.log N) := by
    have h2 : ∀ᶠ N : ℕ in atTop, Real.log N ≠ 0 := by
      filter_upwards [eventually_gt_atTop 1] with N hN
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    filter_upwards [h2] with N hN
    field_simp
  exact hprod.congr' heventually_eq

/-- **Over-fitting half.** As `N → ∞`, if the algorithm sends its
family-wise budget `α_fam,N → 0`, the probability that some spurious
candidate is accepted at *any* stage tends to `0` — a genuine limit
statement, fully proved here directly from `Theorem family-wise`
(`FamilyWiseErrorControl.lean`) rather than left as an unproved pointer.
An earlier version of this file stated only
`theorem overfitting_bound_pointer : True := trivial`, a vacuous
placeholder asserting nothing; this replaces it with the real content. -/
theorem overfitting_prob_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Kmax : ℕ → ℕ) (hKmax : ∀ N, 0 < Kmax N)
    (A : (N : ℕ) → Fin (Kmax N) → Set Ω)
    (alphaFam : ℕ → ℝ) (hnonneg : ∀ N, 0 ≤ alphaFam N)
    (hper : ∀ N k, μ (A N k) ≤ ENNReal.ofReal (alphaFam N / Kmax N))
    (halpha_to_zero : Tendsto alphaFam atTop (nhds 0)) :
    Tendsto (fun N => μ (⋃ k, A N k)) atTop (nhds (0 : ℝ≥0∞)) := by
  have hbound : ∀ N : ℕ, μ (⋃ k, A N k) ≤ ENNReal.ofReal (alphaFam N) := by
    intro N
    have hKmaxR : (0:ℝ) < (Kmax N : ℝ) := by exact_mod_cast hKmax N
    calc μ (⋃ k, A N k)
        ≤ ∑' k, μ (A N k) := measure_iUnion_le _
      _ = ∑ k, μ (A N k) := tsum_fintype _
      _ ≤ ∑ _k : Fin (Kmax N), ENNReal.ofReal (alphaFam N / Kmax N) :=
          Finset.sum_le_sum (fun k _ => hper N k)
      _ = (Kmax N : ℕ) • ENNReal.ofReal (alphaFam N / Kmax N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = ENNReal.ofReal ((Kmax N : ℝ) * (alphaFam N / Kmax N)) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (Kmax N : ℕ),
              ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (alphaFam N) := by
          congr 1
          field_simp
  have htop_zero : Tendsto (fun N => ENNReal.ofReal (alphaFam N)) atTop (nhds 0) := by
    have hcont := ENNReal.continuous_ofReal.tendsto (0:ℝ)
    have hcomposed := hcont.comp halpha_to_zero
    rw [show (fun N => ENNReal.ofReal (alphaFam N)) = ENNReal.ofReal ∘ alphaFam from rfl,
        show (nhds (0 : ENNReal)) = nhds (ENNReal.ofReal (0 : ℝ)) from by rw [ENNReal.ofReal_zero]]
    exact hcomposed
  have hbot_zero : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (nhds 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hbot_zero htop_zero
    (fun _ => by simp) hbound

end KNOMP
