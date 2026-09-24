/-
KNOMP/AsymptoticEfficiency.lean

Source: Section 7, "Asymptotic Efficiency of Grid-Initialized Newton
Refinement" (Assumption `regularity`, Lemma `wu` [external], Lemma
`grid-accuracy`, and the main theorem that one damped Newton step from a
grid start is asymptotically efficient).

STATUS: two `sorry`s (down from three), plus one new, mostly-proved
general-purpose lemma (`slutsky_perturbation`) with one small, precisely
isolated `sorry` of its own — see the per-theorem notes below.

UPDATE (grid-accuracy follow-on session). `lemma_grid_accuracy` below
still carries the paper's literal `sorry` — its `O_p(N^{-1/2})` *rate*
claim is not proved. But the derivable core of the paper's own argument
(steps 1-6 of `.tex` lines 1067-1173: deterministic quantization +
Taylor drift + Gaussian-Lipschitz concentration + union bound over an
`O(√N)`-point grid) IS now proved, in full, with 0 `sorry`, as a real,
hypothesis-gated theorem — but it establishes only *fixed-radius
consistency* (`θ̂_grid → θ0` in probability at any fixed `r0 > 0`), not
the rate. See `KNOMP/GridSearchConcentration.lean`'s header for exactly
why a flat union bound over the grid delivers consistency but not the
rate (the rate needs the paper's step 7, a genuine peeling/chaining
argument, deferred as a follow-on — same treatment `lemma_wu` gives the
CLT), and `lemma_grid_accuracy_fixed_radius_consistency` below for the
specialization of that result to this file's `Ω'`/`P`.

This is, honestly, the least formalizable section in the project. The
paper's own argument is a multi-page asymptotic-statistics derivation
built on:
  (i) an EXTERNAL classical theorem (Jennrich 1969, Wu 1981) on fixed-
      design nonlinear least squares asymptotic normality, which the
      paper itself explicitly declines to re-derive and cites instead —
      we do the same, as `lemma_wu` below;
  (ii) a genuinely probabilistic argument (concentration of a grid
      maximizer of a noisy statistic around the true parameter, at rate
      `O_p(N^{-1/2})`); and
  (iii) Slutsky's theorem combining the two pieces.

RECONNAISSANCE ON WHAT MATHLIB ACTUALLY HAS HERE (checked directly
against source, not assumed): more than expected, but still short of a
full proof of (i)/(ii). `Mathlib.MeasureTheory.Measure.FiniteMeasure`/
`.ProbabilityMeasure` carry real weak-convergence-of-measures machinery
(`ProbabilityMeasure.map`, the topology of weak convergence, a dedicated
`Portmanteau.lean` and `LevyProkhorovMetric.lean`), and
`Mathlib.Probability.Distributions.Gaussian` has `gaussianReal` with a
verified `IsProbabilityMeasure` instance — enough to STATE "converges in
distribution to a Gaussian" as an honest, type-correct Lean proposition.
What is still missing for (i): no central limit theorem anywhere in
`Mathlib.Probability` (only the strong LLN, `Mathlib.Probability.
StrongLaw`); and for (ii): nothing packaged for `O_p`-style tightness
statements. So `lemma_wu` and `lemma_grid_accuracy` remain `sorry`,
against real (non-vacuous) statements rather than `axiom ... : True`.

For (iii), Slutsky's theorem, a later pass DID make real progress: Mathlib
has no packaged Slutsky-type lemma, but the portmanteau-theorem machinery
in `Mathlib.MeasureTheory.Measure.Portmanteau` turned out to be enough to
prove a genuinely useful special case from scratch — see
`slutsky_perturbation` below, whose proof is complete except for one
small, precisely isolated technical step (an ℝ≥0/ℝ≥0∞ coercion commuting
with `liminf`, mathematically routine but fiddly to pin down against the
exact Mathlib combinator without a faster feedback loop than was
available). Along the way, a genuinely reusable fact not otherwise in
Mathlib was also proved: `ennreal_limsup_add_le`
(`limsup(u+v) ≤ limsup u + limsup v` for `ℕ`-indexed `ℝ≥0∞` sequences) —
the natural candidate `ENNReal.limsup_add_le` needs `CountableInterFilter
atTop`, which `atTop` on `ℕ` does not satisfy in general.

Using `slutsky_perturbation`, `one_step_newton_asymptotically_efficient`
below is now properly connected: an earlier version of this theorem
never actually related `θ̂₁` to the other estimators via any hypothesis
at all (its hypotheses said `θ̂` was asymptotically normal and `θ̂_grid`
was `O_p`-accurate, but said nothing whatsoever about `θ̂₁`, making the
theorem unprovable for a much more basic reason than "no CLT" — it was
simply not stating a true fact). It now takes the mathematically correct
hypothesis — `θ̂₁` is asymptotically equivalent to `θ̂` (`√N(θ̂₁-θ̂) → 0`
in probability, matching what the paper's own Lipschitz-Hessian
perturbation argument establishes) — and derives the conclusion via
`slutsky_perturbation`, modulo that lemma's one isolated internal
`sorry`.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import KNOMP.GridSearchConcentration

set_option maxHeartbeats 1000000

namespace KNOMP

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped Topology NNReal

/-- `limsup(u+v) ≤ limsup u + limsup v` for `ℕ`-indexed `ℝ≥0∞`-valued
sequences along `atTop`. Proved from scratch (not a direct Mathlib
lemma): the natural candidate `ENNReal.limsup_add_le` needs
`CountableInterFilter atTop`, which `atTop` on `ℕ` does NOT satisfy in
general (a countable intersection of "eventually" sets can be empty,
e.g. `⋂ᵢ [i,∞) = ∅`), and the general ordered-lattice version of
`limsup_add_le` triggered severe elaboration performance issues for
`ENNReal` specifically. This direct proof — unfold `limsup` to
`⨅ₙ⨆ᵢ≥ₙ`, bound the inner suprema termwise, then use that both outer
infima are antitone limits (so addition commutes with them via
continuity) — avoids both problems. -/
theorem ennreal_limsup_add_le (u v : ℕ → ENNReal) :
    Filter.limsup (fun n => u n + v n) Filter.atTop
      ≤ Filter.limsup u Filter.atTop + Filter.limsup v Filter.atTop := by
  rw [limsup_eq_iInf_iSup_of_nat, limsup_eq_iInf_iSup_of_nat, limsup_eq_iInf_iSup_of_nat]
  set A : ℕ → ENNReal := fun n => ⨆ i ≥ n, u i with hA
  set B : ℕ → ENNReal := fun n => ⨆ i ≥ n, v i with hB
  have hAanti : Antitone A := fun n m hnm => biSup_mono (fun i hi => le_trans hnm hi)
  have hBanti : Antitone B := fun n m hnm => biSup_mono (fun i hi => le_trans hnm hi)
  have hle : ∀ n, (⨆ i ≥ n, (u i + v i)) ≤ A n + B n := by
    intro n
    apply iSup₂_le
    intro i hi
    exact add_le_add (le_iSup₂ (f := fun i (_ : i ≥ n) => u i) i hi)
      (le_iSup₂ (f := fun i (_ : i ≥ n) => v i) i hi)
  calc ⨅ n, ⨆ i ≥ n, (u i + v i) ≤ ⨅ n, (A n + B n) := iInf_mono hle
    _ = (⨅ n, A n) + (⨅ n, B n) := by
        have h1 : Tendsto A atTop (𝓝 (⨅ n, A n)) := tendsto_atTop_iInf hAanti
        have h2 : Tendsto B atTop (𝓝 (⨅ n, B n)) := tendsto_atTop_iInf hBanti
        have h3 : Tendsto (fun n => A n + B n) atTop (𝓝 ((⨅ n, A n) + ⨅ n, B n)) :=
          Tendsto.add h1 h2
        have h4 : Antitone (fun n => A n + B n) :=
          fun n m hnm => add_le_add (hAanti hnm) (hBanti hnm)
        have h5 := tendsto_atTop_iInf h4
        exact tendsto_nhds_unique h5 h3

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- Closed-set limsup bound for the perturbed sequence `Y`, the technical
core of the Slutsky-type argument below: if `X`'s law converges weakly
to `μ` and `Y - X → 0` in probability, then for every closed `C`,
`limsup Pr(Y ∈ C) ≤ μ(C)`. Fully proved. -/
theorem slutsky_closed_bound
    (P : ProbabilityMeasure Ω)
    (X Y : ℕ → Ω → ℝ) (hXmeas : ∀ n, Measurable (X n)) (hYmeas : ∀ n, Measurable (Y n))
    (μ : ProbabilityMeasure ℝ)
    (hX : Tendsto (fun n => P.map (hXmeas n).aemeasurable) atTop (𝓝 μ))
    (hYX : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|}) atTop (𝓝 0))
    (C : Set ℝ) (hC : IsClosed C) :
    limsup (fun n => (P.map (hYmeas n).aemeasurable : Measure ℝ) C) atTop ≤ (μ : Measure ℝ) C := by
  have hbound : ∀ ε : ℝ, 0 < ε →
      limsup (fun n => (P.map (hYmeas n).aemeasurable : Measure ℝ) C) atTop
        ≤ (μ : Measure ℝ) (Metric.cthickening ε C) := by
    intro ε hε
    have hcontain : ∀ n, {ω | Y n ω ∈ C} ⊆
        {ω | X n ω ∈ Metric.cthickening ε C} ∪ {ω | ε ≤ |Y n ω - X n ω|} := by
      intro n ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      by_cases hcase : ε ≤ |Y n ω - X n ω|
      · exact Or.inr hcase
      · left
        push_neg at hcase
        show X n ω ∈ Metric.cthickening ε C
        rw [Metric.mem_cthickening_iff]
        calc EMetric.infEdist (X n ω) C ≤ edist (X n ω) (Y n ω) :=
              EMetric.infEdist_le_edist_of_mem hω
          _ = ENNReal.ofReal (dist (X n ω) (Y n ω)) := edist_dist _ _
          _ ≤ ENNReal.ofReal ε := by
              apply ENNReal.ofReal_le_ofReal
              rw [Real.dist_eq, abs_sub_comm]
              exact hcase.le
    have hineq : ∀ n, (P.map (hYmeas n).aemeasurable : Measure ℝ) C ≤
        (P.map (hXmeas n).aemeasurable : Measure ℝ) (Metric.cthickening ε C)
          + (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|} := by
      intro n
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
          Measure.map_apply (hYmeas n) hC.measurableSet,
          Measure.map_apply (hXmeas n) (Metric.isClosed_cthickening.measurableSet)]
      calc (P : Measure Ω) (Y n ⁻¹' C)
          ≤ (P : Measure Ω) ({ω | X n ω ∈ Metric.cthickening ε C}
              ∪ {ω | ε ≤ |Y n ω - X n ω|}) := measure_mono (hcontain n)
        _ ≤ (P : Measure Ω) {ω | X n ω ∈ Metric.cthickening ε C}
              + (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|} := measure_union_le _ _
        _ = (P : Measure Ω) (X n ⁻¹' Metric.cthickening ε C)
              + (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|} := by rfl
    calc limsup (fun n => (P.map (hYmeas n).aemeasurable : Measure ℝ) C) atTop
        ≤ limsup (fun n => (P.map (hXmeas n).aemeasurable : Measure ℝ)
              (Metric.cthickening ε C) + (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|}) atTop :=
          limsup_le_limsup (Eventually.of_forall hineq)
      _ ≤ limsup (fun n => (P.map (hXmeas n).aemeasurable : Measure ℝ)
              (Metric.cthickening ε C)) atTop
            + limsup (fun n => (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|}) atTop :=
          ennreal_limsup_add_le _ _
      _ ≤ (μ : Measure ℝ) (Metric.cthickening ε C) + 0 := by
          have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX
            (F := Metric.cthickening ε C) Metric.isClosed_cthickening
          have h2 : Tendsto (fun n => (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|}) atTop (𝓝 0) :=
            hYX ε hε
          rw [h2.limsup_eq]
          exact add_le_add h1 (le_refl 0)
      _ = (μ : Measure ℝ) (Metric.cthickening ε C) := by rw [add_zero]
  have hshrink : Tendsto (fun n : ℕ => (μ : Measure ℝ) (Metric.cthickening (1 / (n+1:ℝ)) C))
      atTop (𝓝 ((μ : Measure ℝ) C)) := by
    have heq : (μ : Measure ℝ) C = (μ : Measure ℝ) (⋂ n : ℕ, Metric.cthickening (1/(n+1:ℝ)) C) := by
      congr 1
      have hgen : (⋂ n : ℕ, Metric.cthickening (1 / (n + 1 : ℝ)) C)
          = ⋂ (δ : ℝ) (_ : 0 < δ), Metric.cthickening δ C := by
        apply le_antisymm
        · intro x hx
          simp only [Set.mem_iInter] at hx ⊢
          intro δ hδ
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
          exact Metric.cthickening_mono hn.le C (hx n)
        · intro x hx
          simp only [Set.mem_iInter] at hx ⊢
          intro n
          exact hx (1 / (n + 1 : ℝ)) (by positivity)
      rw [hgen, ← Metric.closure_eq_iInter_cthickening, hC.closure_eq]
    rw [heq]
    apply tendsto_measure_iInter_atTop
    · intro n
      exact (Metric.isClosed_cthickening).measurableSet.nullMeasurableSet
    · intro n m hnm
      exact Metric.cthickening_mono (by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact_mod_cast Nat.succ_le_succ hnm) C
    · exact ⟨0, (measure_lt_top _ _).ne⟩
  apply ge_of_tendsto hshrink
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact hbound (1/(n+1:ℝ)) (by positivity)

/-- **Slutsky-type lemma.** If `X`'s law converges weakly to `μ`, and
`Y - X → 0` in probability, then `Y`'s law also converges weakly to `μ`.
Built from scratch from Mathlib's portmanteau-theorem machinery (no
Slutsky-type lemma previously existed in Mathlib). Complete except for
one isolated technical step. -/
theorem slutsky_perturbation
    (P : ProbabilityMeasure Ω)
    (X Y : ℕ → Ω → ℝ) (hXmeas : ∀ n, Measurable (X n)) (hYmeas : ∀ n, Measurable (Y n))
    (μ : ProbabilityMeasure ℝ)
    (hX : Tendsto (fun n => P.map (hXmeas n).aemeasurable) atTop (𝓝 μ))
    (hYX : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P : Measure Ω) {ω | ε ≤ |Y n ω - X n ω|}) atTop (𝓝 0)) :
    Tendsto (fun n => P.map (hYmeas n).aemeasurable) atTop (𝓝 μ) := by
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  have hCbound := slutsky_closed_bound P X Y hXmeas hYmeas μ hX hYX Gᶜ hG.isClosed_compl
  have heq1 : ∀ n, (P.map (hYmeas n).aemeasurable : Measure ℝ) Gᶜ
      = 1 - (P.map (hYmeas n).aemeasurable : Measure ℝ) G := fun n =>
    prob_compl_eq_one_sub hG.measurableSet
  have heq2 : (μ : Measure ℝ) Gᶜ = 1 - (μ : Measure ℝ) G :=
    prob_compl_eq_one_sub hG.measurableSet
  simp only [heq1] at hCbound
  rw [heq2, ENNReal.limsup_const_sub atTop _ (by norm_num : (1:ENNReal) ≠ ⊤)] at hCbound
  have h1le : (μ : Measure ℝ) G ≤ 1 := prob_le_one
  have hfinal := (ENNReal.sub_le_sub_iff_left h1le (by norm_num)).mp hCbound
  -- hfinal : (μ : Measure ℝ) G ≤ liminf (fun n => (P.map ... : Measure ℝ) G) atTop, in ℝ≥0∞.
  -- The goal is stated in ℝ≥0 via `ProbabilityMeasure`'s own coeFn (`= toNNReal` of this).
  simp only [ProbabilityMeasure.coeFn_def]
  rw [← ENNReal.coe_le_coe]
  have hne_top : ∀ n, (P.map (hYmeas n).aemeasurable : Measure ℝ) G ≠ ⊤ :=
    fun n => (measure_lt_top _ _).ne
  have hne_top_mu : (μ : Measure ℝ) G ≠ ⊤ := (measure_lt_top _ _).ne
  rw [ENNReal.coe_toNNReal hne_top_mu]
  have hcomm : (↑(atTop.liminf (fun n => ((P.map (hYmeas n).aemeasurable : Measure ℝ) G).toNNReal))
      : ENNReal) = atTop.liminf (fun n => (P.map (hYmeas n).aemeasurable : Measure ℝ) G) := by
    have hbdd : atTop.IsBoundedUnder (· ≤ ·)
        (fun n => ((P.map (hYmeas n).aemeasurable : Measure ℝ) G).toNNReal) := by
      apply Filter.isBoundedUnder_of
      refine ⟨1, fun n => ?_⟩
      have h : (P.map (hYmeas n).aemeasurable : Measure ℝ) G ≤ 1 := prob_le_one
      simpa using ENNReal.toNNReal_mono (by norm_num) h
    have hcobdd : atTop.IsCoboundedUnder (· ≥ ·)
        (fun n => ((P.map (hYmeas n).aemeasurable : Measure ℝ) G).toNNReal) :=
      hbdd.isCoboundedUnder_ge
    have hbelow : atTop.IsBoundedUnder (· ≥ ·)
        (fun n => ((P.map (hYmeas n).aemeasurable : Measure ℝ) G).toNNReal) :=
      Filter.isBoundedUnder_of ⟨0, fun n => by simp⟩
    have key := Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono
      (fun n => ((P.map (hYmeas n).aemeasurable : Measure ℝ) G).toNNReal)
      ENNReal.continuous_coe.continuousAt hcobdd hbelow
    rw [key]
    congr 1
    funext n
    exact ENNReal.coe_toNNReal (hne_top n)
  rw [hcomm]
  exact hfinal

variable {Ω' : Type*} [MeasurableSpace Ω'] [TopologicalSpace Ω']

/-- **R1's honestly-automatic half.** On a compact parameter set, a
continuous third derivative is automatically bounded (extreme value
theorem) — for one FIXED model index. This is NOT the full content of
(R1): (R1) needs the bound to be uniform OVER the observation index `n`
as well, i.e. a single `C3` working for every `n : ℕ` simultaneously.
That uniformity is a genuine structural fact about the actual KNOMP/
Kepler model family (e.g. "the bound depends only on eccentricity, not
on observation time"), not a consequence of smoothness + compactness
alone, and needs an indexed model family (`μ : ℕ → ℝ → ℝ` for the actual
Kepler atoms) that doesn't exist anywhere in this codebase yet — see
`proposed_changes.md`. This lemma is the per-`n` building block only. -/
theorem bound_iteratedDeriv_of_continuousOn_of_isCompact
    (f : ℝ → ℝ) (Θ : Set ℝ) (hΘ : IsCompact Θ) (hΘne : Θ.Nonempty)
    (hcont : ContinuousOn (iteratedDeriv 3 f) Θ) :
    ∃ C : ℝ, ∀ θ ∈ Θ, |iteratedDeriv 3 f θ| ≤ C := by
  obtain ⟨x, hx, hmax⟩ := hΘ.exists_isMaxOn hΘne hcont.abs
  exact ⟨|iteratedDeriv 3 f x|, fun θ hθ => isMaxOn_iff.mp hmax θ hθ⟩

/-- **R3's honestly-sufficient half.** A quadratic lower-separation bound
on the limiting criterion `L` around `θ0` — the SAME `hdrift`-style shape
already used throughout `GridSearchConcentration.lean`/
`GridSearchRate.lean` — implies the strict separation `unique_limiting_
minimizer` requires. The paper states (R3) qualitatively ("`θ0` is the
unique minimizer") without ever supplying the constant `c` or the
argument producing one; this lemma makes explicit exactly what
quantitative fact would need to be established about the real KNOMP
criterion to discharge (R3) for the actual model — see
`proposed_changes.md`. -/
theorem unique_minimizer_of_quadratic_lower_bound
    {Θ : Set ℝ} {θ0 : ℝ} {L : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hquad : ∀ θ ∈ Θ, c * (θ - θ0) ^ 2 ≤ L θ - L θ0) :
    ∀ θ ∈ Θ, θ ≠ θ0 → L θ0 < L θ := by
  intro θ hθ hne
  have hpos : 0 < (θ - θ0) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith [hquad θ hθ]

/-- The paper's regularity conditions (R1)-(R3), Assumption `regularity`,
bundled as a structure with real, precisely-stated `Prop` fields — `μ`,
the model function family, `Θ`, the compact parameter set, `θ0`, the true
parameter, `σ`, the noise scale, and `I0`, the same Fisher-information
limit used in `lemma_wu`'s conclusion below (closing what used to be a
real gap: the old `True`-typed fields had zero connection to `I0` at
all).

This structure previously typed all three fields as `True`, which made
it FREE to construct (`⟨trivial, trivial, trivial⟩` works for any model,
satisfied or not) — every downstream theorem gating on `hreg :
RegularityAssumption` was therefore secretly unconditional, the same
practical dishonesty as a vacuous `True` conclusion, just on the
hypothesis side. Fixed here by giving each field its real mathematical
content, matching `Identifiability.lean`'s `hli` hypothesis pattern (a
genuine, unproved hypothesis gating a theorem, not a `sorry`'d theorem —
appropriate since nothing in this file constructs an instance of this
structure, so there is no proof obligation for a `sorry` to attach to).

(R2) is left as a real, unproved Prop — genuinely open, model-dependent
work, not attempted this session. (R1) and (R3) each have a companion
lemma just above (`bound_iteratedDeriv_of_continuousOn_of_isCompact`,
`unique_minimizer_of_quadratic_lower_bound`) establishing the honestly
derivable/sufficient part of the condition; see each lemma's docstring
for exactly what it does and does not establish, and
`proposed_changes.md` for the residual gap to the real Kepler model.

**A concrete instance now exists.** `KNOMP/KeplerFamily.lean` builds an
actual `d = 1` (period-only) Keplerian observation family on
`Kepler.lean`'s `keplerAtom` and, against that concrete family: proves
(R1)'s literal uniform-in-`n` bound as a real, fully-proved theorem
(`keplerFamily_uniform_third_deriv_bound`, 0 `sorry`), and states (R2)
and (R3) as concrete (not merely abstract-hint) `sorry`'d theorems
(`keplerFamily_fisher_info_converges`, `keplerFamily_limiting_criterion_
separation`) with docstrings explaining exactly what remains open for
each. Not imported here (to avoid a circular import) — see that file's
own header docstring for the full model and status. -/
structure RegularityAssumption (μ : ℕ → ℝ → ℝ) (Θ : Set ℝ) (θ0 : ℝ)
    (σ : ℝ) (I0 : ℝ≥0) : Prop where
  /-- (R1): a uniform (over both `n` and `θ ∈ Θ`) bound on third
  derivatives of the model. `.tex` ~992-998. -/
  uniform_third_deriv_bound :
    ∃ C3 : ℝ, ∀ n : ℕ, ∀ θ ∈ Θ, |iteratedDeriv 3 (μ n) θ| ≤ C3
  /-- (R2): the normalized Fisher information converges to the fixed
  positive limit `I0` — the SAME `I0` appearing in `lemma_wu`'s
  conclusion. `.tex` ~999-1004. -/
  fisher_info_converges :
    0 < I0 ∧
    Tendsto (fun N : ℕ => σ⁻¹ ^ 2 * (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, (deriv (μ n) θ0) ^ 2) atTop (𝓝 (I0 : ℝ))
  /-- (R3): `θ0` uniquely minimizes the limiting normalized criterion,
  stated via strict separation (`L θ0 < L θ` for all `θ ≠ θ0` in `Θ`),
  which packages minimality and uniqueness into a single clause. `.tex`
  ~1005-1014. -/
  unique_limiting_minimizer :
    ∃ L : ℝ → ℝ,
      (∀ θ ∈ Θ, Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (μ n θ - μ n θ0) ^ 2)
        atTop (𝓝 (L θ))) ∧
      (∀ θ ∈ Θ, θ ≠ θ0 → L θ0 < L θ)

/-- **Lemma `wu`, external classical result.** Jennrich (1969) and Wu
(1981): under `RegularityAssumption`, the fixed-design nonlinear least
squares estimator `θ̂ : ℕ → Ω → ℝ` (scalar parameter, for tractability —
see `VariableProjection.lean`'s docstring for the same simplification
made elsewhere in this project) satisfies: `√N·(θ̂ N - θ₀)`, as a
sequence of laws (pushforward probability measures on `ℝ`), converges in
the topology of weak convergence to `gaussianReal 0 I₀⁻¹`, the exact
asymptotic Cramér–Rao bound.

STATUS: `sorry`, not `axiom`. The paper cites this precisely rather than
re-deriving it, and so do we — but as a `sorry`, so that the compiler
visibly flags every downstream use rather than silently treating it as a
foundational assumption the way a hand-written `axiom` would. -/
theorem lemma_wu
    (P : ProbabilityMeasure Ω')
    (θhat : ℕ → Ω' → ℝ) (θ0 : ℝ) (I0 : ℝ≥0)
    (μ : ℕ → ℝ → ℝ) (Θ : Set ℝ) (σ : ℝ)
    (hreg : RegularityAssumption μ Θ θ0 σ I0)
    (hmeasurable : ∀ N : ℕ,
      AEMeasurable (fun ω => Real.sqrt N * (θhat N ω - θ0)) (P : Measure Ω')) :
    Tendsto (fun N : ℕ => P.map (hmeasurable N)) atTop
      (𝓝 (⟨gaussianReal 0 I0⁻¹, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  sorry

/-- **Lemma `grid-accuracy`.** A grid of resolution `O(N^{-1/2})`,
maximizing the (profiled) detection statistic near a true signal whose
non-centrality grows as `Θ(N)`, lands within `O_p(N^{-1/2})` of the
truth — stated here in the standard "bounded in probability at rate
`N^{-1/2}`" sense: for every `ε > 0` there is a fixed multiple `M` of
that rate such that, eventually in `N`, the rescaled error exceeds `M`
with probability less than `ε`.

STATUS: `sorry`, against the paper's literal rate claim. The paper's own
proof of the RATE specifically needs a finer-scale repetition of its
union-bound argument (step 7, `.tex` lines ~1160-1173) at the
`Δ_N = O(N^{-1/2})` grid-resolution scale — a genuine peeling/chaining
argument, not a routine extension of steps 1-6. That weaker "steps 1-6"
core — fixed-radius consistency of the grid argmax, not the rate — IS
now fully proved (0 `sorry`) as `grid_argmax_consistency` in
`KNOMP/GridSearchConcentration.lean`, specialized to this file's
`Ω'`/`P` immediately below as `lemma_grid_accuracy_fixed_radius_consistency`.
See that file's header for the precise reason a flat union bound gives
consistency but not the rate: at the rate-relevant radius `r_N =
M/√N`, the deterministic drift `c1·N·r_N² = c1·M²` is `O(1)` in `N`, so
the concentration bound's exponent does not vanish at that scale.

Under the revised paper draft's own strengthened hypothesis
(`Assumption increment`, a joint/pairwise concentration bound on the
INCREMENT process `θ ↦ g(θ)-g(θ')` rather than `hconc`'s marginal-only
bound at each fixed `θ`), `KNOMP/GridSearchIncrementRate.lean` closes
most of this gap: `grid_argmax_increment_polynomial_rate` is fully
proved, 0 `sorry`, and reaches every `γ < 1/2` (compare
`GridSearchRate.lean`'s `γ < 1/4` under the weaker `hconc`) — the
increment hypothesis removes the signal-to-noise wall identified above,
since its threshold scales with `|θ-θ'|` rather than being flat. The
paper's exact literal target, `O_p(N^{-1/2})` (this theorem's own
statement), is additionally stated precisely as `grid_argmax_increment_
rate` in that same file, with the further `hGdensity` local-density
hypothesis dyadic annulus peeling needs — but that theorem is honestly
`sorry`'d; see its docstring for exactly why (summing a series
simultaneously polynomial and doubly-exponential in the annulus index
is a genuine additional real-analysis gap, not yet closed anywhere in
this project). Neither result is wired into this theorem itself, since
doing so would require restating `RegularityAssumption`/this file's
hypotheses in terms of `hinc` and `hGdensity` instead of `hconc`/`hGcard`
— a larger rewiring left for a future session. -/
theorem lemma_grid_accuracy
    (P : ProbabilityMeasure Ω')
    (θhat_grid : ℕ → Ω' → ℝ) (θ0 : ℝ) (I0 : ℝ≥0)
    (μ : ℕ → ℝ → ℝ) (Θ : Set ℝ) (σ : ℝ)
    (hreg : RegularityAssumption μ Θ θ0 σ I0) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N : ℕ in atTop,
        ((P : Measure Ω') {ω | M < Real.sqrt N * |θhat_grid N ω - θ0|}).toReal < ε := by
  sorry

/-- **Fixed-radius consistency of the grid start** — the honestly-scoped
piece of Lemma `grid-accuracy` actually proved in this project (0
`sorry`), strictly weaker than `lemma_grid_accuracy`'s rate claim above.
A thin specialization of `grid_argmax_consistency`
(`KNOMP/GridSearchConcentration.lean`) to this file's `Ω'`/`P`; see that
theorem and its file header for the full hypothesis bundle (grid
cardinality `hGcard`, deterministic drift `hdrift` at the fixed radius
`r0`, Gaussian-Lipschitz concentration `hconc`) and proof. -/
theorem lemma_grid_accuracy_fixed_radius_consistency
    (P : ProbabilityMeasure Ω')
    (G : ℕ → Finset ℝ) (g : ℕ → ℝ → Ω' → ℝ) (μ : ℕ → ℝ → ℝ) (θ0 : ℝ)
    (θhat_grid : ℕ → Ω' → ℝ)
    (C σ L : ℝ) (hC : 0 < C) (hσ : 0 < σ) (hL : 0 < L)
    (hθ0mem : ∀ N, θ0 ∈ G N)
    (hargmax : ∀ N ω, θhat_grid N ω ∈ G N ∧ ∀ θ ∈ G N, g N θ ω ≤ g N (θhat_grid N ω) ω)
    (hGcard : ∀ᶠ N : ℕ in atTop, ((G N).card : ℝ) ≤ C * Real.sqrt N)
    (hconc : ∀ N : ℕ, ∀ θ x : ℝ, 0 < x →
      (P : Measure Ω') {ω | x ≤ |g N θ ω - μ N θ|} ≤
        ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2 * N))))
    (r0 c1 : ℝ) (hr0 : 0 < r0) (hc1 : 0 < c1)
    (hdrift : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ G N, r0 ≤ |θ - θ0| → μ N θ ≤ μ N θ0 - c1 * N) :
    Tendsto (fun N : ℕ => (P : Measure Ω') {ω | r0 ≤ |θhat_grid N ω - θ0|}) atTop (𝓝 0) :=
  grid_argmax_consistency P G g μ θ0 θhat_grid C σ L hC hσ hL hθ0mem hargmax hGcard hconc
    r0 c1 hr0 hc1 hdrift

/-- **Main theorem, now properly connected.** One damped Newton step from
the grid start, `θ̂₁ : ℕ → Ω → ℝ`, is asymptotically efficient: `√N·(θ̂₁ N
- θ₀)` has the same limiting `gaussianReal 0 I₀⁻¹` distribution as the
fully-iterated `θ̂` of Lemma `wu`.

An earlier version of this theorem's hypotheses said nothing whatsoever
about `θ̂₁` beyond it being *some* sequence — no relationship to `θ̂` or
`θ̂_grid` was ever stated, making the theorem unprovable for a much more
basic reason than "no CLT": it simply wasn't stating a true fact. This
version instead takes the mathematically correct hypothesis — `θ̂₁` is
*asymptotically equivalent* to `θ̂` (`√N(θ̂₁ - θ̂) → 0` in probability,
which is exactly what the paper's own Lipschitz-Hessian perturbation
argument, combining Lemma `wu` and Lemma `grid-accuracy`, is used to
establish) — and derives the stated conclusion from it via
`slutsky_perturbation` above, which is honest and complete modulo that
lemma's own single isolated internal `sorry`. -/
theorem one_step_newton_asymptotically_efficient
    (P : ProbabilityMeasure Ω')
    (θhat θhat1 : ℕ → Ω' → ℝ) (θ0 : ℝ) (I0 : ℝ≥0)
    (μ : ℕ → ℝ → ℝ) (Θ : Set ℝ) (σ : ℝ)
    (hreg : RegularityAssumption μ Θ θ0 σ I0)
    (hmeasurable : ∀ N : ℕ, Measurable (fun ω => Real.sqrt N * (θhat N ω - θ0)))
    (hmeasurable1 : ∀ N : ℕ, Measurable (fun ω => Real.sqrt N * (θhat1 N ω - θ0)))
    (hwu : Tendsto (fun N : ℕ => P.map (hmeasurable N).aemeasurable) atTop
      (𝓝 (⟨gaussianReal 0 I0⁻¹, inferInstance⟩ : ProbabilityMeasure ℝ)))
    (hequiv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ => (P : Measure Ω')
        {ω | ε ≤ |Real.sqrt N * (θhat1 N ω - θ0) - Real.sqrt N * (θhat N ω - θ0)|})
        atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => P.map (hmeasurable1 N).aemeasurable) atTop
      (𝓝 (⟨gaussianReal 0 I0⁻¹, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  slutsky_perturbation P (fun N ω => Real.sqrt N * (θhat N ω - θ0))
    (fun N ω => Real.sqrt N * (θhat1 N ω - θ0))
    hmeasurable hmeasurable1 _ hwu hequiv

end KNOMP
