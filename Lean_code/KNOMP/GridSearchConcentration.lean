/-
KNOMP/GridSearchConcentration.lean

PURPOSE: general-purpose, not KNOMP-specific, infrastructure for
`AsymptoticEfficiency.lean`'s `lemma_grid_accuracy` (paper Section 7,
"Accuracy of the grid-search starting point", `lem:grid-accuracy`, `.tex`
lines 1067-1173).

STATUS: 0 `sorry`, 0 `axiom`.

SCOPE (read this before comparing against the paper). The paper's lemma
claims a rate: `θ̂_grid - θ0 = O_p(N^{-1/2})`. Its proof sketch has seven
steps; steps 1-6 (deterministic quantization + Taylor drift + Gaussian-
Lipschitz concentration + union bound over an `O(√N)`-point grid) argue
consistency at a FIXED radius; step 7 ("a finer-scale repetition of the
same argument" at the `Δ_N = O(N^{-1/2})` scale) is what actually
delivers the *rate*, not just consistency.

This file proves ONLY the fixed-radius result — `grid_argmax_consistency`
below: for every fixed `r0 > 0`, the grid argmax's probability of being
`r0`-far from `θ0` tends to `0` as `N → ∞`. This is a real, non-vacuous,
fully-proved theorem (0 `sorry`), but it is STRICTLY WEAKER than the
paper's stated rate. The reason step 7 is not attempted here: at the
rate-relevant radius `r_N = M/√N`, the deterministic drift
`c1 * N * r_N² = c1 * M²` is `O(1)` in `N` (not growing), so with a
Lipschitz constant `L = O(√N)` the concentration bound's exponent does
NOT vanish as `N → ∞` at that scale — a flat union bound over the grid,
exactly the argument used below, does not make the failure probability
vanish at the rate-relevant radius. Turning this into the actual rate
needs a genuine peeling/chaining argument (bounding the annuli
`r_N ≤ |θ-θ0| < 2 r_N`, `2 r_N ≤ |θ-θ0| < 4 r_N`, ... separately and
summing a geometric series of union bounds), comparable in depth to this
project's already-documented CLT gap (`lemma_wu`, same file). Per
explicit user direction (this file's governing session), that peeling
argument is deferred as a follow-on, not attempted here — this is the
same treatment `lemma_wu` gives the CLT: an honest, narrower, fully
proved result now, with the harder external piece named and deferred
rather than faked.

Also deferred (real, well-scoped follow-on work, not attempted here):
- Deriving `hconc` from a raw Gaussian noise vector and an explicit
  Lipschitz bound on `g` (i.e. actually proving the cited
  Boucheron-Lugosi-Massart Thm 5.6, or locating/building the Mathlib
  primitive for it) — taken here as an explicit hypothesis rather than a
  `sorry`, since *given* `g`'s Lipschitz structure the bound is an
  unconditional classical fact, not a paper-specific unknown.
- Modeling an actual geometric grid over `Θ` (vs. taking the cardinality
  bound `hGcard` as a hypothesis) and connecting `g` to the paper's real
  detection statistic `ρ_W(f(θ))` — this file stays paper-structure-
  agnostic, matching `AnalyticZeroMeasure.lean`/`LinearIndependentEvaluation.lean`.

PROOF STRATEGY for `grid_argmax_consistency`. Fix `r0 > 0`, obtain
`c1 > 0` from `hdrift`. Set `x_N := c1 * N / 2`.
  * The bad event `{r0 ≤ |θ̂_grid N ω - θ0|}` is contained in the union,
    over grid points `θ` in `G N` with `r0 ≤ |θ - θ0|`, of
    `{g N θ0 ω ≤ g N θ ω}` — since `θ̂_grid N ω` is itself such a `θ`
    whenever the bad event holds (it maximizes `g N · ω` over `G N`, and
    `θ0 ∈ G N`).
  * For each such `θ`: if `|g N θ ω - μ N θ| < x_N` and
    `|g N θ0 ω - μ N θ0| < x_N` both hold, then (triangle inequality +
    `hdrift`'s `μ N θ ≤ μ N θ0 - c1 * N`) `g N θ ω < g N θ0 ω` strictly —
    so `{g N θ0 ω ≤ g N θ ω}` is contained in the union of the two
    `x_N`-deviation events, each bounded by `hconc`.
  * Union bound over the `≤ C√N` grid points, with `hconc`'s Gaussian
    tail at `x_N = c1*N/2`: total failure probability
    `≤ 4 * C * √N * exp(-κN)` for `κ := c1²/(8σ²L²) > 0` — exponential
    decay beats the `√N` polynomial factor
    (`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`), giving `→ 0`.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

namespace KNOMP

open MeasureTheory Filter Topology
open scoped ENNReal Topology

/-- **Fixed-radius consistency of a grid-search argmax**, under an
explicit grid-cardinality bound (`hGcard`), a deterministic quadratic
drift hypothesis at the fixed radius `r0` (`hdrift`), and a Gaussian-
Lipschitz-style concentration hypothesis (`hconc`) for the statistic `g`
around an abstract mean function `μ`. See the file header for exactly
what this delivers versus the paper's stronger, rate-level claim. -/
theorem grid_argmax_consistency
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (G : ℕ → Finset ℝ) (g : ℕ → ℝ → Ω → ℝ) (μ : ℕ → ℝ → ℝ) (θ0 : ℝ)
    (θhat_grid : ℕ → Ω → ℝ)
    (C σ L : ℝ) (hC : 0 < C) (hσ : 0 < σ) (hL : 0 < L)
    (hθ0mem : ∀ N, θ0 ∈ G N)
    (hargmax : ∀ N ω, θhat_grid N ω ∈ G N ∧ ∀ θ ∈ G N, g N θ ω ≤ g N (θhat_grid N ω) ω)
    (hGcard : ∀ᶠ N : ℕ in atTop, ((G N).card : ℝ) ≤ C * Real.sqrt N)
    (hconc : ∀ N : ℕ, ∀ θ x : ℝ, 0 < x →
      (P : Measure Ω) {ω | x ≤ |g N θ ω - μ N θ|} ≤
        ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2 * N))))
    (r0 c1 : ℝ) (hr0 : 0 < r0) (hc1 : 0 < c1)
    (hdrift : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ G N, r0 ≤ |θ - θ0| → μ N θ ≤ μ N θ0 - c1 * N) :
    Tendsto (fun N : ℕ => (P : Measure Ω) {ω | r0 ≤ |θhat_grid N ω - θ0|}) atTop (𝓝 0) := by
  set κ : ℝ := c1 ^ 2 / (8 * σ ^ 2 * L ^ 2) with hκdef
  have hκpos : 0 < κ := by positivity
  have hbound : ∀ᶠ N : ℕ in atTop,
      (P : Measure Ω) {ω | r0 ≤ |θhat_grid N ω - θ0|} ≤
        ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * N)) := by
    filter_upwards [hdrift, hGcard, eventually_ge_atTop 1] with N hdriftN hGcardN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    set x : ℝ := c1 * N / 2 with hxdef
    have hxpos : 0 < x := by positivity
    set S : Finset ℝ := (G N).filter (fun θ => r0 ≤ |θ - θ0|) with hSdef
    have hsubset1 : {ω | r0 ≤ |θhat_grid N ω - θ0|} ⊆
        ⋃ θ ∈ S, {ω | g N θ0 ω ≤ g N θ ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      obtain ⟨hmem, hmax⟩ := hargmax N ω
      have hle : g N θ0 ω ≤ g N (θhat_grid N ω) ω := hmax θ0 (hθ0mem N)
      simp only [Set.mem_iUnion]
      exact ⟨θhat_grid N ω, Finset.mem_filter.mpr ⟨hmem, hω⟩, hle⟩
    have hsubset2 : ∀ θ ∈ S,
        {ω | g N θ0 ω ≤ g N θ ω} ⊆
          {ω | x ≤ |g N θ ω - μ N θ|} ∪ {ω | x ≤ |g N θ0 ω - μ N θ0|} := by
      intro θ hθ ω hω
      obtain ⟨hθG, hθr0⟩ := Finset.mem_filter.mp hθ
      have hdrift_θ : μ N θ ≤ μ N θ0 - c1 * N := hdriftN θ hθG hθr0
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨hA, hB⟩ := hcon
      rw [abs_lt] at hA hB
      linarith [hA.1, hA.2, hB.1, hB.2]
    have hperθ : ∀ θ ∈ S,
        (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
          ENNReal.ofReal (4 * Real.exp (-κ * N)) := by
      intro θ hθ
      have hxeq : x ^ 2 / (2 * σ ^ 2 * L ^ 2 * (N : ℝ)) = κ * N := by
        rw [hxdef, hκdef]
        field_simp
        ring
      calc (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω}
          ≤ (P : Measure Ω) ({ω | x ≤ |g N θ ω - μ N θ|} ∪ {ω | x ≤ |g N θ0 ω - μ N θ0|}) :=
            measure_mono (hsubset2 θ hθ)
        _ ≤ (P : Measure Ω) {ω | x ≤ |g N θ ω - μ N θ|}
              + (P : Measure Ω) {ω | x ≤ |g N θ0 ω - μ N θ0|} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2 * N)))
              + ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2 * N))) :=
            add_le_add (hconc N θ x hxpos) (hconc N θ0 x hxpos)
        _ = ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2 * N))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
        _ = ENNReal.ofReal (4 * Real.exp (-κ * N)) := by
            have : -x ^ 2 / (2 * σ ^ 2 * L ^ 2 * (N : ℝ)) = -κ * N := by
              rw [neg_div, hxeq]; ring
            rw [this]
    have hunion : (P : Measure Ω) {ω | r0 ≤ |θhat_grid N ω - θ0|} ≤
        ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} :=
      (measure_mono hsubset1).trans (measure_biUnion_finset_le S _)
    have hsum_le : ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
        S.card • ENNReal.ofReal (4 * Real.exp (-κ * N)) :=
      Finset.sum_le_card_nsmul S _ _ hperθ
    have hcardS : (S.card : ℝ) ≤ C * Real.sqrt N :=
      le_trans (by exact_mod_cast Finset.card_filter_le (G N) _) hGcardN
    have hnsmul_eq : S.card • ENNReal.ofReal (4 * Real.exp (-κ * N)) =
        ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * N))) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hcard_bound : ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * N))) ≤
        ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * N)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp_nonneg : (0 : ℝ) ≤ 4 * Real.exp (-κ * N) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcardS hexp_nonneg]
    calc (P : Measure Ω) {ω | r0 ≤ |θhat_grid N ω - θ0|}
        ≤ ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} := hunion
      _ ≤ S.card • ENNReal.ofReal (4 * Real.exp (-κ * N)) := hsum_le
      _ = ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * N))) := hnsmul_eq
      _ ≤ ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * N)) := hcard_bound
  have hupper : Tendsto (fun N : ℕ => ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * N)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * N)) atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) κ hκpos).comp
        tendsto_natCast_atTop_atTop
    have h2 : (fun N : ℕ => 4 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * N))
        = fun N : ℕ => 4 * C * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * N)) := by
      funext N
      rw [Real.sqrt_eq_rpow]
      ring
    have h3 : Tendsto (fun N : ℕ => 4 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * N))
        atTop (𝓝 (4 * C * 0)) := by
      rw [h2]
      exact h1.const_mul (4 * C)
    rw [mul_zero] at h3
    have h4 := ENNReal.tendsto_ofReal h3
    simpa using h4
  have hlower : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (Eventually.of_forall (fun N => by simp)) hbound

end KNOMP
