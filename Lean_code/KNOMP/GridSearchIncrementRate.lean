/-
KNOMP/GridSearchIncrementRate.lean

PURPOSE: follow-on to `GridSearchConcentration.lean`/`GridSearchRate.lean`,
using the revised paper draft's `Assumption increment` (`.tex`
`KNOMP_complete_proofs_revised_2.tex` lines 1126-1148; unchanged in
content, only shifted to ~1160-1188 by an unrelated 28-line insertion
earlier in the file, in the current canonical paper
`source/KNOMP_fix_attempt_1.tex` — confirmed via `diff` against
`revised_2.tex`, which touches only §2/§11's Fourier citation, not this
assumption) instead of the earlier, weaker marginal concentration
hypothesis `hconc`. `hconc` only
controls `g N θ` against its own mean at a single fixed `θ`; the paper's
revised `Assumption increment` controls the INCREMENT process
`θ ↦ g N θ - g N θ'` jointly, with a noise scale proportional to
`|θ - θ'|` rather than a θ-independent scale. `GridSearchRate.lean`'s own
header already anticipated that exactly this kind of stronger tool would
be needed to beat its `N^{-1/4}` wall; this file supplies it.

STATUS: 1 `sorry` (`grid_argmax_increment_rate`, the paper's literal
`O_p(N^{-1/2})` target via dyadic annulus peeling — see that theorem's
own docstring for exactly what's missing), 0 `axiom`.
`grid_argmax_increment_polynomial_rate` (γ < 1/2) is fully proved, 0
`sorry`.

## What improves, and why

Calibrating the increment-concentration threshold `x` (per grid point
`θ`, against its OWN distance `rθ := |θ - θ0|`) to exactly cancel a
quadratic drift `μ N θ ≤ μ N θ0 - c1 * N * rθ²` only needs
`x * √N * rθ = c1 * N * rθ² / 2`, i.e. `x = c1 * √N * rθ / 2` — note this
is `Θ(√N · rθ)`, ONE power of `rθ` less than the marginal case's
calibration `x = Θ(N · rθ²)` (half the drift, with no `rθ`-scaling
available in `hconc`'s flat threshold). Since `hinc`'s tail bound is
`exp(-x² / (2σ²L²))` with no separate `/N` factor (the `√N` needed to
match `hconc`'s `Θ(√N)` noise scale at a fixed point is already folded
into the threshold's own `|θ-θ'|`-proportional shape), the resulting
per-point exponent is `κ · N · rθ²` (quadratic in `rθ`) instead of the
marginal case's `κ · N · rθ⁴` (quartic) — exactly the signal-to-noise
improvement `GridSearchRate.lean`'s header predicted would be needed.

Because `rθ ≥ r` for every `θ` counted in the union bound at threshold
radius `r`, and `exp` is monotone, the per-point bound `exp(-κNrθ²)` is
in turn bounded above by the single number `exp(-κNr²)` — i.e. even
though the calibration is genuinely per-point, the FINAL bound used in
the union sum collapses to a single, `θ`-independent number depending
only on `r`. This means the flat cardinality hypothesis `hGcard`
(unchanged from `GridSearchRate.lean`) suffices for a shrinking-radius
result — no grid-density hypothesis is needed for this weaker
(polynomial-rate) theorem. (A density hypothesis WOULD be needed to
reach the paper's exact `O_p(N^{-1/2})` rate via annulus peeling — see
"Not attempted" below.)

This file's one new hypothesis, `hdrift`, is stated UNCONDITIONALLY
(`∀ θ ∈ G N, μ N θ ≤ μ N θ0 - c1*N*(θ-θ0)²`, not gated behind
`r ≤ |θ-θ0|` the way `GridSearchRate.lean`'s is) — a genuine, standard
quadratic-curvature assumption (the same shape `AsymptoticEfficiency.
lean`'s `unique_minimizer_of_quadratic_lower_bound` uses), needed here
because the per-point calibration argument uses each point's own actual
distance, not just "past a fixed threshold."

## What this file proves

`grid_argmax_increment_polynomial_rate`: for any FIXED `γ` with
`0 < γ < 1/2` (compare `GridSearchRate.lean`'s `γ < 1/4`), the grid
argmax's probability of being farther than `N^{-γ}` from `θ0` tends to
`0` — i.e. `θ̂_grid - θ0 = o_p(N^{-γ})` for every such `γ`. Genuinely
short of the paper's `γ = 1/2` (`O_p`, not `o_p`, and the boundary value
itself), for the same reason `GridSearchRate.lean` falls short of `1/4`:
a flat/uniform-bound union argument at a single shrinking radius cannot
reach the exact boundary rate, only every rate strictly below it.

## `grid_argmax_increment_rate`: the full `O_p(N^{-1/2})`, stated and honestly `sorry`'d

Reaching the exact rate (not just every `γ < 1/2`) needs dyadic annulus
peeling at the rate-relevant radius `r_N = M/√N`: on annulus `j`
(`2^j r_N ≤ rθ < 2^{j+1} r_N`), both the drift and the calibrated
threshold become `N`-independent (`Θ(M²4^j)`, `Θ(M2^j)`), giving a
per-point tail bound `exp(-β4^j)` whose decay must be checked against a
per-annulus POINT COUNT — which the flat `hGcard` cannot supply (it has
no information about how points distribute across radii). This needs a
genuine local-density hypothesis (`hGdensity : ∀ r, |{θ ∈ G N :
|θ-θ0|≤r}| ≤ C√N r + C`, strictly stronger than `hGcard`) plus a
geometric-series summation over `j : ℕ`. The theorem below states this
precisely, with `hGdensity` as an explicit hypothesis and the target
`O_p` conclusion in closed `Cfin·exp(-κfin·M²)` form, but is marked
`sorry` — the missing step (bounding a series that is simultaneously
polynomial and doubly-exponential in `j`, plus a genuine "`M` past a
fixed structural threshold" case split) is comparable in scope to this
project's other open, well-scoped follow-on items (`CLAUDE.md` "Open
work"), and is left as real, precisely-characterized future work rather
than attempted at risk of an incomplete or silently-wrong proof — see
the theorem's own docstring for the exact missing step. The
polynomial-rate result above is what's delivered, fully proved, 0
`sorry`.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

namespace KNOMP

open MeasureTheory Filter Topology
open scoped ENNReal Topology

/-- **Shrinking-radius consistency of a grid-search argmax under
increment concentration, at any polynomial rate below `N^{-1/2}`.**
See the file header for the exact signal-to-noise calculation and for
why this reaches `γ < 1/2` (compare `grid_argmax_polynomial_rate`'s
`γ < 1/4` in `GridSearchRate.lean`) but not the paper's literal
`O_p(N^{-1/2})` claim. -/
theorem grid_argmax_increment_polynomial_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (G : ℕ → Finset ℝ) (g : ℕ → ℝ → Ω → ℝ) (μ : ℕ → ℝ → ℝ) (θ0 : ℝ)
    (θhat_grid : ℕ → Ω → ℝ)
    (C σ L : ℝ) (hC : 0 < C) (hσ : 0 < σ) (hL : 0 < L)
    (hθ0mem : ∀ N, θ0 ∈ G N)
    (hargmax : ∀ N ω, θhat_grid N ω ∈ G N ∧ ∀ θ ∈ G N, g N θ ω ≤ g N (θhat_grid N ω) ω)
    (hGcard : ∀ᶠ N : ℕ in atTop, ((G N).card : ℝ) ≤ C * Real.sqrt N)
    (hinc : ∀ N : ℕ, ∀ θ θ' : ℝ, ∀ x : ℝ, 0 < x →
      (P : Measure Ω) {ω | x * Real.sqrt N * |θ - θ'| ≤
          |(g N θ ω - g N θ' ω) - (μ N θ - μ N θ')|} ≤
        ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2))))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 1 / 2)
    (c1 : ℝ) (hc1 : 0 < c1)
    (hdrift : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ G N, μ N θ ≤ μ N θ0 - c1 * N * (θ - θ0) ^ 2) :
    Tendsto (fun N : ℕ => (P : Measure Ω) {ω | (N : ℝ) ^ (-γ) ≤ |θhat_grid N ω - θ0|})
      atTop (𝓝 0) := by
  set κ : ℝ := c1 ^ 2 / (8 * σ ^ 2 * L ^ 2) with hκdef
  have hκpos : 0 < κ := by positivity
  set α : ℝ := 1 - 2 * γ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; linarith
  have hbound : ∀ᶠ N : ℕ in atTop,
      (P : Measure Ω) {ω | (N : ℝ) ^ (-γ) ≤ |θhat_grid N ω - θ0|} ≤
        ENNReal.ofReal (2 * C * Real.sqrt N * Real.exp (-κ * (N : ℝ) ^ α)) := by
    filter_upwards [hdrift, hGcard, eventually_ge_atTop 1] with N hdriftN hGcardN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    set r : ℝ := (N : ℝ) ^ (-γ) with hrdef
    have hrpos : 0 < r := by rw [hrdef]; positivity
    have e1 : (N : ℝ) * r ^ 2 = (N : ℝ) ^ α := by
      rw [hrdef, hαdef, ← Real.rpow_natCast ((N : ℝ) ^ (-γ)) 2,
        ← Real.rpow_mul hNpos.le]
      rw [show (1 : ℝ) - 2 * γ = 1 + (-γ * 2) by ring, Real.rpow_add hNpos, Real.rpow_one]
      norm_num
    set S : Finset ℝ := (G N).filter (fun θ => r ≤ |θ - θ0|) with hSdef
    have hsubset1 : {ω | r ≤ |θhat_grid N ω - θ0|} ⊆
        ⋃ θ ∈ S, {ω | g N θ0 ω ≤ g N θ ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      obtain ⟨hmem, hmax⟩ := hargmax N ω
      have hle : g N θ0 ω ≤ g N (θhat_grid N ω) ω := hmax θ0 (hθ0mem N)
      simp only [Set.mem_iUnion]
      exact ⟨θhat_grid N ω, Finset.mem_filter.mpr ⟨hmem, hω⟩, hle⟩
    have hperθ : ∀ θ ∈ S,
        (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
          ENNReal.ofReal (2 * Real.exp (-κ * (N : ℝ) ^ α)) := by
      intro θ hθ
      obtain ⟨hθG, hθr⟩ := Finset.mem_filter.mp hθ
      set rθ : ℝ := |θ - θ0| with hrθdef
      have hrθpos : 0 < rθ := lt_of_lt_of_le hrpos hθr
      set x : ℝ := c1 * Real.sqrt N * rθ / 2 with hxdef
      have hxpos : 0 < x := by positivity
      have hdrift_θ : μ N θ ≤ μ N θ0 - c1 * N * rθ ^ 2 := by
        have := hdriftN θ hθG
        rwa [← sq_abs (θ - θ0)] at this
      have hxeq : x * Real.sqrt N * rθ = c1 * N * rθ ^ 2 / 2 := by
        rw [hxdef]
        have : c1 * Real.sqrt N * rθ / 2 * Real.sqrt N * rθ
            = c1 * (Real.sqrt N * Real.sqrt N) * (rθ * rθ) / 2 := by ring
        rw [this, hsqN, sq]
      have hsub : {ω | g N θ0 ω ≤ g N θ ω} ⊆
          {ω | x * Real.sqrt N * rθ ≤
              |(g N θ ω - g N θ0 ω) - (μ N θ - μ N θ0)|} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        by_contra hcon
        push_neg at hcon
        rw [abs_lt] at hcon
        rw [hxeq] at hcon
        linarith [hcon.2, hdrift_θ]
      have hr2 : r ^ 2 ≤ rθ ^ 2 := by
        have h0 : (0 : ℝ) ≤ r := hrpos.le
        have h1 : (0 : ℝ) ≤ rθ := le_trans h0 hθr
        calc r ^ 2 = r * r := sq r
          _ ≤ rθ * rθ := mul_le_mul hθr hθr h0 h1
          _ = rθ ^ 2 := (sq rθ).symm
      have hexp_le : Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2)) ≤ Real.exp (-κ * (N : ℝ) ^ α) := by
        apply Real.exp_le_exp.mpr
        have hNsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
        have hx2 : x ^ 2 = c1 ^ 2 * (N : ℝ) * rθ ^ 2 / 4 := by
          rw [hxdef, show (c1 * Real.sqrt (N : ℝ) * rθ / 2) ^ 2
              = c1 ^ 2 * (Real.sqrt (N : ℝ)) ^ 2 * rθ ^ 2 / 4 from by ring, hNsq]
        have hxsq : x ^ 2 / (2 * σ ^ 2 * L ^ 2) = κ * (N : ℝ) * rθ ^ 2 := by
          rw [hx2, hκdef]
          field_simp
          ring
        have hmono : κ * (N : ℝ) * r ^ 2 ≤ κ * (N : ℝ) * rθ ^ 2 :=
          mul_le_mul_of_nonneg_left hr2 (by positivity)
        have hkey : κ * (N : ℝ) ^ α ≤ x ^ 2 / (2 * σ ^ 2 * L ^ 2) := by
          rw [hxsq, ← e1]
          nlinarith [hmono]
        rw [neg_div, neg_mul]
        linarith [hkey]
      calc (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω}
          ≤ (P : Measure Ω) {ω | x * Real.sqrt N * rθ ≤
              |(g N θ ω - g N θ0 ω) - (μ N θ - μ N θ0)|} := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2))) := hinc N θ θ0 x hxpos
        _ ≤ ENNReal.ofReal (2 * Real.exp (-κ * (N : ℝ) ^ α)) :=
            ENNReal.ofReal_le_ofReal (by linarith [hexp_le])
    have hunion : (P : Measure Ω) {ω | r ≤ |θhat_grid N ω - θ0|} ≤
        ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} :=
      (measure_mono hsubset1).trans (measure_biUnion_finset_le S _)
    have hsum_le : ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
        S.card • ENNReal.ofReal (2 * Real.exp (-κ * (N : ℝ) ^ α)) :=
      Finset.sum_le_card_nsmul S _ _ hperθ
    have hcardS : (S.card : ℝ) ≤ C * Real.sqrt N :=
      le_trans (by exact_mod_cast Finset.card_filter_le (G N) _) hGcardN
    have hnsmul_eq : S.card • ENNReal.ofReal (2 * Real.exp (-κ * (N : ℝ) ^ α)) =
        ENNReal.ofReal ((S.card : ℝ) * (2 * Real.exp (-κ * (N : ℝ) ^ α))) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hcard_bound : ENNReal.ofReal ((S.card : ℝ) * (2 * Real.exp (-κ * (N : ℝ) ^ α))) ≤
        ENNReal.ofReal (2 * C * Real.sqrt N * Real.exp (-κ * (N : ℝ) ^ α)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp_nonneg : (0 : ℝ) ≤ 2 * Real.exp (-κ * (N : ℝ) ^ α) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcardS hexp_nonneg]
    calc (P : Measure Ω) {ω | r ≤ |θhat_grid N ω - θ0|}
        ≤ ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} := hunion
      _ ≤ S.card • ENNReal.ofReal (2 * Real.exp (-κ * (N : ℝ) ^ α)) := hsum_le
      _ = ENNReal.ofReal ((S.card : ℝ) * (2 * Real.exp (-κ * (N : ℝ) ^ α))) := hnsmul_eq
      _ ≤ ENNReal.ofReal (2 * C * Real.sqrt N * Real.exp (-κ * (N : ℝ) ^ α)) := hcard_bound
  have hupper : Tendsto (fun N : ℕ => ENNReal.ofReal (2 * C * Real.sqrt N * Real.exp (-κ * (N : ℝ) ^ α)))
      atTop (𝓝 0) := by
    have hcomp : Tendsto (fun x : ℝ => (x ^ α) ^ (1 / (2 * α) : ℝ) * Real.exp (-κ * x ^ α))
        atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / (2 * α)) κ hκpos).comp
        (tendsto_rpow_atTop hαpos)
    have heq : (fun x : ℝ => (x ^ α) ^ (1 / (2 * α) : ℝ) * Real.exp (-κ * x ^ α))
        =ᶠ[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.exp (-κ * x ^ α)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      congr 1
      rw [← Real.rpow_mul hx]
      congr 1
      field_simp [hαpos.ne']
    have hfinal : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.exp (-κ * x ^ α)) atTop (𝓝 0) :=
      hcomp.congr' heq
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * (N : ℝ) ^ α)) atTop (𝓝 0) :=
      hfinal.comp tendsto_natCast_atTop_atTop
    have h2 : (fun N : ℕ => 2 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * (N : ℝ) ^ α))
        = fun N : ℕ => 2 * C * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * (N : ℝ) ^ α)) := by
      funext N
      rw [Real.sqrt_eq_rpow]
      ring
    have h3 : Tendsto (fun N : ℕ => 2 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * (N : ℝ) ^ α))
        atTop (𝓝 (2 * C * 0)) := by
      rw [h2]
      exact h1.const_mul (2 * C)
    rw [mul_zero] at h3
    have h4 := ENNReal.tendsto_ofReal h3
    simpa using h4
  have hlower : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (Eventually.of_forall (fun N => by simp)) hbound

/-- **The paper's literal target: `O_p(N^{-1/2})` consistency of the grid
argmax under increment concentration and a local grid-density bound.**

Unlike `grid_argmax_increment_polynomial_rate` above (which fixes `γ`
first and only needs the flat cardinality bound `hGcard`), reaching the
exact boundary rate needs the calibration to work simultaneously across
EVERY radius `r ≥ M/√N` at once, at a fixed `M` — and the naive
"collapse to a single uniform per-point bound" trick used above provably
fails here: at `r_N = M/√N`, the per-point exponent `κ·N·r_N² = κM²` is
`N`-independent, so a flat count bound `|S| ≤ C√N` forces the total union
bound `C√N·exp(-κM²) → ∞`, not `→ 0`. The fix is dyadic annulus peeling:
partition `S := {θ ∈ G N : M/√N ≤ |θ-θ0|}` into layers
`Sⱼ := {θ ∈ G N : 2^j·M/√N ≤ |θ-θ0| < 2^(j+1)·M/√N}` (`j : ℕ`). On layer
`j`, using the SAME per-point calibration as `grid_argmax_increment_
polynomial_rate` but at the layer's own inner radius, the tail bound
becomes the `N`-INDEPENDENT number `exp(-κ·M²·4^j)` for every point in
the layer. This is where `hGdensity` below (replacing the flat `hGcard`)
is essential: it bounds `|Sⱼ|` by the also-`N`-independent quantity
`C·M·2^(j+1) + C`, so the whole per-layer contribution
`(C·M·2^(j+1)+C)·exp(-κM²4^j)` is `N`-independent, and — this is the
crux step not yet carried out — summing this over `j : ℕ` is a genuine
convergent series (the `4^j` in the exponent eventually dominates the
`2^j` prefactor for any fixed `M > 0`, once `M` clears a fixed structural
threshold `M0` not depending on the target error `ε`), giving a total
bound of the claimed `Cfin·exp(-κfin·M²)` shape — sufficient for `O_p`
since letting `M → ∞` drives it to `0` independent of `N`.

**Why this is left `sorry`, not attempted further this session:** the
per-layer tail bound and the `hGdensity`-based per-layer count bound are
each individually routine repeats of `grid_argmax_increment_polynomial_
rate`'s own per-point argument (just localized to a dyadic shell instead
of a half-line `{rθ ≥ r}`); what is NOT routine is the subsequent
`∑ j : ℕ, (C·M·2^(j+1)+C)·exp(-κM²4^j)` bound itself — bounding a series
whose terms are simultaneously polynomial (`2^j`) and doubly-exponential
(`exp(-const·4^j)`) in `j` by a clean, `M`-uniform closed form is a
genuine additional real-analysis lemma this project has no counterpart
for (nothing here resembles `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_
zero`, which is a single-exponential, not doubly-exponential, decay
statement), together with the bookkeeping to handle "annulus peeling only
provably closes for `M ≥ M0`" as a genuinely separate case from "`M < M0`"
in the final `O_p` argument. This is comparable in scope to the CLT gap
`CLAUDE.md`'s "Open work" item 2 already flags, not a routine extension
of what's above — hence stated concretely here (rather than left as
untouched prose) and marked `sorry`, per house rule 1/2, instead of
attempted at risk of an incomplete or silently-wrong proof. -/
theorem grid_argmax_increment_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (G : ℕ → Finset ℝ) (g : ℕ → ℝ → Ω → ℝ) (μ : ℕ → ℝ → ℝ) (θ0 : ℝ)
    (θhat_grid : ℕ → Ω → ℝ)
    (C σ L : ℝ) (hC : 0 < C) (hσ : 0 < σ) (hL : 0 < L)
    (hθ0mem : ∀ N, θ0 ∈ G N)
    (hargmax : ∀ N ω, θhat_grid N ω ∈ G N ∧ ∀ θ ∈ G N, g N θ ω ≤ g N (θhat_grid N ω) ω)
    (hGdensity : ∀ᶠ N : ℕ in atTop, ∀ ρ : ℝ, 0 < ρ →
      (((G N).filter (fun θ => |θ - θ0| ≤ ρ)).card : ℝ) ≤ C * Real.sqrt N * ρ + C)
    (hinc : ∀ N : ℕ, ∀ θ θ' : ℝ, ∀ x : ℝ, 0 < x →
      (P : Measure Ω) {ω | x * Real.sqrt N * |θ - θ'| ≤
          |(g N θ ω - g N θ' ω) - (μ N θ - μ N θ')|} ≤
        ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * σ ^ 2 * L ^ 2))))
    (c1 : ℝ) (hc1 : 0 < c1)
    (hdrift : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ G N, μ N θ ≤ μ N θ0 - c1 * N * (θ - θ0) ^ 2) :
    ∃ Cfin κfin : ℝ, 0 < Cfin ∧ 0 < κfin ∧
      ∀ M : ℝ, 0 < M →
        ∀ᶠ N : ℕ in atTop,
          (P : Measure Ω) {ω | M / Real.sqrt N ≤ |θhat_grid N ω - θ0|} ≤
            ENNReal.ofReal (Cfin * Real.exp (-κfin * M ^ 2)) := by
  sorry

end KNOMP
