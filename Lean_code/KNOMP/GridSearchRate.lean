/-
KNOMP/GridSearchRate.lean

PURPOSE: follow-on to `GridSearchConcentration.lean`, attempting "step 7"
of `AsymptoticEfficiency.lean`'s `lemma_grid_accuracy` (paper Section 7,
`lem:grid-accuracy`, `.tex` lines 1067-1173): upgrading fixed-radius
consistency (`grid_argmax_consistency`) toward the paper's literal rate
claim `θ̂_grid - θ0 = O_p(N^{-1/2})`.

STATUS: 0 `sorry`, 0 `axiom`. Does NOT reach the paper's `N^{-1/2}` rate
— see "MID-SESSION FINDING" below for exactly why, checked by hand
before any Lean was written, per CLAUDE.md house rule 3. What this file
DOES deliver, fully proved: `grid_argmax_polynomial_rate`, a genuine
strengthening of `grid_argmax_consistency` from a FIXED radius to any
POLYNOMIALLY SHRINKING radius `N^{-γ}` for every `γ < 1/4`.

## MID-SESSION FINDING: why the paper's own step-7 sketch, read literally,
does not prove the rate, and why `N^{-1/4}` (not `N^{-1/2}`) is the wall
for this proof technique

The originally-planned approach (see the plan this file's governing
session started from) was a dyadic-annulus peeling argument directly at
the rate-relevant radius `r_N = M/√N`: split `{θ : r_N ≤ |θ-θ0|}` into
annuli `A_j = {θ : 2^j r_N ≤ |θ-θ0| < 2^{j+1} r_N}`, bound each annulus's
failure probability via the SAME per-point argument
`grid_argmax_consistency` uses (concentration of `g N θ` around `μ N θ`
at both `θ` and `θ0`, forced apart by the deterministic drift), and sum a
geometric tail.

Working the per-annulus bound through by hand (not just restating the
paper's prose) exposes a genuine obstruction. On annulus `A_j`, the
drift is `Δ_j := c1 * N * (2^j r_N)² = c1 * M² * 4^j` — `N`-independent,
as the plan anticipated. But the per-point concentration argument
(`hsubset2`/`hperθ` in `GridSearchConcentration.lean`) can only ever use
a deviation threshold `x_j ≤ Δ_j / 2` (that's the largest split of the
drift between the two triangle-inequality events that still forces a
contradiction) — so `x_j` is *also* `O(1)` in `N` at this radius. But
`hconc`'s concentration bound has variance scale `Θ(N)` (that's what
makes `x = Θ(N)` give exponent `Θ(1)` at the *fixed*-radius scale in
`grid_argmax_consistency`): an `O(1)` threshold against an `O(√N)` noise
scale gives an exponent `x_j² / N = O(1/N) → 0`, i.e. the per-point bound
`2 exp(-x_j²/(2σ²L²N)) → 2`, useless, for *every* `j`, *no matter how the
union is sliced*. Concretely: solving for the radius `r` at which
`x(r) := c1 N r² / 2` is itself `Θ(√N)` (the minimum needed for a
non-vanishing per-point bound) gives `r = Θ(N^{-1/4})`, not `Θ(N^{-1/2})`.
This is not a defect of the peeling idea specifically — ANY reorganization
of the SAME marginal, per-point concentration hypothesis (`hconc`, which
only controls `g N θ` against its own mean at a single fixed `θ`) hits
this identical wall, because the wall is a signal-to-noise statement, not
a union-bound bookkeeping issue. (This also explains, in hindsight, why
the paper's own text at `.tex` ~1160 — "the `Θ(NΔ_N²) = Θ(1)`-order local
curvature term dominates the `Θ(√(N log N))` deviation bound" — doesn't
actually hold as a literal inequality: `Θ(1)` does not dominate
`Θ(√(N log N))`. The paper's step 7 is a hand-waved sketch at exactly
this point, not a rigorous derivation from the hypotheses stated earlier
in the section.)

This is also *not* surprising as a piece of general M-estimation theory:
crude two-step "quantize + union bound" arguments of exactly this shape
are well known to deliver a suboptimal polynomial rate rather than the
sharp `√N` rate; reaching the sharp rate genuinely needs a different,
stronger tool — controlling the INCREMENT process `θ ↦ g N θ - g N θ'`
directly (a modulus-of-continuity / chaining argument over a Gaussian- or
sub-Gaussian-type process, e.g. van der Vaart & Wellner's rate theorems
for M-estimators), not a per-point marginal concentration hypothesis
peeled over annuli. `hconc` as stated (and as inherited from
`GridSearchConcentration.lean`) does not capture increment structure at
all, so this file does not attempt to state or use such a hypothesis —
doing so honestly would require deriving or positing a materially
different, KNOMP-specific fact (e.g. from the actual linear-in-noise
structure of `ρ_W(f(θ))`, which lives in other sections of the paper, not
in this file's paper-structure-agnostic abstraction) rather than a clean
reusable primitive, and is left as real, well-scoped follow-on work (see
`CLAUDE.md` "Open work").

## What this file proves instead

`grid_argmax_polynomial_rate`: for any FIXED `γ` with `0 < γ < 1/4`, the
grid argmax's probability of being farther than `N^{-γ}` from `θ0` tends
to `0` as `N → ∞` — i.e. `θ̂_grid - θ0 = o_p(N^{-γ})` for every such `γ`.
This is a genuine strengthening of `grid_argmax_consistency` (radius now
shrinks to `0`, not just fixed) via the *identical* proof technique (no
peeling/annuli needed at all — a single shrinking radius suffices, since
unlike the rate-relevant `N^{-1/2}` scale, `N^{1-4γ} → ∞` for `γ < 1/4`,
which is exactly what keeps the union bound's exponential decay beating
its polynomial `√N` prefactor). It is still strictly short of the paper's
`O_p(N^{-1/2})` claim: `γ` can be pushed arbitrarily close to, but never
reaches, `1/4`.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

namespace KNOMP

open MeasureTheory Filter Topology
open scoped ENNReal Topology

/-- **Shrinking-radius consistency of a grid-search argmax, at any
polynomial rate below `N^{-1/4}`.** Same hypothesis shape as
`grid_argmax_consistency` (`GridSearchConcentration.lean`), with the
fixed radius `r0` replaced by the shrinking sequence `(N:ℝ)^(-γ)`. See
this file's header for exactly how far this technique reaches (`γ < 1/4`)
and why it cannot be pushed to the paper's `γ = 1/2`. -/
theorem grid_argmax_polynomial_rate
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
    (γ : ℝ) (hγ0 : 0 < γ) (hγ4 : γ < 1 / 4)
    (c1 : ℝ) (hc1 : 0 < c1)
    (hdrift : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ G N,
        (N : ℝ) ^ (-γ) ≤ |θ - θ0| → μ N θ ≤ μ N θ0 - c1 * N * ((N : ℝ) ^ (-γ)) ^ 2) :
    Tendsto (fun N : ℕ => (P : Measure Ω) {ω | (N : ℝ) ^ (-γ) ≤ |θhat_grid N ω - θ0|})
      atTop (𝓝 0) := by
  set κ : ℝ := c1 ^ 2 / (8 * σ ^ 2 * L ^ 2) with hκdef
  have hκpos : 0 < κ := by positivity
  set α : ℝ := 1 - 4 * γ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; linarith
  have hbound : ∀ᶠ N : ℕ in atTop,
      (P : Measure Ω) {ω | (N : ℝ) ^ (-γ) ≤ |θhat_grid N ω - θ0|} ≤
        ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * (N : ℝ) ^ α)) := by
    filter_upwards [hdrift, hGcard, eventually_ge_atTop 1] with N hdriftN hGcardN hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    set r : ℝ := (N : ℝ) ^ (-γ) with hrdef
    have hrpos : 0 < r := by rw [hrdef]; positivity
    set x : ℝ := c1 * N * r ^ 2 / 2 with hxdef
    have hxpos : 0 < x := by positivity
    set S : Finset ℝ := (G N).filter (fun θ => r ≤ |θ - θ0|) with hSdef
    have hsubset1 : {ω | r ≤ |θhat_grid N ω - θ0|} ⊆
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
      obtain ⟨hθG, hθr⟩ := Finset.mem_filter.mp hθ
      have hdrift_θ : μ N θ ≤ μ N θ0 - c1 * N * r ^ 2 := hdriftN θ hθG hθr
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨hA, hB⟩ := hcon
      rw [abs_lt] at hA hB
      have hxeq2 : x = c1 * N * r ^ 2 / 2 := hxdef
      linarith [hA.1, hA.2, hB.1, hB.2]
    have hperθ : ∀ θ ∈ S,
        (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
          ENNReal.ofReal (4 * Real.exp (-κ * (N : ℝ) ^ α)) := by
      intro θ hθ
      have hxeq : x ^ 2 / (2 * σ ^ 2 * L ^ 2 * (N : ℝ)) = κ * (N : ℝ) ^ α := by
        have e1 : r ^ 4 = (N : ℝ) ^ (-γ * 4) := by
          rw [hrdef, ← Real.rpow_natCast ((N:ℝ) ^ (-γ)) 4, ← Real.rpow_mul (le_of_lt hNpos)]
          norm_num
        have e2 : (N : ℝ) ^ α = (N : ℝ) * (N : ℝ) ^ (-γ * 4) := by
          rw [hαdef, show (1:ℝ) - 4 * γ = 1 + (-γ * 4) by ring, Real.rpow_add hNpos,
            Real.rpow_one]
        have hNr4 : (N : ℝ) * r ^ 4 = (N : ℝ) ^ α := by rw [e2, e1]
        rw [hxdef, hκdef, ← hNr4]
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
        _ = ENNReal.ofReal (4 * Real.exp (-κ * (N : ℝ) ^ α)) := by
            have : -x ^ 2 / (2 * σ ^ 2 * L ^ 2 * (N : ℝ)) = -κ * (N:ℝ) ^ α := by
              rw [neg_div, hxeq]; ring
            rw [this]
    have hunion : (P : Measure Ω) {ω | r ≤ |θhat_grid N ω - θ0|} ≤
        ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} :=
      (measure_mono hsubset1).trans (measure_biUnion_finset_le S _)
    have hsum_le : ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} ≤
        S.card • ENNReal.ofReal (4 * Real.exp (-κ * (N:ℝ) ^ α)) :=
      Finset.sum_le_card_nsmul S _ _ hperθ
    have hcardS : (S.card : ℝ) ≤ C * Real.sqrt N :=
      le_trans (by exact_mod_cast Finset.card_filter_le (G N) _) hGcardN
    have hnsmul_eq : S.card • ENNReal.ofReal (4 * Real.exp (-κ * (N:ℝ) ^ α)) =
        ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * (N:ℝ) ^ α))) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hcard_bound : ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * (N:ℝ) ^ α))) ≤
        ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * (N:ℝ) ^ α)) := by
      apply ENNReal.ofReal_le_ofReal
      have hexp_nonneg : (0 : ℝ) ≤ 4 * Real.exp (-κ * (N:ℝ) ^ α) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcardS hexp_nonneg]
    calc (P : Measure Ω) {ω | r ≤ |θhat_grid N ω - θ0|}
        ≤ ∑ θ ∈ S, (P : Measure Ω) {ω | g N θ0 ω ≤ g N θ ω} := hunion
      _ ≤ S.card • ENNReal.ofReal (4 * Real.exp (-κ * (N:ℝ) ^ α)) := hsum_le
      _ = ENNReal.ofReal ((S.card : ℝ) * (4 * Real.exp (-κ * (N:ℝ) ^ α))) := hnsmul_eq
      _ ≤ ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * (N:ℝ) ^ α)) := hcard_bound
  have hupper : Tendsto (fun N : ℕ => ENNReal.ofReal (4 * C * Real.sqrt N * Real.exp (-κ * (N:ℝ) ^ α)))
      atTop (𝓝 0) := by
    have hcomp : Tendsto (fun x : ℝ => (x ^ α) ^ (1 / (2 * α) : ℝ) * Real.exp (-κ * x ^ α))
        atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / (2 * α)) κ hκpos).comp
        (tendsto_rpow_atTop hαpos)
    have heq : (fun x : ℝ => (x ^ α) ^ (1 / (2 * α) : ℝ) * Real.exp (-κ * x ^ α))
        =ᶠ[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.exp (-κ * x ^ α)) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      congr 1
      rw [← Real.rpow_mul hx]
      congr 1
      field_simp [hαpos.ne']
    have hfinal : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.exp (-κ * x ^ α)) atTop (𝓝 0) :=
      hcomp.congr' heq
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * (N:ℝ) ^ α)) atTop (𝓝 0) :=
      hfinal.comp tendsto_natCast_atTop_atTop
    have h2 : (fun N : ℕ => 4 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * (N:ℝ) ^ α))
        = fun N : ℕ => 4 * C * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-κ * (N:ℝ) ^ α)) := by
      funext N
      rw [Real.sqrt_eq_rpow]
      ring
    have h3 : Tendsto (fun N : ℕ => 4 * C * Real.sqrt (N : ℝ) * Real.exp (-κ * (N:ℝ) ^ α))
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
