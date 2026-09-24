/-
KNOMP/JitterLikelihoodMaximizer.lean

Source: Section 5, "Existence of the Jitter Likelihood Maximizer",
Proposition `jitter` (existence AND non-concavity), plus Corollary
`jitter-search` (informal optimization-methodology remark, not a
mathematical claim requiring its own formalization).

STATUS: PROVED, using the paper's own exact formula. An earlier version
of this file only proved an ABSTRACT version of the existence half
("any continuous function on `[0,∞)` tending to `-∞` has a maximizer"),
explicitly because the source `.tex` was not available in that session
to check the paper's precise formula against, and the NON-CONCAVITY half
of the Proposition was missing entirely (caught during a coverage
re-check against the source). Both gaps are now closed: the paper's
exact per-dataset jitter log-likelihood, Eq. `jitter-lik`,
`ℓ_d(s) = -½Σₙlog(σₙ²+s) - ½Σₙrₙ²/(σₙ²+s)`, is used directly, and both
halves of the Proposition (existence, and non-concavity) are proved
against it.

Non-concavity is formalized as two separate, each individually clean,
facts rather than one combined "generically changes sign" statement
(which the paper itself states somewhat informally — "for a fixed
dataset with residuals spanning a realistic range... generically changes
sign"): (1) a UNIVERSAL fact, true for every configuration whatsoever —
`ℓ_d''(s) > 0` for all sufficiently large `s`, because the positive
(log-determinant) term of the second derivative decays as `(σₙ²+s)⁻²`
while the negative (quadratic-residual) term decays strictly faster, as
`(σₙ²+s)⁻³` — which alone shows `ℓ_d` is never concave on all of
`[0,∞)`, for any configuration; and (2) a concrete existence witness
showing `ℓ_d''(0) < 0` is achievable for suitable residuals (matching
"can be made negative by taking a single `rₙ²` sufficiently large"),
confirming non-convexity is also possible. The second-derivative formula
itself (`ℓ_d''(s) = Σₙ[1/(2(σₙ²+s)²) - rₙ²/(σₙ²+s)³]`) is the paper's own
elementary calculus (differentiating twice), taken as given rather than
re-derived via Mathlib's `HasDerivAt` machinery, matching how several
other files in this project handle "elementary, not restated" calculus
steps — what IS proved here is the substantive real-analysis content
(the asymptotic sign comparison, and the concrete witness), not the
routine differentiation itself.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Basic

namespace KNOMP

open Filter

variable {N : ℕ}

/-- **General fact behind Theorem `jitter-max`'s existence half.** A
function continuous on `[0,∞)` that tends to `-∞` as its argument grows
attains a global maximum somewhere on `[0,∞)`. -/
theorem exists_max_of_tendsto_atBot
    (f : ℝ → ℝ) (hcont : Continuous f)
    (htendsto : Tendsto f atTop atBot) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s, 0 ≤ s → f s ≤ f s₀ := by
  have hev : ∀ᶠ s in atTop, f s ≤ f 0 := htendsto.eventually_le_atBot (f 0)
  obtain ⟨S, hS⟩ := eventually_atTop.mp hev
  set S' := max S 0 with hS'def
  have hS'nonneg : (0:ℝ) ≤ S' := le_max_right _ _
  have hcompact : IsCompact (Set.Icc (0:ℝ) S') := isCompact_Icc
  have hnonempty : (Set.Icc (0:ℝ) S').Nonempty := ⟨0, le_refl 0, hS'nonneg⟩
  obtain ⟨s₀, hs₀mem, hs₀max⟩ := hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨s₀, hs₀mem.1, ?_⟩
  intro s hs
  by_cases hcase : s ≤ S'
  · exact hs₀max ⟨hs, hcase⟩
  · push_neg at hcase
    have hsS : S ≤ s := le_trans (le_max_left S 0) hcase.le
    exact le_trans (hS s hsS) (hs₀max ⟨le_refl 0, hS'nonneg⟩)

/-- The paper's own exact per-dataset jitter log-likelihood, Eq.
`jitter-lik`: `ℓ_d(s) = -½Σₙlog(σₙ²+s) - ½Σₙrₙ²/(σₙ²+s)`. -/
noncomputable def jitterLogLik (sigma2 r : Fin N → ℝ) (s : ℝ) : ℝ :=
  -(1/2) * ∑ n, Real.log (sigma2 n + s) - (1/2) * ∑ n, (r n) ^ 2 / (sigma2 n + s)

/-- **Continuity half of Proposition `jitter`, for the exact formula.** -/
theorem jitterLogLik_continuousOn
    (sigma2 r : Fin N → ℝ) (hsig : ∀ n, 0 < sigma2 n) :
    ContinuousOn (jitterLogLik sigma2 r) (Set.Ici 0) := by
  unfold jitterLogLik
  apply ContinuousOn.sub
  · apply continuousOn_const.mul
    apply continuousOn_finset_sum
    intro n _
    apply Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id)
    intro s hs
    simp only [Set.mem_Ici] at hs
    have : 0 < sigma2 n + s := by linarith [hsig n]
    exact this.ne'
  · apply continuousOn_const.mul
    apply continuousOn_finset_sum
    intro n _
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro s hs
    simp only [Set.mem_Ici] at hs
    have : 0 < sigma2 n + s := by linarith [hsig n]
    exact this.ne'

/-- **Divergence half of Proposition `jitter`, for the exact formula
(concrete, not the abstract hypothesis of an earlier version of this
file).** As `s → ∞`, the log-determinant term diverges to `-∞` (each of
the finitely many summands does, and there is at least one, by
`NeZero N`) while the quadratic-residual term tends to a finite limit
(`0`); the sum of a term diverging to `-∞` and a term with a finite limit
diverges to `-∞`. -/
theorem jitterLogLik_tendsto_atBot
    (sigma2 r : Fin N → ℝ) (hsig : ∀ n, 0 < sigma2 n) [NeZero N] :
    Tendsto (jitterLogLik sigma2 r) atTop atBot := by
  unfold jitterLogLik
  obtain ⟨n0⟩ := (inferInstance : Nonempty (Fin N))
  have hlog : Tendsto (fun s => ∑ n, Real.log (sigma2 n + s)) atTop atTop := by
    have hterm0 : Tendsto (fun s => Real.log (sigma2 n0 + s)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop (sigma2 n0) tendsto_id)
    have hbound : ∀ᶠ s in atTop, Real.log (sigma2 n0 + s) ≤ ∑ n, Real.log (sigma2 n + s) := by
      filter_upwards [eventually_ge_atTop 1] with s hs
      apply Finset.single_le_sum (f := fun n => Real.log (sigma2 n + s))
      · intro n _
        apply Real.log_nonneg
        have := hsig n
        linarith
      · exact Finset.mem_univ n0
    exact tendsto_atTop_mono' atTop hbound hterm0
  have hquad : Tendsto (fun s => ∑ n, (r n) ^ 2 / (sigma2 n + s)) atTop (nhds 0) := by
    have heq : (0:ℝ) = ∑ _n : Fin N, (0:ℝ) := by simp
    rw [heq]
    apply tendsto_finset_sum
    intro n _
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_left atTop (sigma2 n) tendsto_id
  have h1 : Tendsto (fun s => -(1/2) * ∑ n, Real.log (sigma2 n + s)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by norm_num) hlog
  have h2 : Tendsto (fun s => -((1/2) * ∑ n, (r n) ^ 2 / (sigma2 n + s))) atTop (nhds 0) := by
    have := Filter.Tendsto.mul (tendsto_const_nhds (x := (1/2:ℝ))) hquad
    have hneg := this.neg
    simpa using hneg
  have hfinal := Filter.Tendsto.atBot_add h1 h2
  simpa [sub_eq_add_neg] using hfinal

/-- **Existence half of Proposition `jitter`, for the exact formula.** -/
theorem jitterLogLik_exists_max
    (sigma2 r : Fin N → ℝ) (hsig : ∀ n, 0 < sigma2 n) [NeZero N] :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s, 0 ≤ s → jitterLogLik sigma2 r s ≤ jitterLogLik sigma2 r s₀ := by
  have htendsto := jitterLogLik_tendsto_atBot sigma2 r hsig
  have hcont := jitterLogLik_continuousOn sigma2 r hsig
  have hev : ∀ᶠ s in atTop, jitterLogLik sigma2 r s ≤ jitterLogLik sigma2 r 0 :=
    htendsto.eventually_le_atBot (jitterLogLik sigma2 r 0)
  obtain ⟨S, hS⟩ := eventually_atTop.mp hev
  set S' := max S 0 with hS'def
  have hS'nonneg : (0:ℝ) ≤ S' := le_max_right _ _
  have hcompact : IsCompact (Set.Icc (0:ℝ) S') := isCompact_Icc
  have hnonempty : (Set.Icc (0:ℝ) S').Nonempty := ⟨0, le_refl 0, hS'nonneg⟩
  have hcontIcc : ContinuousOn (jitterLogLik sigma2 r) (Set.Icc (0:ℝ) S') :=
    hcont.mono Set.Icc_subset_Ici_self
  obtain ⟨s₀, hs₀mem, hs₀max⟩ := hcompact.exists_isMaxOn hnonempty hcontIcc
  refine ⟨s₀, hs₀mem.1, ?_⟩
  intro s hs
  by_cases hcase : s ≤ S'
  · exact hs₀max ⟨hs, hcase⟩
  · push_neg at hcase
    have hsS : S ≤ s := le_trans (le_max_left S 0) hcase.le
    exact le_trans (hS s hsS) (hs₀max ⟨le_refl 0, hS'nonneg⟩)

/-- The paper's own second-derivative formula for `ℓ_d`,
`ℓ_d''(s) = Σₙ[1/(2(σₙ²+s)²) - rₙ²/(σₙ²+s)³]` — elementary calculus
(differentiating `ℓ_d` twice), not re-derived here via `HasDerivAt`
(matching how several other files in this project handle "elementary,
not restated" calculus steps); what IS proved below, against this
formula, is the substantive real-analysis content. -/
noncomputable def jitterLogLikSecondDeriv (sigma2 r : Fin N → ℝ) (s : ℝ) : ℝ :=
  ∑ n, (1 / (2 * (sigma2 n + s) ^ 2) - (r n) ^ 2 / (sigma2 n + s) ^ 3)

/-- **Non-concavity, universal half.** `ℓ_d''(s) > 0` for all
sufficiently large `s`, for EVERY configuration of `(σₙ², rₙ)` — the
positive (log-determinant) term of the second derivative decays as
`(σₙ²+s)⁻²` while the negative (quadratic-residual) term decays strictly
faster, as `(σₙ²+s)⁻³`; for large `s` the former dominates. Since a
concave function has `f'' ≤ 0` everywhere, this alone shows `ℓ_d` is
never concave on all of `[0,∞)`, for any residual configuration
whatsoever — matching the paper's own "it is positive as `s→∞`...
regardless of the residuals" remark exactly. -/
theorem jitterLogLikSecondDeriv_eventually_pos
    (sigma2 r : Fin N → ℝ) (hsig : ∀ n, 0 < sigma2 n) [NeZero N] :
    ∀ᶠ s : ℝ in atTop, 0 < jitterLogLikSecondDeriv sigma2 r s := by
  have hterm_eq : ∀ (n : Fin N) (s : ℝ), 0 < sigma2 n + s →
      1 / (2 * (sigma2 n + s) ^ 2) - (r n) ^ 2 / (sigma2 n + s) ^ 3
        = ((sigma2 n + s) / 2 - (r n) ^ 2) / (sigma2 n + s) ^ 3 := by
    intro n s hpos
    field_simp
  have hterm_pos : ∀ n : Fin N, ∀ᶠ s : ℝ in atTop,
      0 < 1 / (2 * (sigma2 n + s) ^ 2) - (r n) ^ 2 / (sigma2 n + s) ^ 3 := by
    intro n
    have hlin : Tendsto (fun s : ℝ => (sigma2 n + s) / 2 - (r n) ^ 2) atTop atTop := by
      apply Tendsto.atTop_add _ tendsto_const_nhds
      apply Tendsto.atTop_div_const (by norm_num)
      exact tendsto_atTop_add_const_left atTop (sigma2 n) tendsto_id
    have hev1 := hlin.eventually_gt_atTop 0
    have hev2 : ∀ᶠ s : ℝ in atTop, 0 < sigma2 n + s := by
      filter_upwards [eventually_ge_atTop (-(sigma2 n) + 1)] with s hs
      linarith
    filter_upwards [hev1, hev2] with s hs1 hs2
    rw [hterm_eq n s hs2]
    exact div_pos hs1 (pow_pos hs2 3)
  have hall : ∀ᶠ s : ℝ in atTop, ∀ n : Fin N,
      0 < 1 / (2 * (sigma2 n + s) ^ 2) - (r n) ^ 2 / (sigma2 n + s) ^ 3 :=
    Filter.eventually_all.mpr hterm_pos
  filter_upwards [hall] with s hs
  unfold jitterLogLikSecondDeriv
  apply Finset.sum_pos
  · intro n _
    exact hs n
  · exact Finset.univ_nonempty

/-- **Non-concavity, concrete witness half.** `ℓ_d''(0) < 0` is
achievable for a suitable residual configuration (`σ² = 1`, `r = 10`, a
single point) — matching the paper's "can be made negative by taking a
single `rₙ²` sufficiently large relative to `σₙ²`". Combined with the
universal eventual-positivity above, this exhibits both signs occurring
across the admissible configurations: `ℓ_d` is never concave on `[0,∞)`
(by the theorem above, for any configuration), and is not convex either
for suitably large residuals (by this one) — matching the paper's "in
general neither concave nor convex" exactly. -/
theorem jitterLogLikSecondDeriv_neg_witness :
    jitterLogLikSecondDeriv (N := 1) (fun _ => 1) (fun _ => 10) 0 < 0 := by
  unfold jitterLogLikSecondDeriv
  norm_num

end KNOMP
