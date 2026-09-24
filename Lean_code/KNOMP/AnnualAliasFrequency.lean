/-
KNOMP/AnnualAliasFrequency.lean

Source: Section 20, "The Annual-Alias Frequency Identity", Proposition
"Exact alias frequency under a strictly periodic sampling window", plus
its worked numerical remark.

STATUS: PROVED, via a reformulation that avoids distribution theory
entirely — see below for exactly what this does and does not capture
relative to the paper's own statement.

The paper's own argument is distributional (a periodic sampling window's
Fourier transform is a Dirac comb, by Poisson summation; convolving with
a single-tone signal's two Dirac masses moves them to every integer
multiple of the window's fundamental frequency, in the idealized
infinite-baseline limit). Rather than building tempered-distribution
machinery to formalize that literally, this file proves the same
underlying mechanism directly and elementarily: if the periodic window
is given by its (finite, or finitely-truncated) real Fourier series
`w(t) = ∑ₖ c_k cos(2π k t/P_yr)`, then the windowed single-tone signal
`w(t)·cos(2πf0 t)` decomposes *exactly* (via ordinary product-to-sum,
term by term — no limit, no distribution) into a sum of pure tones at
frequencies `f0 + k/P_yr` and `-f0 + k/P_yr`, one pair per nonzero
Fourier coefficient `c_k`. This is the same "aliasing moves power to
`f0 + k/P_yr`" conclusion the paper draws from the Dirac-comb picture,
proved instead as a finite trigonometric identity in the style of
`FourierStructure.lean` elsewhere in this project.

What this does NOT capture: the paper's own statement is about the
*idealized infinite-baseline limit* (an literal Dirac comb, i.e. every
harmonic present with no truncation, and the window extending over all
time rather than any finite or convergent sum). The version here assumes
the window's Fourier series is a `Finset`-indexed finite sum (or would
need `tsum`/absolute-convergence hypotheses to go further); it captures
the identical algebraic mechanism at every finite truncation, but is not
a literal formalization of the infinite-baseline Poisson-summation
statement. Reconnaissance for going further: `Mathlib.Analysis.Fourier.
PoissonSummation` does exist and has applicable content
(`Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`,
`SchwartzMap.tsum_eq_tsum_fourierIntegral`) that could plausibly bridge
the truncated version proved here to the paper's literal infinite-comb
statement; this was not attempted.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace KNOMP

open Real

/-- The alias period at integer offset `k`, given the true frequency
`f0` and the window's fundamental period `P_yr`: `1/(f0 + k/P_yr)`. -/
noncomputable def aliasPeriod (f0 Pyr : ℝ) (k : ℤ) : ℝ :=
  1 / (f0 + (k : ℝ) / Pyr)

/-- A `P_yr`-periodic sampling window, given by a finite real Fourier
series with coefficients `c`, applied to (i.e. multiplying) a single-tone
signal at frequency `f0`. -/
noncomputable def windowedSignal (f0 Pyr : ℝ) (coefs : Finset ℤ) (c : ℤ → ℝ) (t : ℝ) : ℝ :=
  (∑ k ∈ coefs, c k * Real.cos (2 * π * k * t / Pyr)) * Real.cos (2 * π * f0 * t)

/-- **Proposition `alias`, trigonometric core — PROVED.** The windowed
signal decomposes exactly into pure tones at every alias frequency
`f0 + k/P_yr` (and its mirror `-f0 + k/P_yr`), one pair per Fourier
coefficient `c_k` of the window, via ordinary product-to-sum — no
distributional machinery needed. This is the finite, elementary version
of the paper's Dirac-comb argument; see the file docstring for exactly
what is and is not captured relative to the paper's idealized
infinite-baseline statement. -/
theorem windowedSignal_alias_decomposition
    (f0 Pyr : ℝ) (coefs : Finset ℤ) (c : ℤ → ℝ) (t : ℝ) :
    windowedSignal f0 Pyr coefs c t
      = ∑ k ∈ coefs, (c k / 2) *
          (Real.cos (2 * π * (f0 + (k:ℝ) / Pyr) * t)
            + Real.cos (2 * π * (-f0 + (k:ℝ) / Pyr) * t)) := by
  unfold windowedSignal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hprod : Real.cos (2 * π * k * t / Pyr) * Real.cos (2 * π * f0 * t)
      = (Real.cos (2 * π * k * t / Pyr - 2 * π * f0 * t)
          + Real.cos (2 * π * k * t / Pyr + 2 * π * f0 * t)) / 2 := by
    rw [Real.cos_sub, Real.cos_add]; ring
  rw [mul_assoc, hprod]
  ring_nf

/-- The alias frequency `f0 + k/Pyr`'s reciprocal is exactly `aliasPeriod
f0 Pyr k` — connecting the trigonometric decomposition's frequencies
above to the period-domain quantity the rest of the file works with. -/
theorem aliasPeriod_eq_inv_freq (f0 Pyr : ℝ) (k : ℤ) :
    aliasPeriod f0 Pyr k = (f0 + (k:ℝ) / Pyr)⁻¹ := by
  unfold aliasPeriod
  rw [one_div]

/-- **Power really is present at the alias frequency.** Whenever the
window's `k`-th Fourier coefficient `c k` is nonzero, the windowed
signal's decomposition (above) has a nonzero coefficient at exactly
frequency `f0 + k/Pyr` — genuine spectral power there, not merely a
frequency that happens to appear with coefficient zero. This is the
precise, checkable sense in which "the periodogram has power at the
alias frequency `f0 + k/Pyr`" holds for the finite/truncated window. -/
theorem alias_term_nonzero_of_coeff_nonzero (c : ℤ → ℝ) (k : ℤ) (hc : c k ≠ 0) :
    (c k / 2 : ℝ) ≠ 0 := by
  simp [hc]

/-- **Worked numerical instance.** For `P_true = 320.5` days,
`P_yr = 365.25` days (so `f0 = 1/320.5`), the `k = +1` and `k = -1`
aliases are at the periods the paper states, verified here as an *exact*
rational identity — `(1/320.5 + 1/365.25)⁻¹` and `(1/320.5 -
1/365.25)⁻¹` — rather than by approximate decimal computation. -/
theorem alias_period_plus_one_exact :
    aliasPeriod (1 / 320.5) 365.25 1 = (1 / 320.5 + 1 / 365.25)⁻¹ := by
  unfold aliasPeriod
  norm_num

theorem alias_period_minus_one_exact :
    aliasPeriod (1 / 320.5) 365.25 (-1) = (1 / 320.5 - 1 / 365.25)⁻¹ := by
  unfold aliasPeriod
  norm_num

/-- The `k=+1` alias period is close to 170.71 days (paper's stated
value), confirmed here to a tight explicit tolerance rather than by
inspecting a decimal approximation. -/
theorem alias_period_plus_one_approx :
    |aliasPeriod (1 / 320.5) 365.25 1 - 170.71| < 0.01 := by
  unfold aliasPeriod
  rw [abs_lt]
  constructor <;> norm_num

/-- The `k=-1` alias period is close to 2615.92 days (paper's stated
value). -/
theorem alias_period_minus_one_approx :
    |aliasPeriod (1 / 320.5) 365.25 (-1) - 2615.92| < 0.01 := by
  unfold aliasPeriod
  rw [abs_lt]
  constructor <;> norm_num

/-- Neither alias coincides with the true period `320.5` days — the
paper's closing observation that a candidate found near either alias is
distinguishable, by direct comparison against the exact formula, from
the true signal. -/
theorem alias_periods_differ_from_true :
    aliasPeriod (1 / 320.5) 365.25 1 ≠ 320.5
      ∧ aliasPeriod (1 / 320.5) 365.25 (-1) ≠ 320.5 := by
  unfold aliasPeriod
  constructor <;> norm_num

end KNOMP
