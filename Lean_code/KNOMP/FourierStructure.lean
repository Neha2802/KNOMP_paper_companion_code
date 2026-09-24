/-
KNOMP/FourierStructure.lean

Source: Section 11, "Exact Leading-Order Fourier Structure of the
Keplerian Atom": Lemma `kepler-series`, Lemma `eqcenter`, Proposition
`fourier` (exact O(e²) Fourier coefficients).

STATUS: PARTIAL (stage 1 not attempted; stage 2, including the
corrected non-degeneracy fact below, fully proved).

The paper's derivation has two stages: (1) a PERTURBATIVE stage (solving
Kepler's equation as a power series in `e`, Lemma `kepler-series`, then
converting to the "equation of center" `δ := ν - M`, Lemma `eqcenter`) —
this is genuine asymptotic analysis (implicit function theorem plus
formal power series matching) that would need Mathlib's formal-power-
series or asymptotic (`Asymptotics.IsBigO`) machinery to state and prove
properly, and is NOT attempted here; and (2) a TRIGONOMETRIC stage
(substituting `δ`'s truncated expansion into `cos(ν+ω)` and reducing via
product-to-sum identities to extract Fourier coefficients) — this is
ordinary, checkable trigonometric algebra, and IS proved here in full,
taking stage (1)'s output as given input data rather than re-deriving it.

Concretely: rather than working with formal `O(e³)` asymptotic
statements, we define `fApprox` directly from the paper's *stated*
second-order truncations of `cos δ` and `sin δ` (Eqs. just before
`cos-nu-omega` in the source proof) as exact ingredients, and prove the
resulting Fourier decomposition holds *exactly* for this object — which
is the same trigonometric content the paper's proof establishes, stated
without needing formal little-o/big-O bookkeeping. The genuinely
asymptotic claim ("these truncations of `cos δ`, `sin δ` really do agree
with the true values to `O(e³)`") is Lemma `kepler-series`/`eqcenter`'s
content, taken as given here.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace KNOMP

open Real

/-- The Keplerian atom (unit gain), as a function of mean anomaly `M`,
using given (not re-derived) truncated `cos δ`, `sin δ` values matching
the paper's own second-order expressions. -/
noncomputable def fApprox (M e omega : ℝ) (cosDelta sinDelta : ℝ) : ℝ :=
  Real.cos (M + omega) * cosDelta - Real.sin (M + omega) * sinDelta + e * Real.cos omega

/-- Product-to-sum: `sinA·sinB = ½[cos(A-B) - cos(A+B)]`. -/
theorem sin_mul_sin_eq (A B : ℝ) :
    Real.sin A * Real.sin B = (Real.cos (A - B) - Real.cos (A + B)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- Product-to-sum: `cosA·cosB = ½[cos(A-B) + cos(A+B)]`. -/
theorem cos_mul_cos_eq (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- `sin²x = (1 - cos(2x))/2`, derived from `Real.cos_sq` and the
Pythagorean identity (Mathlib does not appear to have this exact
half-angle form under a single name). -/
theorem sin_sq_eq (x : ℝ) : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
  have h := Real.cos_sq x
  have hpyth := Real.sin_sq_add_cos_sq x
  linarith

/-- **Proposition `fourier`, trigonometric core.** Given the paper's own
stated truncations `cos δ = 1 - 2e²sin²M` and `sin δ = 2e sinM +
(5/4)e²sin(2M)` (taken as hypotheses, matching Lemma `eqcenter`'s output),
`fApprox` decomposes exactly into the stated Fourier coefficients `A₁,
B₁, A₂, B₂` plus an explicit (not hidden in a remainder) third-harmonic
term `(9/8)e²cos(3M+ω)`.

PROOF METHOD: the identity is verified via `linear_combination` against
six elementary trigonometric sub-identities (product-to-sum for the two
`sin·sin` and one `cos·cos` product that arise, the `sin²` half-angle
identity, and the two angle-sum expansions needed to eliminate
`cos(M+ω)`, `cos(M-ω)`, `cos(2M+ω)` in favor of the base atoms `cosM,
sinM, cosω, sinω` and the untouched harmonics `cos(2M), sin(2M),
cos(3M+ω)`) — the exact coefficient of each sub-identity in the
combination was derived by hand (a page of algebra, not restated in the
file) and cross-checked by the tactic itself succeeding. -/
theorem fourier_decomposition (M e omega : ℝ) :
    fApprox M e omega (1 - 2 * e ^ 2 * (Real.sin M) ^ 2)
        (2 * e * Real.sin M + (5 / 4) * e ^ 2 * Real.sin (2 * M))
      = (1 - 9 / 8 * e ^ 2) * Real.cos omega * Real.cos M
        - (1 - 7 / 8 * e ^ 2) * Real.sin omega * Real.sin M
        + e * Real.cos omega * Real.cos (2 * M) - e * Real.sin omega * Real.sin (2 * M)
        + 9 / 8 * e ^ 2 * Real.cos (3 * M + omega) := by
  unfold fApprox
  have hsin2 : Real.sin M ^ 2 = (1 - Real.cos (2 * M)) / 2 := sin_sq_eq M
  have hprod1 : Real.sin M * Real.sin (M + omega)
      = (Real.cos omega - Real.cos (2 * M + omega)) / 2 := by
    rw [sin_mul_sin_eq]
    rw [show M - (M + omega) = -omega by ring, show M + (M + omega) = 2 * M + omega by ring,
        Real.cos_neg]
  have hprod2 : Real.sin (2 * M) * Real.sin (M + omega)
      = (Real.cos (M - omega) - Real.cos (3 * M + omega)) / 2 := by
    rw [sin_mul_sin_eq]
    rw [show 2 * M - (M + omega) = M - omega by ring,
        show 2 * M + (M + omega) = 3 * M + omega by ring]
  have hprod3 : Real.cos (2 * M) * Real.cos (M + omega)
      = (Real.cos (M - omega) + Real.cos (3 * M + omega)) / 2 := by
    rw [cos_mul_cos_eq]
    rw [show 2 * M - (M + omega) = M - omega by ring,
        show 2 * M + (M + omega) = 3 * M + omega by ring]
  have hcos_pm1 : Real.cos (M + omega) = Real.cos M * Real.cos omega - Real.sin M * Real.sin omega :=
    Real.cos_add M omega
  have hcos_pm2 : Real.cos (M - omega) = Real.cos M * Real.cos omega + Real.sin M * Real.sin omega :=
    Real.cos_sub M omega
  have h2M_expand : Real.cos (2 * M + omega)
      = Real.cos (2 * M) * Real.cos omega - Real.sin (2 * M) * Real.sin omega :=
    Real.cos_add (2 * M) omega
  linear_combination (-2 * e ^ 2 * Real.cos (M + omega)) * hsin2 + (-2 * e) * hprod1
    + (-(5/4) * e ^ 2) * hprod2 + (e ^ 2) * hprod3 + (1 - e ^ 2) * hcos_pm1
    + (-(1/8) * e ^ 2) * hcos_pm2 + e * h2M_expand

/-- **Non-degeneracy of `fourier_decomposition`'s coefficients, corrected
form.** UPDATE: the current canonical paper draft,
`source/KNOMP_fix_attempt_1.tex`, now states and proves this exact
three-way disjunction directly as `Corollary cor:fourier-nondegenerate`
(with the identical case split on `cos ω = 0` used below), and
`Theorem identifiability`'s Step 2 cites that corollary rather than the
old false two-term claim — i.e. the paper has been corrected to match
this file, not the reverse. The paragraph below, describing the
now-superseded citation, is kept as-is for historical context (it
predates that paper fix and remains accurate about the OLD paper text,
`KNOMP_complete_proofs_revised_2.tex` and earlier).

The (superseded) paper citation of this Proposition (used by
`Identifiability.lean`'s general-`k ≥ 1` `hli` case and by
`KeplerFamily.lean`'s R3) claimed `A_1 ≠ 0 ∨ A_2 ≠ 0` for the fundamental/
second-harmonic cosine coefficients `A_1 = (1-9/8 e²) cos ω`,
`A_2 = e cos ω` alone. This is false at `ω = π/2` for every `e`: both are
exactly proportional to `cos ω`, hence both vanish there simultaneously
(see `proposed_changes.md` for the full symmetry argument, `cos ν` even /
`sin ν` odd in `M`, showing this is structural, not a typo). A first
attempt at a fix — citing the fundamental-harmonic **amplitude**
`√(A_1²+B_1²) ≠ 0` instead — is *also* false: at `e = 2√2/3`, `ω = 0`,
`A_1 = (1 - 9/8·8/9)·1 = 0` and `B_1 = -(1-7/8·8/9)·0 = 0`
simultaneously (both factors of `B_1` individually vanish or are
multiplied by `sin ω = 0`), so the amplitude is genuinely `0` there too.
What actually holds everywhere, and is what this theorem states: the
**three-way disjunction** `A_1 ≠ 0 ∨ B_1 ≠ 0 ∨ A_2 ≠ 0` — at the
`ω = π/2` counterexample to the original claim, `B_1 ≠ 0` rescues it;
at the `e = 2√2/3, ω = 0` counterexample to the amplitude claim,
`A_2 = e·cos ω = e ≠ 0` rescues it. Proof: case on `cos ω = 0` (forces
`A_1 = A_2 = 0` identically, but then `sin ω = ±1 ≠ 0` and
`1 - 7/8 e² > 1/8 > 0` for `e < 1`, so `B_1 ≠ 0`) vs. `cos ω ≠ 0` (then
`e = 0` gives `A_1 = cos ω ≠ 0` directly, else `e > 0` gives
`A_2 = e·cos ω ≠ 0`). -/
theorem fourier_coeffs_not_all_zero {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (omega : ℝ) :
    (1 - 9 / 8 * e ^ 2) * Real.cos omega ≠ 0
      ∨ -(1 - 7 / 8 * e ^ 2) * Real.sin omega ≠ 0
      ∨ e * Real.cos omega ≠ 0 := by
  by_cases hcos : Real.cos omega = 0
  · right; left
    have hpyth : Real.sin omega ^ 2 + Real.cos omega ^ 2 = 1 := Real.sin_sq_add_cos_sq omega
    have hsin_ne : Real.sin omega ≠ 0 := by
      intro hsin
      rw [hcos, hsin] at hpyth
      norm_num at hpyth
    have h1e : (0 : ℝ) < 1 - e := by linarith [he.2]
    have h2e : (0 : ℝ) < 1 + e := by linarith [he.1]
    have he2lt1 : e ^ 2 < 1 := by nlinarith [mul_pos h1e h2e]
    have hcoef_pos : (0 : ℝ) < 1 - 7 / 8 * e ^ 2 := by nlinarith [he2lt1]
    exact mul_ne_zero (by linarith) hsin_ne
  · by_cases he0 : e = 0
    · left
      have hcoef1 : (1 - 9 / 8 * e ^ 2 : ℝ) = 1 := by rw [he0]; ring
      rw [hcoef1, one_mul]
      exact hcos
    · right; right
      have he_pos : 0 < e := lt_of_le_of_ne he.1 (Ne.symm he0)
      exact mul_ne_zero (ne_of_gt he_pos) hcos

end KNOMP
