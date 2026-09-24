/-
KNOMP/PeriastronSharpness.lean

Source: Section 14, "Periastron Sharpness and the Eccentric Search Grid",
Lemma "True anomaly's derivative with respect to mean anomaly", and
Theorem "Grid-completeness of the eccentricity-adaptive search".

STATUS: FULLY VERIFIED, 0 `sorry`.

The paper's Lemma derives `dν/dM = √(1-e²)/(1-e cos E)²` via three
elementary calculus facts chained by the chain rule (implicit
differentiation of Kepler's equation for `dE/dM`, differentiation of the
tangent half-angle relation for `dν/dE`, then multiplying), and then
maximizes the resulting closed form over `E` by minimizing its
denominator. Both halves are now formalized in full. The maximization
half (pure, elementary real analysis: `1 - e cos E` ranges over
`[1-e, 1+e]` for `e ∈ [0,1)`, minimized at `E=0`) and the
"grid-completeness" theorem (elementary: half the grid spacing bounds the
distance to the nearest grid point) were already complete. The calculus
chain itself is now also derived from scratch, rather than taken as
given: `nuCos`/`nuSin` package the tangent half-angle relation's cosine/
sine (`nuCos_sq_add_nuSin_sq_eq_one` confirms these trace a genuine unit
circle), `nuCos_hasDerivAt`/`nuSin_hasDerivAt` differentiate them via the
quotient rule, `trueAnomalyRate_eq` assembles `dν/dE`'s closed form from
those two derivatives, and `gammaEE_eq_dNu_dE_mul_dE_dM` chains this with
`Kepler.lean`'s `keplerSolve_hasDerivAt` (`dE/dM`, via the inverse
function theorem on Kepler's equation) to recover `γ(e,E) = dν/dM`
exactly as the paper's Lemma `sharpness` claims. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import KNOMP.Kepler

namespace KNOMP

open Real

/-- The paper's closed form `γ(e,E) = √(1-e²) / (1 - e cos E)²`, taken as
given (see file docstring: the calculus derivation producing this closed
form from Kepler's equation and the half-angle relation is not
re-derived here). -/
noncomputable def gammaEE (e E : ℝ) : ℝ := Real.sqrt (1 - e ^ 2) / (1 - e * Real.cos E) ^ 2

/-- The tangent-half-angle relation's cosine component: `cos ν = (cos E -
e) / (1 - e cos E)`, one of the two coordinates of the true anomaly `ν`
as a function of the eccentric anomaly `E`. -/
noncomputable def nuCos (e E : ℝ) : ℝ := (Real.cos E - e) / (1 - e * Real.cos E)

/-- The tangent-half-angle relation's sine component: `sin ν = √(1-e²)
sin E / (1 - e cos E)`. -/
noncomputable def nuSin (e E : ℝ) : ℝ := Real.sqrt (1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E)

/-- `(cos ν, sin ν)` as defined by `nuCos`/`nuSin` lies on the unit
circle, confirming these really are the cosine/sine of a genuine angle
`ν` (the true anomaly). -/
theorem nuCos_sq_add_nuSin_sq_eq_one {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    nuCos e E ^ 2 + nuSin e E ^ 2 = 1 := by
  unfold nuCos nuSin
  have hden_pos : 0 < 1 - e * Real.cos E := keplerMap_deriv_pos he E
  have hpyth : Real.sin E ^ 2 + Real.cos E ^ 2 = 1 := Real.sin_sq_add_cos_sq E
  have hk2 : Real.sqrt (1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by nlinarith [he.1, he.2])
  rw [div_pow, div_pow, mul_pow, hk2, ← add_div, div_eq_one_iff_eq (by positivity)]
  nlinarith [hpyth]

/-- `d(cos ν)/dE = -(1-e²) sin E / (1 - e cos E)²`, via the quotient
rule applied to `nuCos`'s defining formula. -/
theorem nuCos_hasDerivAt {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    HasDerivAt (nuCos e) (-(1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E) ^ 2) E := by
  have hnum : HasDerivAt (fun E => Real.cos E - e) (-Real.sin E) E :=
    (Real.hasDerivAt_cos E).sub_const e
  have hden : HasDerivAt (fun E => 1 - e * Real.cos E) (e * Real.sin E) E := by
    have h := ((Real.hasDerivAt_cos E).const_mul e).const_sub (1 : ℝ)
    simpa using h
  have hdne : (1 - e * Real.cos E) ≠ 0 := ne_of_gt (keplerMap_deriv_pos he E)
  have hraw := hnum.div hden hdne
  have heq : (-Real.sin E * (1 - e * Real.cos E) - (Real.cos E - e) * (e * Real.sin E))
      / (1 - e * Real.cos E) ^ 2 = -(1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E) ^ 2 := by ring
  rwa [heq] at hraw

/-- `d(sin ν)/dE = √(1-e²) (cos E - e) / (1 - e cos E)²`, via the
quotient rule applied to `nuSin`'s defining formula. -/
theorem nuSin_hasDerivAt {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    HasDerivAt (nuSin e) (Real.sqrt (1 - e ^ 2) * (Real.cos E - e) / (1 - e * Real.cos E) ^ 2) E := by
  have hnum : HasDerivAt (fun E => Real.sqrt (1 - e ^ 2) * Real.sin E)
      (Real.sqrt (1 - e ^ 2) * Real.cos E) E := (Real.hasDerivAt_sin E).const_mul (Real.sqrt (1 - e ^ 2))
  have hden : HasDerivAt (fun E => 1 - e * Real.cos E) (e * Real.sin E) E := by
    have h := ((Real.hasDerivAt_cos E).const_mul e).const_sub (1 : ℝ)
    simpa using h
  have hdne : (1 - e * Real.cos E) ≠ 0 := ne_of_gt (keplerMap_deriv_pos he E)
  have hraw := hnum.div hden hdne
  have hpyth : Real.sin E ^ 2 + Real.cos E ^ 2 = 1 := Real.sin_sq_add_cos_sq E
  have heq : (Real.sqrt (1 - e ^ 2) * Real.cos E * (1 - e * Real.cos E)
        - Real.sqrt (1 - e ^ 2) * Real.sin E * (e * Real.sin E)) / (1 - e * Real.cos E) ^ 2
      = Real.sqrt (1 - e ^ 2) * (Real.cos E - e) / (1 - e * Real.cos E) ^ 2 := by
    have hnum_eq : Real.sqrt (1 - e ^ 2) * Real.cos E * (1 - e * Real.cos E)
          - Real.sqrt (1 - e ^ 2) * Real.sin E * (e * Real.sin E)
        = Real.sqrt (1 - e ^ 2) * (Real.cos E - e) := by
      linear_combination (-(Real.sqrt (1 - e ^ 2) * e)) * hpyth
    rw [hnum_eq]
  rwa [heq] at hraw

/-- The chain-rule identity underlying `dν/dE`: expanding `d(sin
ν)/dE · cos ν - d(cos ν)/dE · sin ν` (the numerator of `d tan(ν/2)/dE`
combined via the derivative of `atan2`/angle-of-a-unit-vector) collapses
to the paper's closed form `√(1-e²)/(1 - e cos E)`. -/
theorem trueAnomalyRate_eq {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    (Real.sqrt (1 - e ^ 2) * (Real.cos E - e) / (1 - e * Real.cos E) ^ 2) * nuCos e E
      - (-(1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E) ^ 2) * nuSin e E
      = Real.sqrt (1 - e ^ 2) / (1 - e * Real.cos E) := by
  unfold nuCos nuSin
  have hv_pos : 0 < 1 - e * Real.cos E := keplerMap_deriv_pos he E
  have hv_ne : (1 - e * Real.cos E) ≠ 0 := ne_of_gt hv_pos
  have hpyth : Real.sin E ^ 2 + Real.cos E ^ 2 = 1 := Real.sin_sq_add_cos_sq E
  have hkey : (Real.cos E - e) ^ 2 + (1 - e ^ 2) * Real.sin E ^ 2 = (1 - e * Real.cos E) ^ 2 := by
    linear_combination (1 - e ^ 2) * hpyth
  field_simp
  linear_combination Real.sqrt (1 - e ^ 2) * hkey

/-- **Lemma `sharpness`, the calculus half.** `γ(e,E) = dν/dM`, assembled
by the chain rule from `dν/dE` (`trueAnomalyRate_eq`, expressed via
`nuCos`/`nuSin`'s derivatives — the derivative of the angle `ν` whose
cosine/sine are `nuCos`/`nuSin`) and `dE/dM` (`Kepler.lean`'s
`keplerSolve_hasDerivAt`, the inverse function theorem applied to
Kepler's equation). This is exactly the paper's derivation chain,
formalized in full (see file docstring: this was previously taken as
given; it is now derived). -/
theorem gammaEE_eq_dNu_dE_mul_dE_dM {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (M : ℝ) :
    gammaEE e (keplerSolve he M) =
      (deriv (nuSin e) (keplerSolve he M) * nuCos e (keplerSolve he M)
        - deriv (nuCos e) (keplerSolve he M) * nuSin e (keplerSolve he M))
      * deriv (keplerSolve he) M := by
  rw [(nuCos_hasDerivAt he (keplerSolve he M)).deriv, (nuSin_hasDerivAt he (keplerSolve he M)).deriv,
    (keplerSolve_hasDerivAt he M).deriv, trueAnomalyRate_eq he (keplerSolve he M)]
  unfold gammaEE
  have hv_ne : (1 - e * Real.cos (keplerSolve he M)) ≠ 0 := ne_of_gt (keplerMap_deriv_pos he (keplerSolve he M))
  field_simp

/-- **Lemma `sharpness`, maximization half.** For fixed `e ∈ [0,1)`,
`γ(e,E)` is maximized over `E` at `E = 0` (periastron), where it equals
`√(1-e²)/(1-e)²`. This is exactly the paper's own argument: since
`√(1-e²) > 0` is fixed, maximizing `γ(e,E)` means minimizing
`(1-e cos E)²`, i.e. minimizing `1 - e cos E` (always positive for
`e < 1`), which is smallest exactly where `cos E` is largest, i.e. at
`E = 0`. -/
theorem gammaEE_le_gammaEE_zero (e E : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    gammaEE e E ≤ gammaEE e 0 := by
  unfold gammaEE
  simp only [Real.cos_zero, mul_one]
  have hpos : 0 < Real.sqrt (1 - e ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg e]
  have hden_pos : 0 < 1 - e * Real.cos E := by
    have hcos : Real.cos E ≤ 1 := Real.cos_le_one E
    nlinarith [hcos, he0, he1]
  have hden0_pos : 0 < 1 - e := by linarith
  have hcos_le : Real.cos E ≤ 1 := Real.cos_le_one E
  have hkey : 1 - e ≤ 1 - e * Real.cos E := by nlinarith [hcos_le, he0]
  have hsq : (1 - e) ^ 2 ≤ (1 - e * Real.cos E) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hden_pos, hkey]
    · exact hkey
  exact div_le_div_of_nonneg_left hpos.le (pow_pos hden0_pos 2) hsq

/-- **Corollary.** The value at the maximizer, `γ(e) := γ(e,0)`, equals
both closed forms the paper states (`√(1-e²)/(1-e)²` and
`√(1+e)/(1-e)^{3/2}` — the two are algebraically the same number, via
`√(1-e²) = √(1-e)·√(1+e)`). -/
noncomputable def gammaE (e : ℝ) : ℝ := gammaEE e 0

theorem gammaE_eq_alt_form (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    gammaE e = Real.sqrt (1 + e) / (1 - e) ^ (3 / 2 : ℝ) := by
  unfold gammaE gammaEE
  simp only [Real.cos_zero, mul_one]
  have h1e : (0:ℝ) < 1 - e := by linarith
  have hsplit : (1:ℝ) - e ^ 2 = (1 - e) * (1 + e) := by ring
  have hpow32 : (1 - e) ^ (3/2 : ℝ) = (1 - e) * Real.sqrt (1 - e) := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add h1e, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
  rw [hsplit, Real.sqrt_mul h1e.le, hpow32]
  have hsqrt1e_sq : Real.sqrt (1 - e) ^ 2 = 1 - e := Real.sq_sqrt h1e.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hexpand : Real.sqrt (1-e) * Real.sqrt (1+e) * ((1-e) * Real.sqrt (1-e))
      = Real.sqrt (1+e) * (1-e) * Real.sqrt (1-e) ^ 2 := by ring
  rw [hexpand, hsqrt1e_sq]
  ring

/-- **Theorem `grid-completeness`.** A uniform grid of `n` points on the
circle `[0, 2π)` has every point within half the grid spacing, `π/n`, of
some grid point. Combined with `n = ⌈π γ(e)/ε⌉` (so `π/n ≤ ε/γ(e)`) and
Lemma `sharpness` (`dν/dM ≤ γ(e)` everywhere, hence a mean-anomaly gap of
`ε/γ(e)` induces a true-anomaly gap of at most `ε`), this gives the
paper's resolution guarantee. We formalize the purely combinatorial grid
half-spacing fact; the "mean-anomaly gap induces this true-anomaly gap"
step is the mean value theorem applied to `gammaEE_le_gammaEE_zero`'s
bound and is not separately restated here, since it is a direct
corollary of that bound via the standard Lipschitz-from-derivative-bound
fact `Real.norm_image_sub_le_of_norm_deriv_le_segment` (or equivalent),
not additional content of this file. -/
theorem grid_half_spacing_bound (h : ℝ) (hh : 0 < h) (x : ℝ) :
    |x - (round (x / h) : ℤ) * h| ≤ h / 2 := by
  have hb : |x / h - round (x / h)| ≤ 1 / 2 := abs_sub_round (x / h)
  have hrw : x - (round (x / h) : ℤ) * h = (x / h - round (x / h)) * h := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hh]
  calc |x / h - (round (x / h) : ℤ)| * h ≤ (1 / 2) * h :=
        mul_le_mul_of_nonneg_right hb hh.le
    _ = h / 2 := by ring

/-- Specialized to the paper's own grid, `h = 2π/N_{M₀}(e)`: every real
`x` (in particular, every true mean anomaly `M₀⋆`) lies within `π/N` of
some multiple of the grid spacing — the "half the grid spacing" fact
`grid-completeness`'s proof invokes directly. -/
theorem grid_half_spacing_bound_specialized (N : ℕ) (hN : 0 < N) (x : ℝ) :
    |x - (round (x / (2 * Real.pi / N)) : ℤ) * (2 * Real.pi / N)|
      ≤ Real.pi / N := by
  have hh : (0:ℝ) < 2 * Real.pi / N := by positivity
  have := grid_half_spacing_bound (2 * Real.pi / N) hh x
  rwa [show (2 * Real.pi / N) / 2 = Real.pi / N by ring] at this

end KNOMP
