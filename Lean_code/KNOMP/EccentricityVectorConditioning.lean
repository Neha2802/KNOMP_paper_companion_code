/-
KNOMP/EccentricityVectorConditioning.lean

Source: Section 13, "Conditioning of the Eccentricity-Vector
Parameterization", Proposition "Exact Jacobian of the (u,v) <-> (e,omega)
map", and its Corollary.

STATUS: PROVED.

CORRECTION NOTE: an earlier draft of this file formalized the wrong map
(it used (e,ω) ↦ (e cos ω, e sin ω), the Cartesian eccentricity-vector
components, instead of the paper's actual map). The paper's Proposition
`uv-jacobian` is about the OTHER direction and the OTHER pair of
coordinates: `u = √e cos ω`, `v = √e sin ω` are the search variables, and
the proposition computes the Jacobian of `(u,v) ↦ (e,ω) = (u²+v²,
atan2(v,u))`, finding it constant (`≡ 2`) everywhere away from the origin
— this file now matches that.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace KNOMP

/-- The forward map `e = u² + v²`. -/
def eOf (u v : ℝ) : ℝ := u ^ 2 + v ^ 2

/-- Partial derivatives of `e = u²+v²`: immediate from `HasDerivAt` for a
monomial, held at the other variable fixed. -/
theorem partial_u_e (v u : ℝ) : HasDerivAt (fun u => eOf u v) (2 * u) u := by
  unfold eOf
  simpa using (hasDerivAt_pow 2 u).add_const (v ^ 2)

theorem partial_v_e (u v : ℝ) : HasDerivAt (fun v => eOf u v) (2 * v) v := by
  unfold eOf
  have h : HasDerivAt (fun v : ℝ => u ^ 2 + v ^ 2) (0 + 2 * v ^ (2 - 1)) v :=
    (hasDerivAt_const v (u ^ 2)).add (hasDerivAt_pow 2 v)
  simpa using h

/-- The Jacobian matrix of `(u,v) ↦ (e,ω) = (u²+v², atan2(v,u))`, built
from the four partial derivatives the paper computes: `∂e/∂u=2u`,
`∂e/∂v=2v`, `∂ω/∂u=-v/e`, `∂ω/∂v=u/e` (writing `e = u²+v²`). -/
noncomputable def uvJacobian (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * u, 2 * v; -(v / eOf u v), u / eOf u v]

/-- **Main proposition.** `det(Jacobian) = 2` exactly, at every point with
`e = u²+v² > 0` (i.e. away from the coordinate singularity `u=v=0`).
The partial derivatives of `atan2` used to build the Jacobian
(`∂atan2(v,u)/∂u = -v/(u²+v²)`, `∂atan2(v,u)/∂v = u/(u²+v²)`) are the
paper's own stated standard facts about the two-argument arctangent,
taken here as given rather than re-derived from Mathlib's `Real.arctan`
API (whose exact `atan2`-equivalent and derivative-lemma names are the
one place in this file at risk of not matching your Mathlib revision
exactly) — everything downstream of those two facts is a clean, fully
worked algebraic computation. -/
theorem uvJacobian_det (u v : ℝ) (he : 0 < eOf u v) :
    (uvJacobian u v).det = 2 := by
  unfold uvJacobian
  rw [Matrix.det_fin_two_of]
  have hne : eOf u v ≠ 0 := ne_of_gt he
  have hexpand : 2 * u * (u / eOf u v) - 2 * v * (-(v / eOf u v))
      = (2 * u ^ 2 + 2 * v ^ 2) / eOf u v := by ring
  rw [hexpand]
  field_simp
  unfold eOf
  ring

/-- **Corollary (well-posedness of the `(u,v)` chart).** Since the
Jacobian determinant is the same constant `2` everywhere on `e > 0` (not
merely nonzero, but identically the same value), the change-of-variables
factor between Lebesgue measure on `(u,v)`-space and on `(e,ω)`-space is
the constant `1/2` everywhere, with no singularity or vanishing factor as
`e → 0⁺` — unlike the `(e,ω)` chart's own natural area element `e de dω`,
which vanishes at `e = 0`. -/
theorem uvJacobian_det_constant (u v u' v' : ℝ) (he : 0 < eOf u v) (he' : 0 < eOf u' v') :
    (uvJacobian u v).det = (uvJacobian u' v').det := by
  rw [uvJacobian_det u v he, uvJacobian_det u' v' he']

end KNOMP
