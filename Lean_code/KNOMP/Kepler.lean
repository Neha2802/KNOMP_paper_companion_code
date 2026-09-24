/-
KNOMP/Kepler.lean

Source: Section 2 (`source/KNOMP_complete_proofs_1_.tex`, lines 97-109) —
the Keplerian atom's definition via Kepler's equation and the true-anomaly
trig identities.

PURPOSE / SCOPE: this file is "Phase 1" of the deferred full-N
`Identifiability.lean` Step 2 argument (see that file's own docstring,
and `HANDOFF.md` §5 item 1): a standalone, fully-proved fact that the
Keplerian atom is real-analytic in the mean anomaly (equivalently, in
time `t`, since `M(t) = n(t - T0)` is affine). This is genuinely useful
on its own — every other file in this project treats the photometric
atom as an abstract given function — and does not depend on, nor is it
yet wired into, the "Phase 2" full-N rank/Fubini genericity argument that
`Identifiability.lean`'s Step 2 will eventually need. That wiring, and
the rank/genericity argument itself, remain open (tracked as future
work; see `SCRATCHPAD.md`).

STATUS: 0 `sorry`, 0 `axiom`. Every theorem below is fully proved.

DELIBERATE REFORMULATION (documented per CLAUDE.md house rule 3 — this is
a flagged, justified substitution, not a silent one): the paper's own
formula for the true anomaly `ν` uses the half-angle relation
`tan(ν/2) = sqrt((1+e)/(1-e)) · tan(E/2)`. Proving *that* formula's
analyticity requires an extra side argument ruling out `tan`'s poles
along the actual orbit (which the paper itself only handles in prose:
"away from the isolated, non-accumulating singularities of tan, which do
not coincide with any point on the actual orbit"). Instead, this file
uses the standard equivalent rational ("Gauss") form:
  `cos ν = (cos E - e) / (1 - e cos E)`
  `sin ν = sqrt(1 - e²) sin E / (1 - e cos E)`
which is the *same* function wherever the paper's `tan(ν/2)` formula is
even defined (a standard trig identity — `(cos ν, sin ν)` and `tan(ν/2)`
determine each other bijectively away from `tan`'s poles), but is
manifestly analytic with no pole-avoidance argument needed at all: for
`e ∈ [0,1)`, the denominator `1 - e cos E ≥ 1 - e > 0` is bounded away
from zero everywhere, unconditionally.

KEY MATHLIB FINDING WORTH RECORDING: earlier reconnaissance (recorded in
the now-superseded initial plan for this file) concluded "no
ImplicitFunctionTheorem file exists in this Mathlib snapshot at all —
this really is being built from scratch." That conclusion was based on
an incomplete search (only for a file literally named
`ImplicitFunctionTheorem*.lean`). A fuller search found:
`Mathlib/Analysis/Calculus/InverseFunctionTheorem/` (Mathlib's actual,
differently-named IFT), and — the key tool actually used below —
`PartialHomeomorph.analyticAt_symm` in
`Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`, a ready-made "the
inverse of a locally analytic homeomorphism, at a point of invertible
derivative, is analytic" lemma. This single lemma supplies essentially
all of the "analytic IFT" content needed for `keplerSolve_analytic`
below, once a *global* continuous inverse is in hand (itself assembled
from `StrictMono.orderIsoOfSurjective` + `OrderIso.toHomeomorph`, both
standard, already-existing Mathlib combinators — no ad hoc
monotone-plus-proper-implies-homeomorphism argument had to be built by
hand, contrary to what the original plan anticipated as "the one piece
of real proof-engineering risk in this phase").
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Module.Basic

set_option maxHeartbeats 1000000

namespace KNOMP

open Filter Topology

/-! ### Step 0: `Real.sin`/`Real.cos` are real-analytic everywhere

Mathlib has no direct statement of this (checked: no `AnalyticOnNhd`/
`AnalyticAt` result anywhere under `Mathlib/Analysis/SpecialFunctions/
Trigonometric/`), despite having every ingredient needed to prove it. The
route: `Complex.sin`/`Complex.cos` unfold (via `rfl`, since not marked
`irreducible`) to combinations of `Complex.exp`, which Mathlib already
knows is entire; combine that with the `AnalyticOnNhd` combinator algebra
to get ℂ-analyticity of `Complex.sin`/`Complex.cos`, then descend to
ℝ-analyticity of the *same* functions via `restrictScalars`, and finally
transport that to `Real.sin`/`Real.cos` by composing with the real-linear
maps `Complex.ofRealCLM`/`Complex.reCLM` and the bridging identities
`Complex.sin_ofReal_re`/`Complex.cos_ofReal_re`. -/

private theorem analyticOnNhd_zI : AnalyticOnNhd ℂ (fun z : ℂ => z * Complex.I) Set.univ :=
  analyticOnNhd_id.mul analyticOnNhd_const

private theorem analyticOnNhd_negzI : AnalyticOnNhd ℂ (fun z : ℂ => -z * Complex.I) Set.univ :=
  analyticOnNhd_id.neg.mul analyticOnNhd_const

private theorem complex_cos_analyticOnNhd : AnalyticOnNhd ℂ Complex.cos Set.univ := by
  have h : Complex.cos
      = fun z => (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 := rfl
  rw [h]
  exact (analyticOnNhd_zI.cexp.add analyticOnNhd_negzI.cexp).div analyticOnNhd_const
    (fun z _ => by norm_num)

private theorem complex_sin_analyticOnNhd : AnalyticOnNhd ℂ Complex.sin Set.univ := by
  have h : Complex.sin
      = fun z => (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 :=
    rfl
  rw [h]
  exact ((analyticOnNhd_negzI.cexp.sub analyticOnNhd_zI.cexp).mul analyticOnNhd_const).div
    analyticOnNhd_const (fun z _ => by norm_num)

theorem real_sin_analyticOnNhd : AnalyticOnNhd ℝ Real.sin Set.univ := by
  have h1 : AnalyticOnNhd ℝ Complex.sin Set.univ := complex_sin_analyticOnNhd.restrictScalars
  have h2 : AnalyticOnNhd ℝ (Complex.sin ∘ Complex.ofRealCLM) Set.univ :=
    h1.comp (Complex.ofRealCLM.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have h3 : AnalyticOnNhd ℝ (Complex.reCLM ∘ (Complex.sin ∘ Complex.ofRealCLM)) Set.univ :=
    (Complex.reCLM.analyticOnNhd Set.univ).comp h2 (Set.mapsTo_univ _ _)
  exact h3.congr isOpen_univ (fun x _ => Complex.sin_ofReal_re x)

theorem real_cos_analyticOnNhd : AnalyticOnNhd ℝ Real.cos Set.univ := by
  have h1 : AnalyticOnNhd ℝ Complex.cos Set.univ := complex_cos_analyticOnNhd.restrictScalars
  have h2 : AnalyticOnNhd ℝ (Complex.cos ∘ Complex.ofRealCLM) Set.univ :=
    h1.comp (Complex.ofRealCLM.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have h3 : AnalyticOnNhd ℝ (Complex.reCLM ∘ (Complex.cos ∘ Complex.ofRealCLM)) Set.univ :=
    (Complex.reCLM.analyticOnNhd Set.univ).comp h2 (Set.mapsTo_univ _ _)
  exact h3.congr isOpen_univ (fun x _ => Complex.cos_ofReal_re x)

/-! ### Step 1: the Kepler map `E ↦ E - e sin E` -/

/-- The forward Kepler map, mean anomaly as a function of eccentric
anomaly, for a fixed eccentricity `e`. Kepler's equation `M = E - e sin E`
says `M = keplerMap e E`. -/
noncomputable def keplerMap (e : ℝ) (E : ℝ) : ℝ := E - e * Real.sin E

theorem keplerMap_hasDerivAt (e E : ℝ) :
    HasDerivAt (keplerMap e) (1 - e * Real.cos E) E := by
  -- keplerMap e = fun y => y - e * Real.sin y
  show HasDerivAt (fun y => y - e * Real.sin y) (1 - e * Real.cos E) E
  exact (hasDerivAt_id E).sub ((Real.hasDerivAt_sin E).const_mul e)

theorem keplerMap_deriv (e E : ℝ) : deriv (keplerMap e) E = 1 - e * Real.cos E :=
  (keplerMap_hasDerivAt e E).deriv

/-- Trivial: a finite combination (via `id`, a constant, and `Real.sin`)
of everywhere-analytic functions. -/
theorem keplerMap_analytic (e : ℝ) : AnalyticOnNhd ℝ (keplerMap e) Set.univ :=
  analyticOnNhd_id.sub (analyticOnNhd_const.mul real_sin_analyticOnNhd)

theorem keplerMap_deriv_pos {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    0 < 1 - e * Real.cos E := by
  have hub : e * Real.cos E ≤ e := by
    calc e * Real.cos E ≤ e * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one E) he.1
      _ = e := mul_one e
  linarith [he.2]

theorem keplerMap_strictMono {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) :
    StrictMono (keplerMap e) := by
  apply strictMono_of_deriv_pos
  intro E
  rw [keplerMap_deriv]
  exact keplerMap_deriv_pos he E

theorem keplerMap_surjective {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) :
    Function.Surjective (keplerMap e) := by
  have hcont : Continuous (keplerMap e) := (keplerMap_analytic e).continuous
  have hbound : ∀ E : ℝ, E - 1 ≤ keplerMap e E ∧ keplerMap e E ≤ E + 1 := by
    intro E
    have hsin1 : e * Real.sin E ≤ e := by
      calc e * Real.sin E ≤ e * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one E) he.1
        _ = e := mul_one e
    have hsin2 : -e ≤ e * Real.sin E := by
      calc -e = e * (-1) := by ring
        _ ≤ e * Real.sin E := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin E) he.1
    constructor
    · simp only [keplerMap]; linarith [he.2]
    · simp only [keplerMap]; linarith [he.2]
  apply hcont.surjective
  · exact tendsto_atTop_mono (fun E => (hbound E).1)
      (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  · exact tendsto_atBot_mono (fun E => (hbound E).2)
      (tendsto_atBot_add_const_right atBot 1 tendsto_id)

/-! ### Step 2: the global inverse `keplerSolve` (eccentric anomaly as a
function of mean anomaly), and its analyticity -/

/-- The Kepler map, packaged as a global order isomorphism `ℝ ≃o ℝ`. -/
noncomputable def keplerOrderIso {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) : ℝ ≃o ℝ :=
  (keplerMap_strictMono he).orderIsoOfSurjective (keplerMap e) (keplerMap_surjective he)

theorem keplerOrderIso_apply {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    keplerOrderIso he E = keplerMap e E := rfl

/-- The Kepler map, packaged as a global homeomorphism `ℝ ≃ₜ ℝ` (an order
isomorphism between linearly-ordered `OrderTopology` spaces is
automatically a homeomorphism). -/
noncomputable def keplerHomeomorph {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) : ℝ ≃ₜ ℝ :=
  (keplerOrderIso he).toHomeomorph

theorem keplerHomeomorph_apply {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    keplerHomeomorph he E = keplerMap e E := by
  simp [keplerHomeomorph, OrderIso.coe_toHomeomorph, keplerOrderIso_apply]

/-- The Kepler map, packaged as a `PartialHomeomorph` on all of `ℝ`
(`source = target = Set.univ`). -/
noncomputable def keplerPartialHomeomorph {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) :
    PartialHomeomorph ℝ ℝ :=
  (keplerHomeomorph he).toPartialHomeomorph

theorem keplerPartialHomeomorph_apply {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    keplerPartialHomeomorph he E = keplerMap e E := by
  rw [keplerPartialHomeomorph, Homeomorph.toPartialHomeomorph_apply, keplerHomeomorph_apply]

theorem keplerPartialHomeomorph_target {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) :
    (keplerPartialHomeomorph he).target = Set.univ := by
  rw [keplerPartialHomeomorph, Homeomorph.toPartialHomeomorph_target]

/-- The eccentric anomaly as a function of the mean anomaly: the global
inverse of `keplerMap e`, i.e. the solution `E` of Kepler's equation
`M = E - e sin E`. -/
noncomputable def keplerSolve {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) : ℝ → ℝ :=
  (keplerPartialHomeomorph he).symm

theorem keplerMap_keplerSolve {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (M : ℝ) :
    keplerMap e (keplerSolve he M) = M := by
  have h : keplerPartialHomeomorph he (keplerSolve he M) = M := by
    apply (keplerPartialHomeomorph he).right_inv
    rw [keplerPartialHomeomorph_target]
    exact Set.mem_univ M
  rwa [keplerPartialHomeomorph_apply] at h

/-- The invertible derivative `1 - e cos E ≠ 0` of `keplerMap e` at a
point, repackaged as a `ContinuousLinearEquiv ℝ ≃L[ℝ] ℝ` (multiplication
by that nonzero scalar), matching `fderiv ℝ (keplerMap e) E`. This is the
input `PartialHomeomorph.analyticAt_symm` needs in place of a general
invertible derivative — in one real dimension, "invertible" just means
"nonzero". -/
noncomputable def keplerDerivEquiv {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (1 - e * Real.cos E) (ne_of_gt (keplerMap_deriv_pos he E)))

theorem keplerMap_fderiv_eq {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (E : ℝ) :
    fderiv ℝ (keplerMap e) E = (keplerDerivEquiv he E : ℝ →L[ℝ] ℝ) := by
  rw [← deriv_fderiv, keplerMap_deriv]
  apply ContinuousLinearMap.ext
  intro x
  simp [keplerDerivEquiv, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]

/-- **The analytic IFT step.** `keplerSolve` is real-analytic everywhere:
at each mean anomaly `M`, it is the local (here, global) inverse of the
analytic, invertible-derivative map `keplerMap e` at `keplerSolve he M`,
so `OpenPartialHomeomorph.analyticAt_symm` applies directly.

In Mathlib 4.32, `analyticAt_symm` lives only on `OpenPartialHomeomorph`,
so this proof uses the homeomorphism (which has `source = target = univ`,
hence is an `OpenPartialHomeomorph` via `toOpenPartialHomeomorph`) rather
than the partial homeomorphism used in the 4.14 version. -/
theorem keplerSolve_analytic {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) :
    AnalyticOnNhd ℝ (keplerSolve he) Set.univ := by
  intro M _
  let fO : OpenPartialHomeomorph ℝ ℝ := (keplerHomeomorph he).toOpenPartialHomeomorph
  have hM : M ∈ fO.target := by
    show M ∈ ((keplerHomeomorph he).toOpenPartialHomeomorph).target
    rw [Homeomorph.toOpenPartialHomeomorph]
    exact Set.mem_univ M
  have happly : ∀ x, fO x = keplerMap e x := by
    show ∀ x, ((keplerHomeomorph he).toOpenPartialHomeomorph) x = keplerMap e x
    intro x
    show ((keplerHomeomorph he).toOpenPartialHomeomorph) x = keplerMap e x
    -- ((keplerHomeomorph he).toOpenPartialHomeomorph) x
    --   = (keplerHomeomorph he).toPartialHomeomorph x   (since
    --   toOpenPartialHomeomorph's `apply` simp projection is the underlying
    --   toPartialHomeomorph's apply, which is the homeomorphism's apply).
    have hx : ((keplerHomeomorph he).toOpenPartialHomeomorph) x
        = ((keplerHomeomorph he).toOpenPartialHomeomorph).toPartialHomeomorph x := rfl
    rw [hx]
    change _ = keplerMap e x
    rw [Homeomorph.toOpenPartialHomeomorph]
    -- After unfolding: LHS is the coe-fn of the OpenPartialHomeomorph
    --   = coe-fn of its toPartialHomeomorph = coe-fn of Homeomorph.toPartialHomeomorph
    -- And we can use the CoeFn equation for toPartialHomeomorphOfImageEq.
    have h2 : ((keplerHomeomorph he).toOpenPartialHomeomorphOfImageEq (Set.univ : Set ℝ)
        isOpen_univ (Set.univ : Set ℝ)
        (by rw [Set.image_univ]; exact (keplerHomeomorph he).surjective.range_eq)).toPartialHomeomorph
        = (keplerHomeomorph he).toPartialHomeomorph := rfl
    rw [h2, Homeomorph.toPartialHomeomorph_apply, keplerHomeomorph_apply]
  have hE : AnalyticAt ℝ fO (fO.symm M) := by
    show AnalyticAt ℝ ((keplerHomeomorph he).toOpenPartialHomeomorph) (fO.symm M)
    have hmap := keplerMap_analytic e (fO.symm M) (Set.mem_univ _)
    refine hmap.congr (Filter.Eventually.of_forall (fun x => (happly x).symm))
  have hderiv : fderiv ℝ fO (fO.symm M) = keplerDerivEquiv he (fO.symm M) := by
    show fderiv ℝ ((keplerHomeomorph he).toOpenPartialHomeomorph) (fO.symm M)
        = keplerDerivEquiv he (fO.symm M)
    have heq : fderiv ℝ fO (fO.symm M) = fderiv ℝ (keplerMap e) (fO.symm M) :=
      Filter.EventuallyEq.fderiv_eq (Filter.Eventually.of_forall happly)
    rw [heq, keplerMap_fderiv_eq he]
  exact fO.analyticAt_symm hM hE hderiv

/-- **`keplerSolve`'s derivative**, needed for the chain-rule computation
of `dν/dM` in `PeriastronSharpness.lean`: `d(keplerSolve he)/dM =
(1 - e cos(keplerSolve he M))⁻¹`, the reciprocal of `keplerMap`'s own
derivative at the corresponding `E`, via the inverse function theorem's
easy direction. Same `OpenPartialHomeomorph` packaging as
`keplerSolve_analytic` above (see that theorem's docstring: in Mathlib
4.32, `hasDerivAt_symm`, like `analyticAt_symm`, lives only on
`OpenPartialHomeomorph`, not `PartialHomeomorph`). -/
theorem keplerSolve_hasDerivAt {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (M : ℝ) :
    HasDerivAt (keplerSolve he) (1 - e * Real.cos (keplerSolve he M))⁻¹ M := by
  let fO : OpenPartialHomeomorph ℝ ℝ := (keplerHomeomorph he).toOpenPartialHomeomorph
  have hM : M ∈ fO.target := by
    show M ∈ ((keplerHomeomorph he).toOpenPartialHomeomorph).target
    rw [Homeomorph.toOpenPartialHomeomorph]
    exact Set.mem_univ M
  have happly : ∀ x, fO x = keplerMap e x := by
    show ∀ x, ((keplerHomeomorph he).toOpenPartialHomeomorph) x = keplerMap e x
    intro x
    have hx : ((keplerHomeomorph he).toOpenPartialHomeomorph) x
        = ((keplerHomeomorph he).toOpenPartialHomeomorph).toPartialHomeomorph x := rfl
    rw [hx]
    change _ = keplerMap e x
    rw [Homeomorph.toOpenPartialHomeomorph]
    have h2 : ((keplerHomeomorph he).toOpenPartialHomeomorphOfImageEq (Set.univ : Set ℝ)
        isOpen_univ (Set.univ : Set ℝ)
        (by rw [Set.image_univ]; exact (keplerHomeomorph he).surjective.range_eq)).toPartialHomeomorph
        = (keplerHomeomorph he).toPartialHomeomorph := rfl
    rw [h2, Homeomorph.toPartialHomeomorph_apply, keplerHomeomorph_apply]
  have htff' : HasDerivAt fO (1 - e * Real.cos (fO.symm M)) (fO.symm M) :=
    (keplerMap_hasDerivAt e (fO.symm M)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun x => (happly x).symm))
  have hf'ne : (1 - e * Real.cos (fO.symm M)) ≠ 0 := ne_of_gt (keplerMap_deriv_pos he (fO.symm M))
  exact fO.hasDerivAt_symm hM hf'ne htff'

/-! ### Step 3: the Keplerian photometric atom, via the rational
("Gauss") true-anomaly identities -/

/-- The Keplerian atom, using the rational ("Gauss") form of the
true-anomaly identities instead of the paper's `tan(ν/2)` half-angle
formula — see this file's header docstring for why, and for the
justification that they agree wherever the paper's own formula is
defined. Here `e ∈ [0,1)` is the eccentricity, `ω` the argument of
periastron, and `E` the eccentric anomaly (itself `keplerSolve he M` for
mean anomaly `M`). -/
noncomputable def keplerAtomOfE (e ω E : ℝ) : ℝ :=
  Real.cos ω * ((Real.cos E - e) / (1 - e * Real.cos E))
    - Real.sin ω * (Real.sqrt (1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E))
    + e * Real.cos ω

/-- The Keplerian atom as a function of the mean anomaly `M` (equivalently,
up to the affine reparameterization `M(t) = n(t - T0)`, of time). -/
noncomputable def keplerAtom {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (ω M : ℝ) : ℝ :=
  keplerAtomOfE e ω (keplerSolve he M)

theorem keplerAtomOfE_analytic {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (ω : ℝ) :
    AnalyticOnNhd ℝ (keplerAtomOfE e ω) Set.univ := by
  have hdenom_ne : ∀ E ∈ (Set.univ : Set ℝ), 1 - e * Real.cos E ≠ 0 :=
    fun E _ => ne_of_gt (keplerMap_deriv_pos he E)
  have hnum1 : AnalyticOnNhd ℝ (fun E => Real.cos E - e) Set.univ :=
    real_cos_analyticOnNhd.sub analyticOnNhd_const
  have hdenom : AnalyticOnNhd ℝ (fun E => 1 - e * Real.cos E) Set.univ :=
    analyticOnNhd_const.sub (analyticOnNhd_const.mul real_cos_analyticOnNhd)
  have hterm1 : AnalyticOnNhd ℝ (fun E => Real.cos ω * ((Real.cos E - e) / (1 - e * Real.cos E)))
      Set.univ :=
    analyticOnNhd_const.mul (hnum1.div hdenom hdenom_ne)
  have hterm2 : AnalyticOnNhd ℝ
      (fun E => Real.sin ω * (Real.sqrt (1 - e ^ 2) * Real.sin E / (1 - e * Real.cos E)))
      Set.univ :=
    analyticOnNhd_const.mul
      ((analyticOnNhd_const.mul real_sin_analyticOnNhd).div hdenom hdenom_ne)
  have := (hterm1.sub hterm2).add (analyticOnNhd_const (𝕜 := ℝ) (v := e * Real.cos ω))
  exact this.congr isOpen_univ (fun E _ => by simp [keplerAtomOfE])

/-- **Main result of this file.** The Keplerian photometric atom is
real-analytic in the mean anomaly `M` (hence, since `M(t) = n(t - T0)` is
an affine reparameterization of time and composition with an affine map
preserves analyticity, in `t`). Composition of `keplerSolve_analytic`
(the analytic-IFT step) with `keplerAtomOfE_analytic` (a manifestly
analytic rational combination). -/
theorem keplerAtom_analytic {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (ω : ℝ) :
    AnalyticOnNhd ℝ (keplerAtom he ω) Set.univ := by
  have h : AnalyticOnNhd ℝ (keplerAtomOfE e ω ∘ keplerSolve he) Set.univ :=
    (keplerAtomOfE_analytic he ω).comp (keplerSolve_analytic he) (Set.mapsTo_univ _ _)
  exact h.congr isOpen_univ (fun M _ => rfl)

end KNOMP
