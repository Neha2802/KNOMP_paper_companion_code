/-
KNOMP/KeplerFamily.lean

Source: Section 7 (`source/KNOMP_complete_proofs_1_.tex`, ~lines 960-1040),
Assumption `regularity` (R1)-(R3), as formalized abstractly in
`AsymptoticEfficiency.lean`'s `RegularityAssumption`. That structure is
stated over an arbitrary model family `μ : ℕ → ℝ → ℝ`; this file supplies
the actual concrete instance — a genuine, `d = 1` (period-only)
Keplerian observation family, built on `Kepler.lean`'s `keplerAtom` — and
uses it to turn R1 into a real, fully-proved theorem, and to state R2/R3
as concrete (not merely abstract-hint) honestly-open statements. See
`proposed_changes.md`'s "§7, Assumption `regularity`" entry and
`CLAUDE.md`'s "Open work" item 3 for the full motivation.

MODEL: the period-only refinement stage from the paper (`θ` = period `P`;
eccentricity `e`, argument of periastron `ω`, epoch `T0`, and linear gain
`K` held fixed at their true values — the same scalar-parameter
simplification already used in `VariableProjection.lean` /
`IncrementalQRUpdate.lean`). Design points `t : ℕ → ℝ` are assumed
confined to a FIXED, bounded observational baseline `[tmin, tmax]`
(`htbdd`). This is a new, explicit hypothesis not stated verbatim by the
paper, but it is the only physically sensible reading of "fixed design,
`N → ∞`" for this model: an *unbounded* baseline would make R1's uniform
bound false in general, since the period-derivative of mean anomaly grows
with elapsed time (`∂M/∂P = -2π(t-T0)/P²`, unbounded as `t-T0 → ∞`).
`N → ∞` must therefore mean increasing sampling density inside a fixed
window, not a growing window.

STATUS: R1 (`keplerFamily_uniform_third_deriv_bound`) is fully proved,
0 `sorry`. R2 and R3 are stated concretely against this family and left
honestly `sorry`'d, per house rule 2 (with docstrings explaining exactly
what is missing) — see each theorem's docstring below.
-/
import KNOMP.Kepler
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 1000000

namespace KNOMP

open Filter Topology
open scoped NNReal

variable {e : ℝ} (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K : ℝ)

/-- Mean anomaly of a period-only Keplerian model at observation time `s`,
as a function of the period `θ`: `M(s, θ) = (2π/θ)·(s - T0)`. Written with
`θ⁻¹` (rather than `/θ`) throughout this file to keep the derivative
chain-rule bookkeeping uniform. -/
noncomputable def meanAnomalyOfPeriod (T0 s θ : ℝ) : ℝ := 2 * Real.pi * (s - T0) * θ⁻¹

/-- The period-only Keplerian observation family: `μ_n(θ) = K · A(M(t_n, θ))`,
where `A = keplerAtom he ω` is the fixed Keplerian photometric atom (fixed
eccentricity/argument-of-periastron) and `t_n` is the (fixed) design point
of observation `n`. This is the concrete instance of the abstract
`μ : ℕ → ℝ → ℝ` that `RegularityAssumption` in `AsymptoticEfficiency.lean`
quantifies over. -/
noncomputable def keplerFamily (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K : ℝ) (t : ℕ → ℝ) (n : ℕ)
    (θ : ℝ) : ℝ :=
  K * keplerAtom he ω (meanAnomalyOfPeriod T0 (t n) θ)

/-! ### The `m`-chain: derivatives of `meanAnomalyOfPeriod` in `θ`

Elementary rational-function derivatives of `θ ↦ c·θ⁻¹` for a fixed
constant `c = 2π(s - T0)`, computed via repeated `hasDerivAt_inv` /
`hasDerivAt_pow` chain-rule steps. Closed forms:
`m' = -c·θ⁻²`, `m'' = 2c·θ⁻³`, `m''' = -6c·θ⁻⁴`. -/

theorem hasDerivAt_meanAnomalyOfPeriod (T0 s θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (meanAnomalyOfPeriod T0 s) (-(2 * Real.pi * (s - T0)) * (θ ^ 2)⁻¹) θ := by
  have h := (hasDerivAt_inv hθ).const_mul (2 * Real.pi * (s - T0))
  show HasDerivAt (fun θ => (2 * Real.pi * (s - T0)) * θ⁻¹)
      (-(2 * Real.pi * (s - T0)) * (θ ^ 2)⁻¹) θ
  have hfun : (fun y => (2 * Real.pi * (s - T0)) * y⁻¹) =ᶠ[𝓝 θ]
            (fun θ => (2 * Real.pi * (s - T0)) * θ⁻¹) := by
    filter_upwards with x; rfl
  have hval : ((2 * Real.pi * (s - T0)) * -(θ ^ 2)⁻¹)
            = (-(2 * Real.pi * (s - T0))) * (θ ^ 2)⁻¹ := by ring
  exact h.congr_of_eventuallyEq hfun |>.congr_deriv hval

/-- `m'(θ) = -c·θ⁻²`, as a standalone function of `θ` (for fixed `s`). -/
noncomputable def meanAnomalyDeriv1 (T0 s θ : ℝ) : ℝ := -(2 * Real.pi * (s - T0)) * (θ ^ 2)⁻¹

theorem hasDerivAt_meanAnomalyDeriv1 (T0 s θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (meanAnomalyDeriv1 T0 s) (2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹) θ := by
  have hp : HasDerivAt (fun θ : ℝ => θ ^ 2) (2 * θ) θ := by simpa using hasDerivAt_pow 2 θ
  have hinv := hp.inv (pow_ne_zero 2 hθ)
  have h := hinv.const_mul (-(2 * Real.pi * (s - T0)))
  have heq : -(2 * Real.pi * (s - T0)) * (-(2 * θ) / (θ ^ 2) ^ 2)
      = 2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹ := by
    have hθ2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ
    field_simp
  rw [heq] at h
  exact h

/-- `m''(θ) = 2c·θ⁻³`, as a standalone function of `θ` (for fixed `s`). -/
noncomputable def meanAnomalyDeriv2 (T0 s θ : ℝ) : ℝ := 2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹

theorem hasDerivAt_meanAnomalyDeriv2 (T0 s θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (meanAnomalyDeriv2 T0 s) (-6 * (2 * Real.pi * (s - T0)) * (θ ^ 4)⁻¹) θ := by
  have hp : HasDerivAt (fun θ : ℝ => θ ^ 3) (3 * θ ^ 2) θ := by simpa using hasDerivAt_pow 3 θ
  have hinv := hp.inv (pow_ne_zero 3 hθ)
  have h := hinv.const_mul (2 * (2 * Real.pi * (s - T0)))
  have heq : 2 * (2 * Real.pi * (s - T0)) * (-(3 * θ ^ 2) / (θ ^ 3) ^ 2)
      = -6 * (2 * Real.pi * (s - T0)) * (θ ^ 4)⁻¹ := by
    have hθ3 : θ ^ 3 ≠ 0 := pow_ne_zero 3 hθ
    field_simp
    ring
  rw [heq] at h
  exact h

/-- `m'''(θ) = -6c·θ⁻⁴`, as a standalone function of `θ` (for fixed `s`). -/
noncomputable def meanAnomalyDeriv3 (T0 s θ : ℝ) : ℝ := -6 * (2 * Real.pi * (s - T0)) * (θ ^ 4)⁻¹

/-! ### The `A`-chain: derivatives of `keplerAtom` (already analytic on
all of `ℝ`, per `Kepler.lean`). -/

theorem hasDerivAt_keplerAtom (he : e ∈ Set.Ico (0 : ℝ) 1) (ω x : ℝ) :
    HasDerivAt (keplerAtom he ω) (deriv (keplerAtom he ω) x) x :=
  ((keplerAtom_analytic he ω) x (Set.mem_univ x)).differentiableAt.hasDerivAt

theorem hasDerivAt_deriv_keplerAtom (he : e ∈ Set.Ico (0 : ℝ) 1) (ω x : ℝ) :
    HasDerivAt (deriv (keplerAtom he ω)) (deriv (deriv (keplerAtom he ω)) x) x :=
  (((keplerAtom_analytic he ω).deriv) x (Set.mem_univ x)).differentiableAt.hasDerivAt

theorem hasDerivAt_deriv_deriv_keplerAtom (he : e ∈ Set.Ico (0 : ℝ) 1) (ω x : ℝ) :
    HasDerivAt (deriv (deriv (keplerAtom he ω))) (deriv (deriv (deriv (keplerAtom he ω))) x) x :=
  (((keplerAtom_analytic he ω).deriv.deriv) x (Set.mem_univ x)).differentiableAt.hasDerivAt

theorem continuous_keplerAtom_derivs (he : e ∈ Set.Ico (0 : ℝ) 1) (ω : ℝ) :
    Continuous (keplerAtom he ω) ∧ Continuous (deriv (keplerAtom he ω)) ∧
      Continuous (deriv (deriv (keplerAtom he ω))) ∧
      Continuous (deriv (deriv (deriv (keplerAtom he ω)))) :=
  ⟨(keplerAtom_analytic he ω).continuous, (keplerAtom_analytic he ω).deriv.continuous,
    (keplerAtom_analytic he ω).deriv.deriv.continuous,
    (keplerAtom_analytic he ω).deriv.deriv.deriv.continuous⟩

/-! ### Faà di Bruno, order 3, assembled by hand for `g(θ) := K · A(m(s, θ))` -/

section FaaDiBruno

variable (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K s : ℝ)

/-- The un-uniformized family at a fixed observation time `s` (i.e.
`keplerFamily` with `t n` replaced by the free variable `s`). -/
noncomputable def gAt (θ : ℝ) : ℝ := K * keplerAtom he ω (meanAnomalyOfPeriod T0 s θ)

local notation "A" => keplerAtom he ω
local notation "A'" => deriv (keplerAtom he ω)
local notation "A''" => deriv (deriv (keplerAtom he ω))
local notation "A'''" => deriv (deriv (deriv (keplerAtom he ω)))
local notation "m" => meanAnomalyOfPeriod T0 s
local notation "m'" => meanAnomalyDeriv1 T0 s
local notation "m''" => meanAnomalyDeriv2 T0 s
local notation "m'''" => meanAnomalyDeriv3 T0 s

theorem hasDerivAt_gAt (θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (gAt he ω T0 K s) (K * (A' (m θ) * m' θ)) θ := by
  have hchain : HasDerivAt (fun θ => A (m θ)) (A' (m θ) * m' θ) θ :=
    (hasDerivAt_keplerAtom he ω (m θ)).comp θ (hasDerivAt_meanAnomalyOfPeriod T0 s θ hθ)
  show HasDerivAt (gAt he ω T0 K s) (K * (A' (m θ) * m' θ)) θ
  have h := hchain.const_mul K
  have hfun : (fun y => K * A (m y)) =ᶠ[𝓝 θ] gAt he ω T0 K s := by
    filter_upwards with x; rfl
  exact h.congr_of_eventuallyEq hfun

/-- `deriv (gAt he ω T0 K s)` agrees with the explicit formula
`fun θ => K * (A' (m θ) * m' θ)` on the open set `{θ | θ ≠ 0}`. -/
theorem deriv_gAt_eventuallyEq (θ : ℝ) (hθ : θ ≠ 0) :
    deriv (gAt he ω T0 K s) =ᶠ[𝓝 θ] fun θ => K * (A' (m θ) * m' θ) := by
  filter_upwards [isOpen_ne.eventually_mem hθ] with θ' hθ'
  exact (hasDerivAt_gAt he ω T0 K s θ' hθ').deriv

theorem hasDerivAt_deriv_gAt (θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (deriv (gAt he ω T0 K s))
      (K * (A'' (m θ) * m' θ ^ 2 + A' (m θ) * m'' θ)) θ := by
  have hchain : HasDerivAt (fun θ => A' (m θ)) (A'' (m θ) * m' θ) θ :=
    (hasDerivAt_deriv_keplerAtom he ω (m θ)).comp θ (hasDerivAt_meanAnomalyOfPeriod T0 s θ hθ)
  have hprod : HasDerivAt (fun θ => A' (m θ) * m' θ)
      (A'' (m θ) * m' θ * m' θ + A' (m θ) * m'' θ) θ :=
    hchain.mul (hasDerivAt_meanAnomalyDeriv1 T0 s θ hθ)
  have hfinal : HasDerivAt (fun θ => K * (A' (m θ) * m' θ))
      (K * (A'' (m θ) * m' θ * m' θ + A' (m θ) * m'' θ)) θ := hprod.const_mul K
  have heq : K * (A'' (m θ) * m' θ * m' θ + A' (m θ) * m'' θ)
      = K * (A'' (m θ) * m' θ ^ 2 + A' (m θ) * m'' θ) := by ring
  rw [heq] at hfinal
  exact hfinal.congr_of_eventuallyEq (deriv_gAt_eventuallyEq he ω T0 K s θ hθ)

/-- `deriv (deriv (gAt he ω T0 K s))` agrees with the explicit formula on
`{θ | θ ≠ 0}`. -/
theorem deriv_deriv_gAt_eventuallyEq (θ : ℝ) (hθ : θ ≠ 0) :
    deriv (deriv (gAt he ω T0 K s)) =ᶠ[𝓝 θ]
      fun θ => K * (A'' (m θ) * m' θ ^ 2 + A' (m θ) * m'' θ) := by
  filter_upwards [isOpen_ne.eventually_mem hθ] with θ' hθ'
  exact (hasDerivAt_deriv_gAt he ω T0 K s θ' hθ').deriv

theorem hasDerivAt_deriv_deriv_gAt (θ : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (deriv (deriv (gAt he ω T0 K s)))
      (K * (A''' (m θ) * m' θ ^ 3 + 3 * (A'' (m θ) * m' θ * m'' θ) + A' (m θ) * m''' θ)) θ := by
  have hchainA'' : HasDerivAt (fun θ => A'' (m θ)) (A''' (m θ) * m' θ) θ :=
    (hasDerivAt_deriv_deriv_keplerAtom he ω (m θ)).comp θ
      (hasDerivAt_meanAnomalyOfPeriod T0 s θ hθ)
  have hterm1 : HasDerivAt (fun θ => A'' (m θ) * m' θ ^ 2)
      (A''' (m θ) * m' θ * m' θ ^ 2 + A'' (m θ) * (2 * m' θ * m'' θ)) θ := by
    have hsq : HasDerivAt (fun θ => m' θ ^ 2) (2 * m' θ * m'' θ) θ := by
      have h := (hasDerivAt_meanAnomalyDeriv1 T0 s θ hθ).mul
        (hasDerivAt_meanAnomalyDeriv1 T0 s θ hθ)
      have heq1 : (m' * m') = (fun θ => m' θ ^ 2) := by
        funext θ; show m' θ * m' θ = m' θ ^ 2; rw [sq]
      rw [heq1] at h
      have heq2 : 2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹ * m' θ
          + m' θ * (2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹) = 2 * m' θ * m'' θ := by
        show 2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹ * m' θ
            + m' θ * (2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹)
          = 2 * m' θ * (2 * (2 * Real.pi * (s - T0)) * (θ ^ 3)⁻¹)
        ring
      rwa [heq2] at h
    exact hchainA''.mul hsq
  have hterm2 : HasDerivAt (fun θ => A' (m θ) * m'' θ)
      (A'' (m θ) * m' θ * m'' θ + A' (m θ) * m''' θ) θ := by
    have hchainA' : HasDerivAt (fun θ => A' (m θ)) (A'' (m θ) * m' θ) θ :=
      (hasDerivAt_deriv_keplerAtom he ω (m θ)).comp θ (hasDerivAt_meanAnomalyOfPeriod T0 s θ hθ)
    exact hchainA'.mul (hasDerivAt_meanAnomalyDeriv2 T0 s θ hθ)
  have hsum : HasDerivAt (fun θ => A'' (m θ) * m' θ ^ 2 + A' (m θ) * m'' θ)
      ((A''' (m θ) * m' θ * m' θ ^ 2 + A'' (m θ) * (2 * m' θ * m'' θ))
        + (A'' (m θ) * m' θ * m'' θ + A' (m θ) * m''' θ)) θ :=
    hterm1.add hterm2
  have hfinal : HasDerivAt (fun θ => K * (A'' (m θ) * m' θ ^ 2 + A' (m θ) * m'' θ))
      (K * ((A''' (m θ) * m' θ * m' θ ^ 2 + A'' (m θ) * (2 * m' θ * m'' θ))
        + (A'' (m θ) * m' θ * m'' θ + A' (m θ) * m''' θ))) θ := hsum.const_mul K
  have heq : K * ((A''' (m θ) * m' θ * m' θ ^ 2 + A'' (m θ) * (2 * m' θ * m'' θ))
        + (A'' (m θ) * m' θ * m'' θ + A' (m θ) * m''' θ))
      = K * (A''' (m θ) * m' θ ^ 3 + 3 * (A'' (m θ) * m' θ * m'' θ) + A' (m θ) * m''' θ) := by
    ring
  rw [heq] at hfinal
  exact hfinal.congr_of_eventuallyEq (deriv_deriv_gAt_eventuallyEq he ω T0 K s θ hθ)

/-- **Order-3 Faà di Bruno, closed form.** The third derivative of
`gAt he ω T0 K s` at `θ ≠ 0`, as the standard 3-term composition formula
`K·(A'''(m)·m'³ + 3·A''(m)·m'·m'' + A'(m)·m''')`. -/
theorem iteratedDeriv_three_gAt (θ : ℝ) (hθ : θ ≠ 0) :
    iteratedDeriv 3 (gAt he ω T0 K s) θ
      = K * (A''' (m θ) * m' θ ^ 3 + 3 * (A'' (m θ) * m' θ * m'' θ) + A' (m θ) * m''' θ) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_deriv_gAt he ω T0 K s θ hθ).deriv

end FaaDiBruno

/-! ### R1: the uniform-in-`n` third-derivative bound, for real -/

/-- Local extreme-value-theorem helper: a continuous function on a
compact, nonempty set is bounded there. Same technique as
`AsymptoticEfficiency.lean`'s `bound_iteratedDeriv_of_continuousOn_of_isCompact`,
inlined here (rather than imported) to avoid a Kepler↔AsymptoticEfficiency
import cycle — `AsymptoticEfficiency.lean` will instead gain a
cross-reference *sentence* pointing at this file. -/
private theorem bound_of_continuousOn_of_isCompact {f : ℝ → ℝ} {Θ : Set ℝ}
    (hΘ : IsCompact Θ) (hΘne : Θ.Nonempty) (hcont : ContinuousOn f Θ) :
    ∃ C : ℝ, ∀ θ ∈ Θ, |f θ| ≤ C := by
  obtain ⟨x, hx, hmax⟩ := hΘ.exists_isMaxOn hΘne hcont.abs
  exact ⟨|f x|, fun θ hθ => isMaxOn_iff.mp hmax θ hθ⟩

/-- **R1, fully proved for the concrete Keplerian family.** For a fixed
eccentricity/argument-of-periastron/epoch/gain, and design points `t`
confined to a fixed observational baseline `[tmin, tmax]` (`htbdd` — see
this file's header docstring for why this hypothesis, absent from the
paper's literal statement, is nonetheless necessary and physically
sensible), the third derivative of `keplerFamily` at any period
`θ ∈ [θmin, θmax]` (`θmin > 0`) is bounded by a SINGLE constant `C3`
independent of the observation index `n` — exactly R1's content, as
opposed to the strictly weaker "bounded for each fixed `n`" fact, which
would follow from compactness alone with no uniformity argument at all.

Proof idea: `A = keplerAtom he ω`'s 0th-3rd derivatives are continuous on
all of `ℝ` (it is real-analytic everywhere, `keplerAtom_analytic`), hence
bounded on the compact interval `[Mlo, Mhi]` that the mean anomaly
`m(t_n, θ)` is confined to as `(t_n, θ)` ranges over `[tmin,tmax]×[θmin,θmax]`
(an explicit, elementary bound from `m`'s closed form). The `m`-chain's
own derivatives `m', m'', m'''` are elementary rational functions of `θ`
alone (bounded directly since `θ ≥ θmin > 0`) and of `t_n - T0` (bounded
since `t_n ∈ [tmin,tmax]`). Combining both bounds through the Faà di
Bruno closed form (`iteratedDeriv_three_gAt`) via the triangle inequality
gives a single `C3` that depends only on `e, ω, T0, K, tmin, tmax, θmin,
θmax` — not on `n`. -/
theorem keplerFamily_uniform_third_deriv_bound (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K : ℝ)
    (t : ℕ → ℝ) {tmin tmax θmin θmax : ℝ} (hθmin : 0 < θmin)
    (htbdd : ∀ n, t n ∈ Set.Icc tmin tmax) :
    ∃ C3 : ℝ, ∀ n : ℕ, ∀ θ ∈ Set.Icc θmin θmax,
      |iteratedDeriv 3 (keplerFamily he ω T0 K t n) θ| ≤ C3 := by
  -- `Tbd` bounds `|t n - T0|` for every `n`, since `t n ∈ [tmin, tmax]`.
  set Tbd : ℝ := |tmax - T0| + |tmin - T0| with hTbddef
  have hTbd : ∀ n, |t n - T0| ≤ Tbd := by
    intro n
    rcases htbdd n with ⟨h1, h2⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [neg_abs_le (tmin - T0), abs_nonneg (tmax - T0), hTbddef]
    · linarith [le_abs_self (tmax - T0), abs_nonneg (tmin - T0), hTbddef]
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  -- `Mbd` bounds `|m (t n) θ|` for every `n` and every `θ ∈ [θmin, θmax]`.
  set Mbd : ℝ := 2 * Real.pi * Tbd * θmin⁻¹ with hMbddef
  have hMbd_nonneg : 0 ≤ Mbd := by
    have hTbd_nonneg : 0 ≤ Tbd := by positivity
    positivity
  have hmbound : ∀ n, ∀ θ ∈ Set.Icc θmin θmax,
      |meanAnomalyOfPeriod T0 (t n) θ| ≤ Mbd := by
    intro n θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le hθmin hθ.1
    have hθinv : θ⁻¹ ≤ θmin⁻¹ := by
      apply inv_anti₀ hθmin hθ.1
    unfold meanAnomalyOfPeriod
    rw [abs_mul, abs_mul]
    have h1 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos hpi
    rw [h1]
    have h2 : |θ⁻¹| = θ⁻¹ := abs_of_pos (inv_pos.mpr hθpos)
    rw [h2]
    calc 2 * Real.pi * |t n - T0| * θ⁻¹
        ≤ 2 * Real.pi * Tbd * θ⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hθpos))
          exact mul_le_mul_of_nonneg_left (hTbd n) (le_of_lt hpi)
      _ ≤ 2 * Real.pi * Tbd * θmin⁻¹ := by
          apply mul_le_mul_of_nonneg_left hθinv
          positivity
  -- extreme value theorem for `A`'s 0th–3rd derivatives on the compact `[-Mbd, Mbd]`.
  have hMbdIcc : (Set.Icc (-Mbd) Mbd).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨CA1, hCA1⟩ := bound_of_continuousOn_of_isCompact isCompact_Icc hMbdIcc
    ((continuous_keplerAtom_derivs he ω).2.1.continuousOn (s := Set.Icc (-Mbd) Mbd))
  obtain ⟨CA2, hCA2⟩ := bound_of_continuousOn_of_isCompact isCompact_Icc hMbdIcc
    ((continuous_keplerAtom_derivs he ω).2.2.1.continuousOn (s := Set.Icc (-Mbd) Mbd))
  obtain ⟨CA3, hCA3⟩ := bound_of_continuousOn_of_isCompact isCompact_Icc hMbdIcc
    ((continuous_keplerAtom_derivs he ω).2.2.2.continuousOn (s := Set.Icc (-Mbd) Mbd))
  -- explicit bounds on `m', m'', m'''`.
  set B1 : ℝ := 2 * Real.pi * Tbd * θmin⁻¹ ^ 2 with hB1def
  set B2 : ℝ := 4 * Real.pi * Tbd * θmin⁻¹ ^ 3 with hB2def
  set B3 : ℝ := 12 * Real.pi * Tbd * θmin⁻¹ ^ 4 with hB3def
  have hm1bound : ∀ n, ∀ θ ∈ Set.Icc θmin θmax, |meanAnomalyDeriv1 T0 (t n) θ| ≤ B1 := by
    intro n θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le hθmin hθ.1
    have hθinv : θ⁻¹ ≤ θmin⁻¹ := inv_anti₀ hθmin hθ.1
    unfold meanAnomalyDeriv1
    rw [abs_mul, abs_neg, abs_mul]
    have h1 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos hpi
    rw [h1]
    have h2 : |(θ ^ 2)⁻¹| = θ⁻¹ ^ 2 := by
      rw [abs_of_pos (inv_pos.mpr (by positivity)), inv_pow]
    rw [h2]
    calc 2 * Real.pi * |t n - T0| * θ⁻¹ ^ 2
        ≤ 2 * Real.pi * Tbd * θ⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hTbd n) (le_of_lt hpi)
      _ ≤ 2 * Real.pi * Tbd * θmin⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
  have hm2bound : ∀ n, ∀ θ ∈ Set.Icc θmin θmax, |meanAnomalyDeriv2 T0 (t n) θ| ≤ B2 := by
    intro n θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le hθmin hθ.1
    have hθinv : θ⁻¹ ≤ θmin⁻¹ := inv_anti₀ hθmin hθ.1
    unfold meanAnomalyDeriv2
    rw [abs_mul, abs_mul, abs_mul]
    have h0 : |(2:ℝ)| = 2 := by norm_num
    have h1 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos hpi
    rw [h0, h1]
    have h2 : |(θ ^ 3)⁻¹| = θ⁻¹ ^ 3 := by
      rw [abs_of_pos (inv_pos.mpr (by positivity)), inv_pow]
    rw [h2]
    calc 2 * (2 * Real.pi * |t n - T0|) * θ⁻¹ ^ 3
        ≤ 2 * (2 * Real.pi * Tbd) * θ⁻¹ ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hTbd n) (le_of_lt hpi)
      _ ≤ 2 * (2 * Real.pi * Tbd) * θmin⁻¹ ^ 3 := by
          apply mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
      _ = B2 := by rw [hB2def]; ring
  have hm3bound : ∀ n, ∀ θ ∈ Set.Icc θmin θmax, |meanAnomalyDeriv3 T0 (t n) θ| ≤ B3 := by
    intro n θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le hθmin hθ.1
    have hθinv : θ⁻¹ ≤ θmin⁻¹ := inv_anti₀ hθmin hθ.1
    unfold meanAnomalyDeriv3
    rw [abs_mul, abs_mul, abs_mul, abs_neg]
    have h0 : |(6:ℝ)| = 6 := by norm_num
    have h1 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos hpi
    rw [h0, h1]
    have h2 : |(θ ^ 4)⁻¹| = θ⁻¹ ^ 4 := by
      rw [abs_of_pos (inv_pos.mpr (by positivity)), inv_pow]
    rw [h2]
    calc 6 * (2 * Real.pi * |t n - T0|) * θ⁻¹ ^ 4
        ≤ 6 * (2 * Real.pi * Tbd) * θ⁻¹ ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hTbd n) (le_of_lt hpi)
      _ ≤ 6 * (2 * Real.pi * Tbd) * θmin⁻¹ ^ 4 := by
          apply mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
      _ = B3 := by rw [hB3def]; ring
  -- assemble the final uniform bound.
  refine ⟨|K| * (CA3 * B1 ^ 3 + 3 * (CA2 * B1 * B2) + CA1 * B3), fun n θ hθ => ?_⟩
  have hθne : θ ≠ 0 := ne_of_gt (lt_of_lt_of_le hθmin hθ.1)
  have hfun : keplerFamily he ω T0 K t n = gAt he ω T0 K (t n) := rfl
  rw [hfun, iteratedDeriv_three_gAt he ω T0 K (t n) θ hθne]
  have hmmem : meanAnomalyOfPeriod T0 (t n) θ ∈ Set.Icc (-Mbd) Mbd := by
    have := hmbound n θ hθ
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩
  have hA1 := hCA1 _ hmmem
  have hA2 := hCA2 _ hmmem
  have hA3 := hCA3 _ hmmem
  have hM1 := hm1bound n θ hθ
  have hM2 := hm2bound n θ hθ
  have hM3 := hm3bound n θ hθ
  have hM1nn : 0 ≤ |meanAnomalyDeriv1 T0 (t n) θ| := abs_nonneg _
  set A3v := deriv (deriv (deriv (keplerAtom he ω))) (meanAnomalyOfPeriod T0 (t n) θ)
  set A2v := deriv (deriv (keplerAtom he ω)) (meanAnomalyOfPeriod T0 (t n) θ)
  set A1v := deriv (keplerAtom he ω) (meanAnomalyOfPeriod T0 (t n) θ)
  set m1v := meanAnomalyDeriv1 T0 (t n) θ
  set m2v := meanAnomalyDeriv2 T0 (t n) θ
  set m3v := meanAnomalyDeriv3 T0 (t n) θ
  have htri : |A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v) + A1v * m3v|
      ≤ |A3v * m1v ^ 3| + |3 * (A2v * m1v * m2v)| + |A1v * m3v| := by
    have h1 : |A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v) + A1v * m3v|
        ≤ |A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v)| + |A1v * m3v| := norm_add_le
      (A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v)) (A1v * m3v)
    have h2 : |A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v)|
        ≤ |A3v * m1v ^ 3| + |3 * (A2v * m1v * m2v)| := norm_add_le
      (A3v * m1v ^ 3) (3 * (A2v * m1v * m2v))
    linarith
  calc |K * (A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v) + A1v * m3v)|
      = |K| * |A3v * m1v ^ 3 + 3 * (A2v * m1v * m2v) + A1v * m3v| := abs_mul _ _
    _ ≤ |K| * (|A3v * m1v ^ 3| + |3 * (A2v * m1v * m2v)| + |A1v * m3v|) := by
        gcongr
    _ = |K| * (|A3v| * |m1v| ^ 3 + 3 * (|A2v| * |m1v| * |m2v|) + |A1v| * |m3v|) := by
        rw [abs_mul, abs_pow, abs_mul, abs_mul, abs_mul, abs_mul,
          show |(3:ℝ)| = 3 from by norm_num]
    _ ≤ |K| * (CA3 * B1 ^ 3 + 3 * (CA2 * B1 * B2) + CA1 * B3) := by
        have hCA1nn : 0 ≤ CA1 := (abs_nonneg _).trans hA1
        have hCA2nn : 0 ≤ CA2 := (abs_nonneg _).trans hA2
        have hCA3nn : 0 ≤ CA3 := (abs_nonneg _).trans hA3
        have hB1nn : 0 ≤ B1 := (abs_nonneg _).trans hM1
        have hB2nn : 0 ≤ B2 := (abs_nonneg _).trans hM2
        have hB3nn : 0 ≤ B3 := (abs_nonneg _).trans hM3
        gcongr

/-! ### R2: normalized Fisher information convergence, for real -/

/-- **R2, stated concretely for the Keplerian family — honestly `sorry`'d.**
The paper's (R2) asserts convergence of the normalized Fisher information
to a fixed positive limit `I0`, but as `proposed_changes.md` already
flags, this assertion has **no content at all** without some assumption
on how the design points `t` fill the observation window `[tmin, tmax]`
as `N → ∞` — the paper's prose never supplies one, and nothing in this
codebase currently does either.

`hequidist` supplies exactly that missing ingredient, in the most
standard form used in this literature: an "asymptotic equidistribution"
hypothesis stating that Cesàro (running-mean) averages of *any* continuous
test function `φ` along the design sequence `t` converge to *some* limit
`L`. This is deliberately weak (it does not commit to a specific limiting
design density, e.g. uniform on `[tmin,tmax]`) so that it is satisfied by
several different reasonable models of "how the observer chose `t`" (a
fixed deterministic grid, an i.i.d. sample from a fixed density, etc.) —
but choosing a *specific* one, and hence pinning down what `I0` actually
*is* in closed form, is a genuine modeling decision this file does not
make. Even granting `hequidist`, concluding the literal Fisher-information
statement below needs: (a) recognizing the test function
`φ(s) := (K · deriv (keplerAtom he ω) (meanAnomalyOfPeriod T0 s θ0) ·
meanAnomalyDeriv1 T0 s θ0)²` as continuous on `[tmin,tmax]` (true, by the
same continuity facts used for R1 — not the obstruction), and (b)
showing the resulting Cesàro limit is strictly positive and equals the
SAME `I0` appearing elsewhere in `AsymptoticEfficiency.lean`'s `lemma_wu`
— genuinely open, unattempted content. Left `sorry`. -/
theorem keplerFamily_fisher_info_converges
    (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K θ0 σ : ℝ) (t : ℕ → ℝ)
    {tmin tmax : ℝ} (hθ0 : θ0 ≠ 0) (I0 : ℝ≥0)
    (hequidist : ∀ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc tmin tmax) →
      ∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, φ (t n))
        atTop (𝓝 L)) :
    0 < I0 ∧
      Tendsto (fun N : ℕ => σ⁻¹ ^ 2 * (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, (deriv (keplerFamily he ω T0 K t n) θ0) ^ 2)
        atTop (𝓝 (I0 : ℝ)) := by
  sorry

/-! ### R3: limiting-criterion separation, for real -/

/-- **R3, stated concretely for the Keplerian family — honestly `sorry`'d.**
The paper's own justification for (R3) is an "almost-periodic-function
uniqueness argument already used in the proof of Theorem
`identifiability`" — i.e. it is NOT independent open content, it is
exactly `Identifiability.lean`'s still-open general-`k ≥ 1` case of `hli`
(`{1, t, t², f_1, ..., f_k}` linearly independent for pairwise-distinct
periods; see that file's docstring and `CLAUDE.md`'s "Open work" item 1),
viewed here from Section 7 instead of Section 4. Discharging this
`sorry` for the real model is expected to reduce to that same Vandermonde-
plus-Fourier argument, not to require separate new mathematics.

Quantitatively, per `unique_minimizer_of_quadratic_lower_bound`'s
docstring in `AsymptoticEfficiency.lean`, the honest target is stronger
than the paper's qualitative "unique minimizer" phrasing: a genuine proof
would need a quadratic (or better) lower separation `c·(θ-θ0)² ≤ L(θ) -
L(θ0)`, not just strict inequality, to support the rest of Section 7's
finite-sample arguments — this statement only asks for the qualitative
form, matching `RegularityAssumption.unique_limiting_minimizer`'s own
(also qualitative) shape, so even fully discharging this `sorry` would
not by itself close that further quantitative gap. -/
theorem keplerFamily_limiting_criterion_separation
    (he : e ∈ Set.Ico (0 : ℝ) 1) (ω T0 K θ0 : ℝ) (t : ℕ → ℝ)
    {θmin θmax : ℝ} (hθmin : 0 < θmin) (hθ0mem : θ0 ∈ Set.Icc θmin θmax) :
    ∃ L : ℝ → ℝ,
      (∀ θ ∈ Set.Icc θmin θmax, Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (keplerFamily he ω T0 K t n θ - keplerFamily he ω T0 K t n θ0) ^ 2)
        atTop (𝓝 (L θ))) ∧
      (∀ θ ∈ Set.Icc θmin θmax, θ ≠ θ0 → L θ0 < L θ) := by
  sorry

end KNOMP
