/-
KNOMP/VariableProjection.lean

Source: Section 15, "Correctness of Variable Projection", Theorem
"Envelope theorem for the profiled objective".

STATUS: PROVED.

Paper statement: profiling out the linear parameters `β` at their optimal
value `β̂(θ)` for each nonlinear parameter `θ`, then differentiating the
resulting profiled objective `h(θ) = J(β̂(θ), θ)` in `θ` alone, gives the
*same* derivative as differentiating `J` directly in `θ` at the optimum —
the term coming from `β̂`'s own dependence on `θ` drops out, because
`β̂(θ)` is a stationary point of `J(·, θ)` in the `β`-direction.

This is the classical envelope theorem. We formalize it abstractly for a
general `J : ℝ × ℝ → ℝ` (the paper's own `β, θ` are each vectors in
general, but the one-real-variable-each case already carries the entire
mathematical content — the chain rule plus one cancellation from the
first-order condition — with no loss beyond index bookkeeping, exactly
the same scope choice made in `IncrementalQRUpdate.lean`'s induction
step). -/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace KNOMP

open ContinuousLinearMap

variable (J : ℝ × ℝ → ℝ) (β : ℝ → ℝ) (θ₀ : ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) (β' : ℝ)

/-- **Envelope theorem.** If `J` is Fréchet differentiable at
`(β(θ₀), θ₀)` with derivative `L`, `β` is differentiable at `θ₀`, and
`(β(θ₀), θ₀)` is a stationary point of `J` in the `β`-direction
(`L (1,0) = 0` — the first-order condition satisfied by an interior
minimizer), then the profiled function `θ ↦ J(β(θ), θ)` has derivative at
`θ₀` equal to `L`'s `θ`-directional component alone, `L (0,1)` — the
`β`-dependence contributes nothing. -/
theorem envelope_theorem
    (hJ : HasFDerivAt J L (β θ₀, θ₀))
    (hβ : HasDerivAt β β' θ₀)
    (hstat : L (1, 0) = 0) :
    HasDerivAt (fun θ => J (β θ, θ)) (L (0, 1)) θ₀ := by
  have hcurve : HasDerivAt (fun θ => (β θ, θ)) (β', 1) θ₀ := hβ.prodMk (hasDerivAt_id θ₀)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun θ => (β θ, θ)) θ₀ hJ hcurve
  have hlin : ((β', (1:ℝ)) : ℝ × ℝ) = β' • ((1:ℝ), (0:ℝ)) + ((0:ℝ), (1:ℝ)) := by
    simp [Prod.ext_iff]
  rw [hlin, map_add, map_smul, hstat, smul_zero, zero_add] at hcomp
  exact hcomp

/-- The stationarity hypothesis above is exactly what an (unconstrained,
interior) minimizer of `J(·, θ₀)` satisfies: if `b ↦ J (b, θ₀)` has a
local minimum at `β θ₀`, its derivative there is `0`, which is precisely
`L (1,0) = 0` (the `β`-directional component of `J`'s derivative). This
connects the abstract hypothesis above to *why* it holds for a profiled
least-squares fit: in the paper's own application, `β̂(θ)` is defined by
the normal equations (`Common.lean`'s `normalEq_betaHat`), which are
exactly the first-order condition for minimizing a positive-definite
quadratic — the `β`-directional derivative there is identically zero for
the same reason `wls_optimality`'s gap term vanishes at `β = β̂(W)`. -/
theorem stationary_of_isLocalMin
    (hmin : IsLocalMin (fun b => J (b, θ₀)) (β θ₀))
    (hJb : HasDerivAt (fun b => J (b, θ₀)) (L (1, 0)) (β θ₀)) :
    L (1, 0) = 0 :=
  hmin.hasDerivAt_eq_zero hJb

end KNOMP
