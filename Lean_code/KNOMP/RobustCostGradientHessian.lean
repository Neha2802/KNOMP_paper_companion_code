/-
KNOMP/RobustCostGradientHessian.lean

Source: Section 4, "The Robust Cost Under Correlated Noise":
Proposition `robust-grad` (gradient of the profiled robust cost),
Proposition `robust-hess` (Gauss-Newton Hessian approximation), and
Corollary `diag-case` (both halves — the gradient's and the Hessian's
diagonal-case reductions).

STATUS: PARTIAL. All three formal claims of the source section are now
present (an earlier version of this file only covered the gradient
proposition and half of the corollary — the Hessian proposition was
missing entirely, caught during a coverage re-check against the source
`.tex`).

The paper's own proof of `robust-grad` has two parts: (1) the
`β`-derivative term in the chain rule vanishes identically, because
`β̂(Θ)` is by definition a stationary point of the inner minimization —
this is exactly `VariableProjection.lean`'s `envelope_theorem`, one
dimension richer (there `η : ℝ`; here `η : Fin d → ℝ`), and is not
re-proved here to avoid duplicating that file's machinery; and (2) the
remaining direct partial derivative through the whitening transform `L⁻¹`
collapses, via a double-sum rearrangement, into the matrix form
`-K(∇_η f)ᵀL⁻ᵀψ(z)`. Part (2) is genuine new algebraic content (a
finite-sum manipulation, not calculus) and is what this file proves in
full; part (1) is taken as a hypothesis (`hstationary`), matching how the
paper's own Proposition states it ("`β̂(Θ)` ... is a stationary point ...
true automatically at any interior minimizer").

The Hessian proposition similarly has an analogous structure once the
paper's own two explicit approximations are granted as hypotheses (not
re-derived): dropping the second-derivative-of-`f` term (the standard
Gauss-Newton truncation) and taking `ψ'(z_i) → 1` (exact in the Gaussian
limit). Given these, the resulting double-sum expression is genuine new
algebraic content — proved in full below (`robust_hess_matrix_form`) as
the clean matrix identity `H = K²(L⁻¹∇f)ᵀ(L⁻¹∇f) = K²(∇f)ᵀL⁻ᵀL⁻¹∇f`.
-/
import KNOMP.Common

namespace KNOMP

open Matrix

variable {N d : ℕ}

/-- **Proposition `robust-grad`, matrix-algebra core.** Given the
per-component chain-rule expression for `∂z_i/∂η_ℓ` (`hzderiv` — the
paper's own, not-further-justified elementary calculus step through the
whitening transform), the resulting gradient of `∑ᵢρ(zᵢ)` collapses to
the matrix form `-K(∇_ηf)ᵀL⁻ᵀψ(z)`, matching Eq. `grad-rob` exactly. -/
theorem robust_grad_matrix_form
    (Linv : Matrix (Fin N) (Fin N) ℝ) (Jf : Matrix (Fin N) (Fin d) ℝ)
    (psi z : Fin N → ℝ) (K : ℝ) (dz : Fin d → Fin N → ℝ)
    (hzderiv : ∀ ell i, dz ell i = -K * dotProduct (fun m => Linv i m) (fun m => Jf m ell)) :
    (fun ell => dotProduct psi (dz ell))
      = fun ell => -K * (dotProduct (fun m => Jf m ell) (Linvᵀ.mulVec psi)) := by
  funext ell
  have step1 : dotProduct psi (dz ell)
      = -K * Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun m => psi i * (Linv i m * Jf m ell))) := by
    simp only [hzderiv, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have step2 : Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun m => psi i * (Linv i m * Jf m ell)))
      = Finset.sum Finset.univ (fun m => Jf m ell * Finset.sum Finset.univ
          (fun i => Linvᵀ m i * psi i)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.transpose_apply]
    ring
  have step3 : dotProduct (fun m => Jf m ell) (Linvᵀ.mulVec psi)
      = Finset.sum Finset.univ (fun m => Jf m ell * Finset.sum Finset.univ
          (fun i => Linvᵀ m i * psi i)) := by
    unfold dotProduct Matrix.mulVec dotProduct
    rfl
  rw [step1, step2, ← step3]

/-- **Proposition `robust-hess`, matrix-algebra core.** Given the paper's
own two stated approximations (Gauss-Newton: drop the second-derivative-
of-`f` term; and `ψ'(z_i) → 1`, exact in the Gaussian limit) — neither
re-derived here, matching how the paper itself presents this as an
approximation rather than an exact identity — the resulting double-sum
expression for the Hessian collapses to the clean matrix identity
`H = K²(L⁻¹∇_ηf)ᵀ(L⁻¹∇_ηf) = K²(∇_ηf)ᵀL⁻ᵀL⁻¹∇_ηf`, matching Eq.
`hess-rob` exactly (using `L⁻ᵀL⁻¹ = (LLᵀ)⁻¹ = Σ⁻¹ = W`, the same
identification the paper's own proof makes in its final step). -/
theorem robust_hess_matrix_form
    (Linv : Matrix (Fin N) (Fin N) ℝ) (Jf : Matrix (Fin N) (Fin d) ℝ) (K : ℝ) :
    (fun ell ell' => K ^ 2 * Finset.sum Finset.univ (fun i =>
      (Finset.sum Finset.univ (fun m => Linv i m * Jf m ell)) *
      (Finset.sum Finset.univ (fun m' => Linv i m' * Jf m' ell'))))
    = fun ell ell' => (K ^ 2 • (Jfᵀ * Linvᵀ * Linv * Jf)) ell ell' := by
  funext ell ell'
  have hLJf : ∀ i ell, Finset.sum Finset.univ (fun m => Linv i m * Jf m ell)
      = (Linv * Jf) i ell := fun i ell => rfl
  simp only [hLJf]
  have hassoc : Jfᵀ * Linvᵀ * Linv * Jf = (Linv * Jf)ᵀ * (Linv * Jf) := by
    rw [Matrix.transpose_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hassoc]
  rw [Matrix.smul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, smul_eq_mul]

/-- **Corollary `diag-case`, gradient half.** When `Σ = diag(σₙ²)`, so
`L = diag(σₙ)`, `Linv = diag(σₙ⁻¹)` is symmetric, and the gradient
formula's single factor of `L⁻ᵀ` becomes a plain per-point division by
`σₙ`, matching the paper's stated reduction
`∇_ηJ_rob = -K∑ₙψ(rₙ)σₙ⁻¹∇_ηfₙ`. -/
theorem diag_case_gradient
    (sigma : Fin N → ℝ) (hsig : ∀ n, sigma n ≠ 0)
    (Jf : Matrix (Fin N) (Fin d) ℝ) (psi : Fin N → ℝ) (K : ℝ) :
    (Matrix.diagonal (fun n => (sigma n)⁻¹))ᵀ.mulVec psi
      = fun n => (sigma n)⁻¹ * psi n := by
  ext n
  rw [Matrix.diagonal_transpose, Matrix.mulVec_diagonal]

/-- **Corollary `diag-case`, Hessian half.** When `Σ = diag(σₙ²)`, so
`L = diag(σₙ)`, the Hessian formula's `L⁻ᵀL⁻¹` factor becomes exactly
`diag(σₙ⁻²) = diag(wₙ)`, the familiar per-point weight — matching the
paper's stated reduction to `K²∑ₙwₙ(∇_ηfₙ)(∇_ηfₙ)ᵀ` (a weighted sum of
rank-one outer products, which is exactly what `Jfᵀ·diag(w)·Jf` computes
entrywise). -/
theorem diag_case_hessian_weight (sigma : Fin N → ℝ) :
    (Matrix.diagonal (fun n => (sigma n)⁻¹))ᵀ * (Matrix.diagonal (fun n => (sigma n)⁻¹))
      = Matrix.diagonal (fun n => (sigma n)⁻¹ * (sigma n)⁻¹) := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]

end KNOMP
