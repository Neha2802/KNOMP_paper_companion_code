/-
KNOMP/MonotonicityAugmentation.lean

Source: Section 16, "Monotonicity Under Candidate-Set Augmentation",
Theorem "Augmenting the candidate set cannot lower the achieved maximum".

STATUS: PROVED.

The candidate set is modeled as a `Finset α` (matching the paper's own
use case: a finite search grid), and "the best score achieved" as
`Finset.sup'` (max over a nonempty finite set). The proof is the
one-paragraph containment argument the paper itself gives, verbatim.
-/
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

namespace KNOMP

variable {α : Type*}

/-- **Theorem (candidate-set monotonicity).** If `C ⊆ C'`, the best value
of `g` over `C'` is at least the best value of `g` over `C`. -/
theorem sup'_mono_of_subset (C C' : Finset α) (hsub : C ⊆ C') (hC : C.Nonempty)
    (g : α → ℝ) :
    C.sup' hC g ≤ C'.sup' (⟨hC.choose, hsub hC.choose_spec⟩ : C'.Nonempty) g := by
  apply Finset.sup'_le
  intro c hc
  exact Finset.le_sup' g (hsub hc)

end KNOMP
