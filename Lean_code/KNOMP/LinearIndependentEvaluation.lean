/-
KNOMP/LinearIndependentEvaluation.lean

PURPOSE: general-purpose, not KNOMP-specific, infrastructure for the
"Phase 2" full-N `Identifiability.lean` Step 2 argument (Deliverable 2 of
`/home/adlucem/.claude/plans/agile-snuggling-squid.md`). If `φ_1,...,φ_m
: S → ℝ` are linearly independent functions on any set `S`, there exist
points `s_1,...,s_m ∈ S` such that the `m×m` evaluation matrix
`[φ_i(s_j)]` is nonsingular.

STATUS: 0 `sorry`, 0 `axiom`.

PROOF STRATEGY. Let `ev : S → (Fin m → ℝ)`, `ev s := fun i => φ i s`.

  * `span ℝ (range ev) = ⊤`: else, by `Submodule.exists_le_ker_of_lt_top`,
    some nonzero functional `f` on `Fin m → ℝ` vanishes on all of
    `range ev`. Representing `f` in the standard basis `Pi.basisFun` as
    `f x = ∑ i, x i * c i` (some `c ≠ 0`), `f (ev s) = 0` for every `s`
    unwinds to `∑ i, c i • φ i = 0` as a function on `S` — contradicting
    `LinearIndependent ℝ φ` via `Fintype.linearIndependent_iff`.
  * Given that, build `t : Fin k → S` with `ev ∘ t` linearly independent
    by induction on `k` up to `m`: at each step the span of the current
    `k < m` images is a proper subspace (`finrank_span_eq_card` gives it
    dimension exactly `k < m = finrank (Fin m → ℝ)`), so since `range ev`
    spans everything, some `x : S` has `ev x` outside that proper
    subspace; extend via `Fin.snoc` and `linearIndependent_fin_snoc`.
  * At `k = m`, `ev ∘ s` is a linearly independent `Fin m`-indexed family
    in the `m`-dimensional space `Fin m → ℝ`, i.e. (via
    `Matrix.linearIndependent_cols_iff_isUnit`, matching column `j` of
    `Matrix.of (fun i j => φ i (s j))` with `ev (s j)`) the matrix is a
    unit, i.e. (`Matrix.isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero` on
    the field `ℝ`) has nonzero determinant.

No KNOMP-specific content anywhere in this file — fully general linear
algebra, reusable independently of the Kepler/photometric-atom context
that motivated it. -/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace KNOMP

open Submodule Module
open scoped Matrix

/-- **General fact, not KNOMP-specific:** if `φ_1,...,φ_m : S → ℝ` are
linearly independent functions on any set `S`, there exist points
`s_1,...,s_m ∈ S` such that the `m×m` evaluation matrix `[φ_i(s_j)]` is
nonsingular. See the file header for the proof strategy. -/
theorem exists_nonsingular_evaluation_matrix {S : Type*} {m : ℕ}
    (φ : Fin m → S → ℝ) (hli : LinearIndependent ℝ φ) :
    ∃ s : Fin m → S, (Matrix.of (fun i j => φ i (s j))).det ≠ 0 := by
  classical
  set ev : S → (Fin m → ℝ) := fun s i => φ i s with hev_def
  have hspan : span ℝ (Set.range ev) = ⊤ := by
    by_contra hne
    obtain ⟨f, hfne, hfker⟩ :=
      Submodule.exists_le_ker_of_lt_top (span ℝ (Set.range ev)) (lt_top_iff_ne_top.mpr hne)
    set c : Fin m → ℝ := fun i => f (Pi.basisFun ℝ (Fin m) i) with hc_def
    have hrepr : ∀ x : Fin m → ℝ, f x = ∑ i, x i * c i := by
      intro x
      conv_lhs => rw [← (Pi.basisFun ℝ (Fin m)).sum_repr x]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, Pi.basisFun_repr, hc_def]
    have hfev : ∀ s : S, ∑ i, ev s i * c i = 0 := by
      intro s
      rw [← hrepr]
      exact hfker (Submodule.subset_span ⟨s, rfl⟩)
    have hcombo : ∑ i, c i • φ i = 0 := by
      funext s
      have h := hfev s
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hev_def, Pi.zero_apply]
      rw [← h]
      exact Finset.sum_congr rfl (fun i _ => mul_comm (c i) (φ i s))
    have hc0 : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hli c hcombo
    apply hfne
    apply LinearMap.ext
    intro x
    rw [hrepr x]
    simp [hc0]
  have hstep : ∀ k : ℕ, k ≤ m → ∃ t : Fin k → S, LinearIndependent ℝ (fun i => ev (t i)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type⟩
    | succ k ih =>
        intro hk
        obtain ⟨t, ht⟩ := ih (Nat.le_of_succ_le hk)
        have hWne : span ℝ (Set.range (fun i => ev (t i))) ≠ ⊤ := by
          intro hW
          have hcard := finrank_span_eq_card ht
          rw [hW, finrank_top, Module.finrank_fin_fun] at hcard
          simp only [Fintype.card_fin] at hcard
          omega
        have hex : ∃ x : S, ev x ∉ span ℝ (Set.range (fun i => ev (t i))) := by
          by_contra hcon
          push_neg at hcon
          apply hWne
          apply le_antisymm le_top
          rw [← hspan]
          apply span_le.mpr
          rintro y ⟨s, rfl⟩
          exact hcon s
        obtain ⟨x, hx⟩ := hex
        refine ⟨Fin.snoc t x, ?_⟩
        have heq : (fun i => ev ((Fin.snoc t x : Fin (k + 1) → S) i))
            = Fin.snoc (fun i => ev (t i)) (ev x) := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp
        rw [heq]
        exact linearIndependent_fin_snoc.mpr ⟨ht, hx⟩
  obtain ⟨s, hs⟩ := hstep m le_rfl
  refine ⟨s, ?_⟩
  have hcols : LinearIndependent ℝ (fun i => (Matrix.of (fun i j => φ i (s j)))ᵀ i) := by
    have heq : (fun i => (Matrix.of (fun i j => φ i (s j)))ᵀ i) = fun i => ev (s i) := by
      funext i
      funext j
      simp [Matrix.transpose_apply, hev_def]
    rw [heq]
    exact hs
  have hunit : IsUnit (Matrix.of (fun i j => φ i (s j))) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  exact isUnit_iff_ne_zero.mp hunit

end KNOMP
