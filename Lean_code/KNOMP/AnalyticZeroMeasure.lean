/-
KNOMP/AnalyticZeroMeasure.lean

PURPOSE: general-purpose, not KNOMP-specific, infrastructure for the
"Phase 2" full-N `Identifiability.lean` Step 2 argument (see that file's
own docstring, `HANDOFF.md` §5 item 1, and `SCRATCHPAD.md` for the full
history). Confirmed absent from this Mathlib snapshot by direct
reconnaissance (`Mathlib/Analysis/Analytic/` and `Mathlib/MeasureTheory/`
searched broadly, zero hits): a real-analytic identity theorem in
several variables — a nonzero real-analytic function on `ℝⁿ` has
Lebesgue-null zero set. This file builds it from scratch, by induction
on `n`.

STATUS: 0 `sorry`, 0 `axiom`.

PROOF STRATEGY — a genuine simplification versus the approach originally
planned (`/home/adlucem/.claude/plans/agile-snuggling-squid.md`), found
during this session's Mathlib reconnaissance and worth recording since it
avoids a flagged research risk entirely. The original plan's inductive
step proposed to view a jointly-analytic function's Taylor coefficients
in the last variable as themselves analytic in the remaining variables —
a fact whose exact Mathlib packaging was unconfirmed. The proof actually
used below needs no such fact. Given `F : ℝ × (Fin n → ℝ) → ℝ` jointly
analytic with witness `F (b, a) ≠ 0`:

  * `g (y) := F (b, y)` is analytic (fix the first coordinate), and
    `g a ≠ 0`, so by the induction hypothesis `Z0 := {y | g y = 0}` is
    null in `Fin n → ℝ`.
  * For `y ∉ Z0`: the slice `t ↦ F (t, y)` is analytic in one real
    variable and NOT identically zero (since `F (b, y) = g y ≠ 0`
    witnesses `t = b`), so by the one-variable case
    (`AnalyticOnNhd.countable_zero_set_of_ne` below, plus
    `Set.Countable.measure_zero`) its zero set in `t` is null.
  * Split `{p | F p = 0} ⊆ (Set.univ ×ˢ Z0) ∪ ({p | F p = 0} ∩
    (Set.univ ×ˢ Z0ᶜ))`. The first piece is null since `Z0` is null
    (`Measure.prod_prod`, unconditional on measurability, plus
    `mul_zero` in `ℝ≥0∞`). The second piece is null by the "slice by
    second coordinate" Fubini identity `Measure.prod_apply_symm`: every
    `y`-slice of it is either `{t | F (t,y) = 0}` (null, `y ∉ Z0`) or `∅`
    (`y ∈ Z0`, excluded by the `Z0ᶜ` factor) — so the outer integral over
    `y` is the integral of the zero function.

No Taylor-coefficient analyticity is needed anywhere in this argument;
only elementary composition/restriction of the already-analytic `F`
along affine slices, which `AnalyticOnNhd.comp₂` handles directly. The
transport between `Fin (n+1) → ℝ` and `ℝ × (Fin n → ℝ)` (needed to even
state the induction) uses Mathlib's `MeasurableEquiv.piFinSuccAbove`,
confirmed measure-preserving via `volume_preserving_piFinSuccAbove`
(`Mathlib/MeasureTheory/Constructions/Pi.lean`), with its inverse
identified with `Fin.snoc` via `Fin.insertNthEquiv_last`
(`Mathlib/Data/Fin/Tuple/Basic.lean`) — confirmed by direct source
reconnaissance, not assumed.

`isolated_set_countable` and `AnalyticOnNhd.countable_zero_set_of_ne`
below are relocated, verbatim, from `KNOMP/Identifiability.lean` (where
they were originally proved but, per grep, used by no other file in the
project) — the one-variable base case this file's induction needs.
`Identifiability.lean` now imports this file and no longer carries its
own copies (see that file's own header for the update). -/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases

set_option maxHeartbeats 1000000

namespace KNOMP

open MeasureTheory TopologicalSpace Set Filter

/-! ### One-variable base case (relocated from `Identifiability.lean`) -/

/-- **General fact, not KNOMP-specific (not previously in Mathlib):** an
isolated subset of a second-countable topological space is countable.
Proved via injection into the space's countable basis: each isolated
point `x ∈ Z` has an isolating open neighbourhood, which can be shrunk to
a basic open set `b_x` still isolating `x` from `Z`, and `x ↦ b_x` is
injective (since `b_x ∩ Z = {x}` pins down `x` from `b_x` alone). -/
theorem isolated_set_countable {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    (Z : Set α) (hiso : ∀ x ∈ Z, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ∩ Z = {x}) :
    Z.Countable := by
  have hchoice : ∀ x ∈ Z, ∃ b ∈ countableBasis α, x ∈ b ∧ b ∩ Z = {x} := by
    intro x hx
    obtain ⟨U, hU_open, hxU, hU_iso⟩ := hiso x hx
    obtain ⟨b, hb_mem, hxb, hbU⟩ :=
      (isBasis_countableBasis α).exists_subset_of_mem_open hxU hU_open
    refine ⟨b, hb_mem, hxb, ?_⟩
    apply le_antisymm
    · intro y hy
      have hyU : y ∈ U ∩ Z := ⟨hbU hy.1, hy.2⟩
      rw [hU_iso] at hyU
      exact hyU
    · intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hxb, hx⟩
  choose! g hg_mem hg_x hg_iso using hchoice
  apply Set.countable_of_injective_of_countable_image (f := g) (s := Z)
  · intro x hx y hy hxy
    have hx_eq : g x ∩ Z = {x} := hg_iso x hx
    have hy_eq : g y ∩ Z = {y} := hg_iso y hy
    rw [hxy, hy_eq] at hx_eq
    have hy_mem : y ∈ ({x} : Set α) := hx_eq ▸ (rfl : y ∈ ({y} : Set α))
    exact (Set.mem_singleton_iff.mp hy_mem).symm
  · apply Set.Countable.mono _ (countable_countableBasis α)
    rintro b ⟨x, hx, rfl⟩
    exact hg_mem x hx

/-- **Nonzero analytic function has countable zero set**, on a
preconnected open subset of a second-countable field (not previously in
Mathlib as a single lemma). Built from `isolated_set_countable` above
plus Mathlib's local/global isolated-zeros machinery
(`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`). -/
theorem AnalyticOnNhd.countable_zero_set_of_ne
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [SecondCountableTopology 𝕜]
    {f : 𝕜 → 𝕜} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (hne : ¬ EqOn f 0 U) :
    {x ∈ U | f x = 0}.Countable := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h | h
  · exact absurd h hne
  · apply isolated_set_countable
    intro x hx
    obtain ⟨hxU, hx0⟩ := hx
    rw [eventually_iff, mem_codiscreteWithin_accPt] at h
    have hacc := h x hxU
    rw [AccPt, not_neBot, Filter.inf_principal_eq_bot] at hacc
    rw [mem_nhdsWithin] at hacc
    obtain ⟨V, hV_open, hxV, hVsub⟩ := hacc
    refine ⟨V, hV_open, hxV, ?_⟩
    apply le_antisymm
    · intro y hy
      simp only [Set.mem_singleton_iff]
      by_contra hyx
      have hy_mem : y ∈ V ∩ ({x} : Set 𝕜)ᶜ := ⟨hy.1, hyx⟩
      have hynotin := hVsub hy_mem
      rw [Set.mem_compl_iff, Set.mem_diff] at hynotin
      exact hynotin ⟨hy.2.1, fun h => h hy.2.2⟩
    · intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hxV, hxU, hx0⟩

/-- A nonzero real-analytic function `ℝ → ℝ` has Lebesgue-null zero set:
the specialization of `countable_zero_set_of_ne` (with `U = Set.univ`,
preconnected) combined with `Set.Countable.measure_zero`
(`[NoAtoms (volume : Measure ℝ)]`, standard). -/
theorem AnalyticOnNhd.volume_zero_set_of_ne_real
    {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    volume {x : ℝ | f x = 0} = 0 := by
  have hnotzero : ¬ EqOn f 0 Set.univ := by
    rintro heq
    obtain ⟨x0, hx0⟩ := hne
    exact hx0 (heq (Set.mem_univ x0))
  have hcnt := AnalyticOnNhd.countable_zero_set_of_ne hf isPreconnected_univ hnotzero
  have hseteq : {x : ℝ | f x = 0} = {x ∈ (Set.univ : Set ℝ) | f x = 0} := by
    ext x; simp
  rw [hseteq]
  exact hcnt.measure_zero volume

/-! ### The `n`-variable theorem, by induction on `n` -/

/-- The transport map `ℝ × (Fin n → ℝ) → (Fin (n+1) → ℝ)`, `Fin.snoc`,
is analytic (it is linear: each component is either the first-coordinate
projection or a coordinate projection of the second factor). -/
private theorem snoc_analyticOnNhd (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × (Fin n → ℝ) => (Fin.snoc p.2 p.1 : Fin (n + 1) → ℝ))
      Set.univ := by
  set comp : ∀ i : Fin (n + 1), (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
    Fin.lastCases (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
      (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))
    with hcompdef
  have heq : (fun p : ℝ × (Fin n → ℝ) => (Fin.snoc p.2 p.1 : Fin (n + 1) → ℝ))
      = ⇑(ContinuousLinearMap.pi comp) := by
    funext p
    funext i
    rw [ContinuousLinearMap.pi_apply]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      simp only [hcompdef, Fin.lastCases_last]
      rfl
    · rw [Fin.snoc_castSucc]
      simp only [hcompdef, Fin.lastCases_castSucc]
      rfl
  rw [heq]
  exact (ContinuousLinearMap.pi comp).analyticOnNhd Set.univ

/-- The measurable equivalence `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)` used to
run the induction, together with the fact that its inverse coincides
with `Fin.snoc` and that it is measure-preserving. -/
private noncomputable def splitEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)

private theorem splitEquiv_symm_eq_snoc (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    (splitEquiv n).symm p = Fin.snoc p.2 p.1 := by
  show (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) p = Fin.snoc p.2 p.1
  rw [Fin.insertNthEquiv_last]
  rfl

private theorem splitEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (splitEquiv n) := volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n)

/-- **Main theorem.** A nonzero real-analytic function `(Fin n → ℝ) → ℝ`
has Lebesgue-null zero set, for every `n`. See the file header for the
proof strategy. -/
theorem AnalyticOnNhd.volume_zero_set_of_ne {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : AnalyticOnNhd ℝ f Set.univ) (hne : ∃ x, f x ≠ 0) :
    volume {x : Fin n → ℝ | f x = 0} = 0 := by
  induction n with
  | zero =>
      obtain ⟨x0, hx0⟩ := hne
      have hempty : {x : Fin 0 → ℝ | f x = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hfx
        exact hx0 (by rw [show x0 = x from funext (fun i => i.elim0)]; exact hfx)
      rw [hempty]; exact measure_empty
  | succ n ih =>
      set F : ℝ × (Fin n → ℝ) → ℝ := fun p => f ((splitEquiv n).symm p) with hFdef
      have hFanalytic : AnalyticOnNhd ℝ F Set.univ := by
        apply hf.comp (snoc_analyticOnNhd n) (Set.mapsTo_univ _ _) |>.congr isOpen_univ
        intro p _
        rw [hFdef]
        simp only [Function.comp_apply, splitEquiv_symm_eq_snoc]
      obtain ⟨x0, hx0⟩ := hne
      set p0 : ℝ × (Fin n → ℝ) := splitEquiv n x0 with hp0def
      have hFp0 : F p0 ≠ 0 := by
        rw [hFdef]
        simp only [hp0def, MeasurableEquiv.symm_apply_apply]
        exact hx0
      set b : ℝ := p0.1
      set a : Fin n → ℝ := p0.2
      have hganalytic : AnalyticOnNhd ℝ (fun y => F (b, y)) Set.univ :=
        AnalyticOnNhd.comp₂ hFanalytic analyticOnNhd_const analyticOnNhd_id
          (fun _ _ => Set.mem_univ _)
      have hga : F (b, a) ≠ 0 := by simpa using hFp0
      have hZ0null : volume {y : Fin n → ℝ | F (b, y) = 0} = 0 := ih _ hganalytic ⟨a, hga⟩
      set Z0 : Set (Fin n → ℝ) := {y | F (b, y) = 0} with hZ0def
      have hZ0closed : IsClosed Z0 := by
        rw [hZ0def]
        exact isClosed_eq hganalytic.continuous continuous_const
      have hZ0meas : MeasurableSet Z0 := hZ0closed.measurableSet
      have hFcont : Continuous F := hFanalytic.continuous
      have hFzeroclosed : IsClosed {p : ℝ × (Fin n → ℝ) | F p = 0} :=
        isClosed_eq hFcont continuous_const
      have hFzeromeas : MeasurableSet {p : ℝ × (Fin n → ℝ) | F p = 0} := hFzeroclosed.measurableSet
      have hsubset : {p : ℝ × (Fin n → ℝ) | F p = 0} ⊆
          (Set.univ ×ˢ Z0) ∪ ({p | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)) := by
        intro p hp
        by_cases hcase : p.2 ∈ Z0
        · exact Or.inl ⟨Set.mem_univ _, hcase⟩
        · exact Or.inr ⟨hp, Set.mem_univ _, hcase⟩
      have hfirstnull : volume ((Set.univ : Set ℝ) ×ˢ Z0) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        simp [hZ0null]
      have hsecondmeas : MeasurableSet ({p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)) :=
        hFzeromeas.inter (MeasurableSet.univ.prod hZ0meas.compl)
      have hsecondnull :
          volume ({p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_apply_symm hsecondmeas]
        have hslice : ∀ y : Fin n → ℝ,
            volume {t : ℝ | (t, y) ∈ {p | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)} = 0 := by
          intro y
          by_cases hyZ0 : y ∈ Z0
          · have : {t : ℝ | (t, y) ∈
                {p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)} = ∅ := by
              ext t
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
                Set.mem_compl_iff, true_and, Set.mem_empty_iff_false, iff_false]
              intro ⟨_, hnZ0⟩
              exact hnZ0 hyZ0
            rw [this]; exact measure_empty
          · have hslicefun : AnalyticOnNhd ℝ (fun t => F (t, y)) Set.univ :=
              AnalyticOnNhd.comp₂ hFanalytic analyticOnNhd_id analyticOnNhd_const
                (fun _ _ => Set.mem_univ _)
            have hslicene : ∃ t, F (t, y) ≠ 0 := by
              by_contra hcon
              push_neg at hcon
              exact hyZ0 (hcon b)
            have hslicenull := AnalyticOnNhd.volume_zero_set_of_ne_real hslicefun hslicene
            have hseteq : {t : ℝ | (t, y) ∈
                {p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)}
                = {t : ℝ | F (t, y) = 0} := by
              ext t
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
                Set.mem_compl_iff, true_and, and_iff_left_iff_imp]
              intro _
              exact hyZ0
            rw [hseteq]
            exact hslicenull
        calc ∫⁻ y, volume {t : ℝ | (t, y) ∈
              {p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)} ∂volume
            = ∫⁻ _ : Fin n → ℝ, 0 ∂volume := lintegral_congr hslice
          _ = 0 := lintegral_zero
      have hFzeronull : volume {p : ℝ × (Fin n → ℝ) | F p = 0} = 0 := by
        have hle : volume {p : ℝ × (Fin n → ℝ) | F p = 0} ≤ 0 := by
          calc volume {p : ℝ × (Fin n → ℝ) | F p = 0}
              ≤ volume ((Set.univ ×ˢ Z0) ∪ ({p | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ))) :=
                measure_mono hsubset
            _ ≤ volume ((Set.univ : Set ℝ) ×ˢ Z0)
                + volume ({p : ℝ × (Fin n → ℝ) | F p = 0} ∩ (Set.univ ×ˢ Z0ᶜ)) :=
                measure_union_le _ _
            _ = 0 := by rw [hfirstnull, hsecondnull]; simp
        exact (nonpos_iff_eq_zero.mp hle)  -- `a ≤ 0 ↔ a = 0` for `ℝ≥0∞`
      have hseteqfinal : {x : Fin (n + 1) → ℝ | f x = 0} =
          (splitEquiv n) ⁻¹' {p : ℝ × (Fin n → ℝ) | F p = 0} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hFdef]
        simp only [MeasurableEquiv.symm_apply_apply]
      rw [hseteqfinal]
      exact (splitEquiv_measurePreserving n).measure_preimage_equiv _ |>.trans hFzeronull

end KNOMP
