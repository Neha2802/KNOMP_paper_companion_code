/-
KNOMP/Identifiability.lean

Source: Section 2, "Identifiability of the Linear Model", Theorem
`identifiability`.

STATUS: 0 `sorry`, 0 `axiom`.

HISTORY (condensed — full narrative in `SCRATCHPAD.md`/`HANDOFF.md`).
An earlier version of this file formalized the paper's Step 2 literally:
"a linear combination of trend + offset + `k` Keplerian atoms vanishing
at just THREE fixed times forces all coefficients to zero, for generic
times/parameters." That statement is false for `k ≥ 1`: evaluating the
`(k+3)`-dimensional coefficient vector at only 3 points is a linear map
`ℝ^(k+3) → ℝ³`, which by rank-nullity has a nontrivial kernel at *every*
choice of 3 points once `k ≥ 1` — no genericity condition on the times
can rescue it. (It's exactly right for `k = 0`, where 3 points in 3
unknowns is an ordinary Vandermonde system.)

That finding drove a "Phase 2" reapproach
(`/home/adlucem/.claude/plans/agile-snuggling-squid.md`): restate the
goal directly as the design matrix's full column rank from `k+3` points
(not 3), rather than routing through "3 points force `g≡0`" at all —
`design_matrix_generically_full_rank` below, built on two new
general-purpose files: `KNOMP/AnalyticZeroMeasure.lean` (nonzero
real-analytic function on `ℝⁿ` has Lebesgue-null zero set) and
`KNOMP/LinearIndependentEvaluation.lean` (linearly independent functions
admit a nonsingular evaluation matrix). That theorem has **zero internal
`sorry`s of its own**: the one real gap — linear independence of
`{1,t,t²,f_1,...,f_k}` as functions on `ℝ` for pairwise-distinct-period
atoms — is taken as an **explicit hypothesis** (`hli`), per CLAUDE.md
house rule 4, rather than a `sorry`. The main `identifiability` theorem
was then rewired to actually consume this: it takes `k+3` witness points
`n : Fin (k+3) → Fin N` from one dataset and an explicit
`hnonsingular : (evaluation matrix at those points).det ≠ 0` hypothesis
instead of the old 3-witness / vacuous-`True` formulation. The proof
combines `hnonsingular` with `Matrix.eq_zero_of_vecMul_eq_zero` (the same
lemma Mathlib's own `Vandermonde.lean` nonsingularity argument uses) to
force the coefficient vector to zero directly, then reuses Step 3
(`restricted_isolates_bd`) to conclude `b_d = 0` for every dataset.
`identifiability` has 0 internal `sorry`; its only remaining obligation
is supplying `hnonsingular`, which for `k = 0` is now fully discharged
(`basisFunctions_linearIndependent_of_k_eq_zero` — Vandermonde-style, no
genericity needed) and for `k ≥ 1` requires the still-open general `hli`
case (see "Open work" in `CLAUDE.md` — Vandermonde for the polynomial
block plus extending `FourierStructure.lean`'s single-atom argument to a
full pairwise-distinct-period system; real, well-scoped follow-on work,
not yet attempted).

The original, now-superseded "3 points, any `k`" theorem
(`analytic_identity_forces_trend_and_atom_coeffs_zero`) and its `sorry`
were deleted outright once the rewiring above was confirmed to have
replaced it with no remaining callers — kept only in `SCRATCHPAD.md`'s
history, not as dead code here, since it no longer represented open work
(the correct statement is now proved, modulo the honestly-flagged `hli`
hypothesis).

Two general-purpose theorems relocated here to `AnalyticZeroMeasure.lean`
in the Phase 2 session — `isolated_set_countable` and
`AnalyticOnNhd.countable_zero_set_of_ne` — are the one-variable base case
of that file's `n`-variable induction, and match, almost word for word,
the paper's own bracketed remark ("the corresponding `g` has a discrete,
at most countable zero set").

The paper's proof has three steps: (1) restricting the linear-dependence
equation to one dataset's support isolates that dataset's own offset
coefficient `b_d` — pure linear algebra, proved below as
`restricted_isolates_bd`; (2) the design matrix's full column rank,
established via the real-analytic identity theorem above
(`design_matrix_generically_full_rank`, gated on `hli`); and (3)
repeating (1)-(2) once per dataset — proved with *less* than the paper's
own per-dataset hypothesis: once `a1, a2, c_j` are known zero from one
dataset's `k+3` witnesses, every other dataset's `b_{d'} = 0` already
follows from Step 1 alone at a single point (`witness`), no second
application of the analytic Step 2 needed elsewhere.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import KNOMP.AnalyticZeroMeasure
import KNOMP.LinearIndependentEvaluation

namespace KNOMP

open TopologicalSpace Set Filter MeasureTheory
open scoped Matrix

variable {N D k : ℕ}

/-- **Step 1.** If the design matrix's columns satisfy a linear
dependence overall, restricting that dependence to one dataset `d`'s
support isolates `b_d` as an explicit function of the other
coefficients and that dataset's own data — the paper's own first
reduction, exactly. -/
theorem restricted_isolates_bd
    (dsetOf : Fin N → Fin D) (t : Fin N → ℝ) (f : Fin k → ℝ → ℝ)
    (a1 a2 : ℝ) (b : Fin D → ℝ) (c : Fin k → ℝ)
    (hlincomb : ∀ n : Fin N,
      a1 * t n + a2 * (t n) ^ 2 + b (dsetOf n) + ∑ j, c j * f j (t n) = 0)
    (d : Fin D) (n : Fin N) (hn : dsetOf n = d) :
    b d = -(a1 * t n + a2 * (t n) ^ 2 + ∑ j, c j * f j (t n)) := by
  have h := hlincomb n
  rw [hn] at h
  linarith

/-! ### Phase 2: the design matrix's full column rank, stated directly

See the file header ("UPDATE (Phase 2 session...)") for why this
supersedes the "3 points force `g≡0`" route above rather than repairing
it, and for what the one remaining hypothesis (`hli`) covers. -/

/-- The design matrix's `k+3` basis functions: the `k` atoms `f`, then
`1, t, t²` (matching `Fin.append`'s natural `Fin (m+n)` ordering with
`m = k`). -/
noncomputable def basisFunctions (f : Fin k → ℝ → ℝ) : Fin (k + 3) → ℝ → ℝ :=
  Fin.append f ![(fun _ : ℝ => (1 : ℝ)), (fun s => s), (fun s => s ^ 2)]

/-- Each of the `k+3` basis functions is real-analytic on all of `ℝ`:
the atoms by hypothesis (e.g. `Kepler.lean`'s `keplerAtom_analytic`), the
trend triple `1, t, t²` trivially. -/
theorem basisFunctions_analytic (f : Fin k → ℝ → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) Set.univ) :
    ∀ i, AnalyticOnNhd ℝ (basisFunctions f i) Set.univ := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · simpa [basisFunctions, Fin.append_left] using hf l
  · simp only [basisFunctions, Fin.append_right]
    fin_cases r
    · simpa using analyticOnNhd_const
    · simpa using analyticOnNhd_id
    · show AnalyticOnNhd ℝ (fun s => s ^ 2) Set.univ
      exact (analyticOnNhd_id (𝕜 := ℝ)).pow 2

/-- The design matrix's determinant, as a function of the evaluation
points `t : Fin (k+3) → ℝ` (fixed atoms `f`), is real-analytic on all of
`ℝ^(k+3)`: via `Matrix.det_apply'`, it is a finite sum over permutations
of constants times finite products of the (analytic, by
`basisFunctions_analytic`) entries composed with coordinate projections
(analytic, `ContinuousLinearMap.proj`), combined by
`Finset.analyticOnNhd_sum`/`Finset.analyticOnNhd_prod`. -/
theorem det_basisFunctions_analytic (f : Fin k → ℝ → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) Set.univ) :
    AnalyticOnNhd ℝ
      (fun t : Fin (k + 3) → ℝ => (Matrix.of (fun i j => basisFunctions f i (t j))).det)
      Set.univ := by
  have hentry : ∀ i j : Fin (k + 3),
      AnalyticOnNhd ℝ (fun t : Fin (k + 3) → ℝ => basisFunctions f i (t j)) Set.univ := by
    intro i j
    have hproj : AnalyticOnNhd ℝ (fun t : Fin (k + 3) → ℝ => t j) Set.univ :=
      (ContinuousLinearMap.proj j : (Fin (k + 3) → ℝ) →L[ℝ] ℝ).analyticOnNhd Set.univ
    exact (basisFunctions_analytic f hf i).comp hproj (Set.mapsTo_univ _ _)
  have heq : (fun t : Fin (k + 3) → ℝ => (Matrix.of (fun i j => basisFunctions f i (t j))).det)
      = ∑ σ : Equiv.Perm (Fin (k + 3)), fun t => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, basisFunctions f (σ i) (t i) := by
    funext t
    rw [Matrix.det_apply']
    simp only [Matrix.of_apply, Finset.sum_apply]
  rw [heq]
  apply Finset.analyticOnNhd_sum
  intro σ _
  apply AnalyticOnNhd.mul analyticOnNhd_const
  have hprod_eq : (fun t : Fin (k + 3) → ℝ => ∏ i, basisFunctions f (σ i) (t i))
      = ∏ i : Fin (k + 3), fun t : Fin (k + 3) → ℝ => basisFunctions f (σ i) (t i) := by
    funext t
    simp only [Finset.prod_apply]
  rw [hprod_eq]
  exact Finset.analyticOnNhd_prod _ (fun i _ => hentry (σ i) i)

/-- **Design matrix generically has full column rank** — the literal
"design matrix has full column rank" statement the paper's Step 2 is
actually for, stated directly rather than routed through the flawed "3
points force `g≡0`" step above. For fixed, analytic atoms `f_1,...,f_k`
such that `{1,t,t²,f_1,...,f_k}` are linearly independent as functions on
`ℝ` (`hli` — see the file header for exactly what this hypothesis covers
and why it is left as an explicit hypothesis rather than a `sorry`, per
CLAUDE.md house rule 4), outside a Lebesgue-null set of evaluation-point
tuples `t : Fin (k+3) → ℝ`, the `(k+3)×(k+3)` design matrix
`[basisFunctions f i (t j)]` is nonsingular.

STATUS: 0 `sorry` in this theorem's own proof (the one gap is the
explicit hypothesis `hli`, not a `sorry`). Built from
`exists_nonsingular_evaluation_matrix` (`LinearIndependentEvaluation.lean`,
giving a nonvanishing witness) and `AnalyticOnNhd.volume_zero_set_of_ne`
(`AnalyticZeroMeasure.lean`, giving the null-zero-set conclusion from
analyticity + a nonvanishing witness), combined with
`det_basisFunctions_analytic` above. -/
theorem design_matrix_generically_full_rank
    (f : Fin k → ℝ → ℝ) (hf : ∀ j, AnalyticOnNhd ℝ (f j) Set.univ)
    (hli : LinearIndependent ℝ (basisFunctions f)) :
    volume {t : Fin (k + 3) → ℝ |
      (Matrix.of (fun i j => basisFunctions f i (t j))).det = 0} = 0 := by
  obtain ⟨s, hs⟩ := exists_nonsingular_evaluation_matrix (basisFunctions f) hli
  exact AnalyticOnNhd.volume_zero_set_of_ne _ (det_basisFunctions_analytic f hf) ⟨s, hs⟩

/-- **Bounded special case of the deferred `hli` hypothesis, `k = 0`.**
With no Keplerian atoms at all, `basisFunctions f` is just the trend
triple `{1, t, t²}`, and these are linearly independent as functions on
`ℝ` — a Vandermonde-type fact, provable directly by evaluating a
vanishing linear combination at `t = 0, 1, -1` and solving the resulting
`3×3` linear system, with no genericity or measure-zero exception needed
at all (matching this file's header docstring's own observation about
the `k = 0` case). This resolves `hli` completely for `k = 0`; the
general `k ≥ 1` case (linear independence against pairwise-distinct-period
Keplerian atoms, needing Fourier/almost-periodic uniqueness machinery not
present anywhere in this project) remains deferred, real follow-on
work — deliberately NOT attempted here, since the plan governing this
work (`agile-snuggling-squid.md`) explicitly flags it as out of scope,
comparable in scale to the project's already-documented CLT gap
(`AsymptoticEfficiency.lean`). -/
theorem basisFunctions_linearIndependent_of_k_eq_zero
    (f : Fin 0 → ℝ → ℝ) : LinearIndependent ℝ (basisFunctions f) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hf0 : basisFunctions f (0 : Fin (0 + 3)) = fun _ : ℝ => (1 : ℝ) := rfl
  have hf1 : basisFunctions f (1 : Fin (0 + 3)) = fun s : ℝ => s := rfl
  have hf2 : basisFunctions f (2 : Fin (0 + 3)) = fun s : ℝ => s ^ 2 := rfl
  have hexpand : ∀ t : ℝ, g 0 * 1 + g 1 * t + g 2 * t ^ 2 = 0 := by
    intro t
    have h := congrFun hg t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [Fin.sum_univ_three] at h
    simpa only [hf0, hf1, hf2] using h
  have e0 := hexpand 0
  have e1 := hexpand 1
  have em1 := hexpand (-1)
  norm_num at e0 e1 em1
  have hg0 : g 0 = 0 := e0
  have hg2 : g 2 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  intro i
  fin_cases i <;> simp_all

/-- **Steps 1-3 combined, main theorem — rewired (Phase 2, follow-on
session).** Superseded formulation of `identifiability`: instead of "3
points force `g≡0`" (the flawed, `k`-independent claim flagged at the top
of this file), this version asks for `k+3` witnesses `n : Fin (k+3) →
Fin N` within one bootstrap dataset `d0`, all sharing that dataset, such
that the resulting `(k+3)×(k+3)` design matrix `[basisFunctions f i
(t (n j))]` is nonsingular at those *actual chosen* observation times
(`hnonsingular`) — an honest, meaningful explicit hypothesis in the sense
of CLAUDE.md house rule 4, replacing the old vacuous `hdistinct_periods :
True` / `hgeneric : True` placeholders. This sidesteps the deferred `hli`
linear-independence fact entirely (see `design_matrix_generically_full_rank`
above, which remains available separately as the "generically nonsingular"
statement built from `hli`): `hnonsingular` is a hypothesis about the data
actually in hand, not a genericity claim requiring `hli` to be proved
first.

PROOF: the linear-dependence equation restricted to dataset `d0`, at each
of the `k+3` witnesses, is exactly the statement that the coefficient
vector `w := Fin.append c ![b d0, a1, a2]` (matching `basisFunctions`'s
own atoms-then-trend index ordering) satisfies `w ᵥ* M = 0` for `M` the
design matrix above; `Matrix.eq_zero_of_vecMul_eq_zero` (the same
nondegenerate-bilinear-form fact `Mathlib.LinearAlgebra.Vandermonde` uses
for its own Vandermonde nonsingularity argument) then forces `w = 0`
outright from `hnonsingular`, i.e. every `c j = 0`, `a1 = 0`, `a2 = 0`.
Step 3 (`witness`, unchanged from before) then gives `∀ d', b d' = 0`
exactly as previously. -/
theorem identifiability
    (dsetOf : Fin N → Fin D) (t : Fin N → ℝ) (f : Fin k → ℝ → ℝ)
    (a1 a2 : ℝ) (b : Fin D → ℝ) (c : Fin k → ℝ)
    (hlincomb : ∀ n : Fin N,
      a1 * t n + a2 * (t n) ^ 2 + b (dsetOf n) + ∑ j, c j * f j (t n) = 0)
    (d0 : Fin D) (n : Fin (k + 3) → Fin N) (hn : ∀ i, dsetOf (n i) = d0)
    (hnonsingular :
      (Matrix.of (fun i j => basisFunctions f i (t (n j)))).det ≠ 0)
    (witness : ∀ d' : Fin D, ∃ n' : Fin N, dsetOf n' = d') :
    a1 = 0 ∧ a2 = 0 ∧ (∀ j, c j = 0) ∧ ∀ d', b d' = 0 := by
  classical
  have hveq :
      (Fin.append c ![b d0, a1, a2]) ᵥ*
        (Matrix.of (fun i j => basisFunctions f i (t (n j)))) = 0 := by
    funext j
    show ∑ i, (Fin.append c ![b d0, a1, a2]) i * basisFunctions f i (t (n j)) = 0
    rw [Fin.sum_univ_add]
    have hatoms :
        ∑ i : Fin k, (Fin.append c ![b d0, a1, a2]) (Fin.castAdd 3 i) *
          basisFunctions f (Fin.castAdd 3 i) (t (n j))
        = ∑ i : Fin k, c i * f i (t (n j)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [basisFunctions]
    have htrend :
        ∑ i : Fin 3, (Fin.append c ![b d0, a1, a2]) (Fin.natAdd k i) *
          basisFunctions f (Fin.natAdd k i) (t (n j))
        = b d0 + a1 * t (n j) + a2 * (t (n j)) ^ 2 := by
      simp [Fin.sum_univ_three, basisFunctions]
    rw [hatoms, htrend]
    have hz := hlincomb (n j)
    rw [hn j] at hz
    linarith
  have hw0 : Fin.append c ![b d0, a1, a2] = 0 :=
    Matrix.eq_zero_of_vecMul_eq_zero hnonsingular hveq
  have hc : ∀ j, c j = 0 := by
    intro j
    have hcj := congrFun hw0 (Fin.castAdd 3 j)
    simpa using hcj
  have ha1 : a1 = 0 := by
    have ha := congrFun hw0 (Fin.natAdd k (1 : Fin 3))
    simpa using ha
  have ha2 : a2 = 0 := by
    have ha := congrFun hw0 (Fin.natAdd k (2 : Fin 3))
    simpa using ha
  refine ⟨ha1, ha2, hc, fun d' => ?_⟩
  -- Step 3: with `a1 = a2 = 0` and every `c j = 0` already established,
  -- Step 1 at *any* single point `n'` in dataset `d'` immediately gives
  -- `b d' = 0` directly — no second `k+3`-witness structure needed.
  obtain ⟨n', hn'⟩ := witness d'
  have hz' := restricted_isolates_bd dsetOf t f a1 a2 b c hlincomb d' n' hn'
  simp only [ha1, ha2, hc, zero_mul, mul_zero, zero_add, zero_pow, add_zero] at hz'
  simpa using hz'

end KNOMP
