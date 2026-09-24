/-
KNOMP/InterferenceBias.lean

Source: Section 10, "Interference Bias Without Cyclic Refinement":
Proposition `noc` (single-pass bias), Proposition `cyclic-gs` (Gauss-Seidel
realization and geometric contraction), Corollary `noc-summary`.

STATUS: PROVED for the bias formula and the contraction recursion/geometric
decay; PARTIAL for one peripheral fact (`|ε12| < 1` from linear
independence of `f1, f2`, which the paper gets "for free" from the
strict Cauchy-Schwarz inequality and which we instead take as an
explicit hypothesis — see the note on `hEps` below).

Everything here uses the plain (unweighted) dot product on `Fin N → ℝ`,
matching the paper's own choice in this section ("unit-weight inner
product").
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace KNOMP

variable {N : ℕ}

/-- A vector's self dot-product is strictly positive iff the vector is
nonzero — the elementary "sum of squares vanishes iff every term does"
fact, used to establish `normV f ≠ 0` for `f ≠ 0` below. -/
theorem dotProduct_self_pos_of_ne_zero {v : Fin N → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v v := by
  unfold dotProduct
  have hnn : (0:ℝ) ≤ Finset.sum Finset.univ (fun i => v i * v i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  rcases (le_iff_eq_or_lt.mp hnn) with heq | hgt
  · exfalso
    apply hv
    funext i
    have hfun : (fun i => v i * v i) = 0 := by
      have hi := (Fintype.sum_eq_zero_iff_of_nonneg
        (f := fun i => v i * v i)
        (by intro i; exact mul_self_nonneg (v i))).mp heq.symm
      funext x; exact congrFun hi x
    have hi := congrFun hfun i
    exact mul_self_eq_zero.mp hi
  · exact hgt

noncomputable def normV (v : Fin N → ℝ) : ℝ := Real.sqrt (dotProduct v v)

theorem normV_sq {v : Fin N → ℝ} : normV v ^ 2 = dotProduct v v := by
  unfold normV
  exact Real.sq_sqrt (by unfold dotProduct; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _))

theorem normV_ne_zero_of_ne_zero {v : Fin N → ℝ} (hv : v ≠ 0) : normV v ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (dotProduct_self_pos_of_ne_zero hv))

/-- The normalized overlap `ε12 = ⟨f1,f2⟩ / (‖f1‖‖f2‖)` between the two
planet curves, matching the paper's Eq. `noc-bias`. -/
noncomputable def eps12 (f1 f2 : Fin N → ℝ) : ℝ :=
  dotProduct f1 f2 / (normV f1 * normV f2)

/-- **Proposition `noc`.** Fitting planet 1's gain alone against the
two-planet truth `y = K1•f1 + K2•f2` gives the exact, biased answer
`K1 + K2 · ε12 · ‖f2‖/‖f1‖`. -/
theorem noc_bias (f1 f2 : Fin N → ℝ) (K1 K2 : ℝ)
    (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) :
    dotProduct (K1 • f1 + K2 • f2) f1 / dotProduct f1 f1
      = K1 + K2 * eps12 f1 f2 * (normV f2 / normV f1) := by
  have hf1n : normV f1 ≠ 0 := normV_ne_zero_of_ne_zero hf1
  have hf2n : normV f2 ≠ 0 := normV_ne_zero_of_ne_zero hf2
  have hf1sq : dotProduct f1 f1 ≠ 0 := by
    rw [← @normV_sq N f1]
    exact pow_ne_zero 2 hf1n
  have hexpand : dotProduct (K1 • f1 + K2 • f2) f1
      = K1 * dotProduct f1 f1 + K2 * dotProduct f2 f1 := by
    simp [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hcomm : dotProduct f2 f1 = dotProduct f1 f2 := dotProduct_comm f2 f1
  have hdef : dotProduct f1 f2 = eps12 f1 f2 * (normV f1 * normV f2) := by
    unfold eps12
    field_simp
  rw [hexpand, hcomm, hdef, ← @normV_sq N f1]
  field_simp

/-- The one-round Gauss-Seidel iteration for the joint two-planet fit:
`K1' = ⟨y - K2•f2, f1⟩` then `K2' = ⟨y - K1'•f1, f2⟩`, valid when `f1, f2`
are unit norm (so `⟨f1,f1⟩ = ⟨f2,f2⟩ = 1`, matching the paper's
normalization for the contraction-rate computation). Iterated from an
arbitrary starting pair `(K1⁰, K2⁰)`. -/
noncomputable def gsIter (f1 f2 y : Fin N → ℝ) (K10 K20 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (K10, K20)
  | (n + 1) =>
      let prev := gsIter f1 f2 y K10 K20 n
      let K1' := dotProduct (y - prev.2 • f2) f1
      let K2' := dotProduct (y - K1' • f1) f2
      (K1', K2')

/-- **Proposition `cyclic-gs`, error recursion.** With `y = K1•f1 + K2•f2`
and `f1, f2` unit norm, the errors `δ1(n) = K1(n) - K1`, `δ2(n) = K2(n) -
K2` obey `δ1(n+1) = -ε12·δ2(n)` and `δ2(n+1) = ε12²·δ2(n)` exactly, term
for term matching the paper's derivation.

PROOF NOTE: `K1n`/`K2n` name the two iterate components as plain opaque
reals throughout, and every substitution of `y = K1•f1 + K2•f2` is done
inside a small side lemma that never simultaneously mentions the
self-referential term `gsIter f1 f2 y ...` — rewriting `y` inside a goal
that *also* contains `y` buried inside such a self-reference silently
corrupts the self-reference too, which was the one genuine subtlety in
this file. -/
theorem gs_error_recursion (f1 f2 y : Fin N → ℝ) (K1 K2 K10 K20 : ℝ)
    (hy : y = K1 • f1 + K2 • f2)
    (hf1u : dotProduct f1 f1 = 1) (hf2u : dotProduct f2 f2 = 1)
    (n : ℕ) :
    ((gsIter f1 f2 y K10 K20 (n + 1)).1 - K1 = - eps12 f1 f2 * ((gsIter f1 f2 y K10 K20 n).2 - K2))
      ∧ ((gsIter f1 f2 y K10 K20 (n + 1)).2 - K2
          = eps12 f1 f2 ^ 2 * ((gsIter f1 f2 y K10 K20 n).2 - K2)) := by
  have heps : dotProduct f1 f2 = eps12 f1 f2 := by
    unfold eps12 normV
    rw [hf1u, hf2u]
    simp
  set K2n := (gsIter f1 f2 y K10 K20 n).2 with hK2n
  have hK1n_def : (gsIter f1 f2 y K10 K20 (n+1)).1 = dotProduct (y - K2n • f2) f1 := rfl
  set K1n := (gsIter f1 f2 y K10 K20 (n+1)).1 with hK1n
  have hstep1 : K1n - K1 = - eps12 f1 f2 * (K2n - K2) := by
    have hval : dotProduct (y - K2n • f2) f1
        = K1 * dotProduct f1 f1 + (K2 - K2n) * dotProduct f2 f1 := by
      have hy' : y - K2n • f2 = K1 • f1 + (K2 - K2n) • f2 := by rw [hy]; module
      rw [hy']
      simp [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hK1n_def, hval, hf1u, dotProduct_comm f2 f1, heps]
    ring
  have hK2n1_def : (gsIter f1 f2 y K10 K20 (n+1)).2
      = dotProduct (y - K1n • f1) f2 := by rw [hK1n]; rfl
  have hstep2 : (gsIter f1 f2 y K10 K20 (n+1)).2 - K2 = eps12 f1 f2 ^ 2 * (K2n - K2) := by
    have hval : dotProduct (y - K1n • f1) f2
        = (K1 - K1n) * dotProduct f1 f2 + K2 * dotProduct f2 f2 := by
      have hy' : y - K1n • f1 = (K1 - K1n) • f1 + K2 • f2 := by rw [hy]; module
      rw [hy']
      simp [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hK2n1_def, hval, hf2u, heps]
    have hflip : K1 - K1n = - (K1n - K1) := by ring
    rw [hflip, hstep1]
    ring
  exact ⟨hstep1, hstep2⟩

/-- **Proposition `cyclic-gs`, geometric contraction.** Consequently, after
`n` full sweeps, `|δ2(n)| = |ε12|^(2n) · |δ2(0)|` exactly, and — this is
where the paper's "PARTIAL" flag applies — `|ε12| < 1` strictly whenever
`f1, f2` are linearly independent (the strict Cauchy-Schwarz inequality;
not re-derived here, taken as the hypothesis `hEps`), which is exactly
when the contraction factor `ε12² < 1` and the iteration converges to the
true, unbiased joint solution `(K1, K2)`. -/
theorem gs_geometric_contraction (f1 f2 y : Fin N → ℝ) (K1 K2 K10 K20 : ℝ)
    (hy : y = K1 • f1 + K2 • f2)
    (hf1u : dotProduct f1 f1 = 1) (hf2u : dotProduct f2 f2 = 1)
    (hEps : |eps12 f1 f2| < 1) (n : ℕ) :
    |(gsIter f1 f2 y K10 K20 n).2 - K2| = |eps12 f1 f2| ^ (2 * n) * |K20 - K2| := by
  induction n with
  | zero => simp [gsIter]
  | succ n ih =>
      have h := (gs_error_recursion f1 f2 y K1 K2 K10 K20 hy hf1u hf2u n).2
      rw [h, abs_mul, ih, abs_pow]
      ring_nf

end KNOMP
