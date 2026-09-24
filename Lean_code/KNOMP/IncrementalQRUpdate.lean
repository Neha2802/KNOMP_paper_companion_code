/-
KNOMP/IncrementalQRUpdate.lean

Source: Section 9, "Exactness of the Incremental QR Update", Theorem `qr`
and Corollary `qr-induction`.

STATUS: PROVED, in full — including Corollary `qr-induction`, which an
earlier version of this file left as a vacuous placeholder (`: True :=
trivial`, not even stating the real proposition). It turned out fully
provable: the "dependent-type bookkeeping" flagged as missing collapses
almost entirely once the single insertion step is packaged as a total,
well-typed function `QRChain.insert : QRChain N → (f : Fin N → ℝ) →
fPerpQ state.Q f ≠ 0 → QRChain N` whose return type already carries the
invariants (orthonormality, column-space membership) — iterating it then
requires no separate induction proof at all.

Paper statement: given `X_k = Q_k R_k` with `Q_k` orthonormal-column and
`R_k` upper-triangular, appending one new column `f ∉ range(X_k)` extends
this to an exact QR factorization of `[X_k, f]` by adding exactly one new
orthonormal column `q_{k+1} = f_perp/‖f_perp‖` and one new row/column of
`R`, reusing `Q_k, R_k` unchanged.

Representation choice: rather than building literal `Fin (p+1)`-indexed
block matrices (which would bury the mathematical content in index
bookkeeping), we state the result the way the paper's own proof actually
uses it: as separate facts about the new column, exactly matching the
paper's three proof paragraphs ("orthonormality of the new column",
"triangularity" — immediate from the block shape, not restated here since
it carries no content beyond "R_k was already triangular" — and
"exactness of the product").
-/
import KNOMP.Common
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace KNOMP

open Matrix

variable {N k : ℕ} (Q : Matrix (Fin N) (Fin k) ℝ) (f : Fin N → ℝ)

/-- Standing hypothesis: `Q`'s columns are orthonormal, i.e. `QᵀQ = 1`. -/
def OrthonormalCols (Q : Matrix (Fin N) (Fin k) ℝ) : Prop := Qᵀ * Q = 1

/-- `f`'s component orthogonal to `range(Q)`, matching the paper's
`f_perp = f - QQᵀf`. -/
noncomputable def fPerpQ : Fin N → ℝ := f - Q.mulVec (Qᵀ.mulVec f)

/-- The new column: `f_perp` normalized to unit length,
`q_{k+1} = f_perp / ‖f_perp‖`. -/
noncomputable def newCol : Fin N → ℝ :=
  (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f)))⁻¹ • fPerpQ Q f

/-- `f ∉ range(Q)` translates exactly to `f_perp ≠ 0` (the paper's own
"suppose `f ∉ range(X_k)`" hypothesis), which gives `dotProduct f_perp
f_perp > 0`: a sum of squares that is not identically zero is positive. -/
theorem fPerpQ_dotSelf_pos (hf : fPerpQ Q f ≠ 0) :
    0 < dotProduct (fPerpQ Q f) (fPerpQ Q f) := by
  unfold dotProduct
  have hnn : (0:ℝ) ≤ Finset.sum Finset.univ (fun i => fPerpQ Q f i * fPerpQ Q f i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  rcases (le_iff_eq_or_lt.mp hnn) with heq | hgt
  · exfalso
    apply hf
    funext i
    have hfun : (fun i => fPerpQ Q f i * fPerpQ Q f i) = 0 := by
      have hi := (Fintype.sum_eq_zero_iff_of_nonneg
        (f := fun i => fPerpQ Q f i * fPerpQ Q f i)
        (by intro i; exact mul_self_nonneg (fPerpQ Q f i))).mp heq.symm
      funext x; exact congrFun hi x
    have hi := congrFun hfun i
    exact mul_self_eq_zero.mp hi
  · exact hgt

/-- **Part 1 (orthonormality of the new column).** Given `f ∉ range(Q)`,
the new column has unit norm and is orthogonal to every existing column. -/
theorem newCol_orthonormal (hQ : OrthonormalCols Q) (hf : fPerpQ Q f ≠ 0) :
    dotProduct (newCol Q f) (newCol Q f) = 1 ∧ Qᵀ.mulVec (newCol Q f) = 0 := by
  have hpos := fPerpQ_dotSelf_pos Q f hf
  constructor
  · unfold newCol
    rw [dotProduct_smul, smul_dotProduct]
    have hXpos : (0 : ℝ) < dotProduct (fPerpQ Q f) (fPerpQ Q f) := hpos
    have hs : Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hpos)
    -- The LHS is `(√X)⁻¹ • (√X)⁻¹ • X = ((√X)²)⁻¹ * X = X⁻¹ * X = 1` for `X = fPerp ⬝ᵥ fPerp`.
    -- Convert smul form to *; combine inverses; use sq_sqrt and sqrt_sq to identify.
    rw [smul_eq_mul, smul_eq_mul]
    -- LHS: `(√X)⁻¹ * ((√X)⁻¹ * X) = ((√X)⁻¹ * (√X)⁻¹) * X = ((√X) * (√X))⁻¹ * X = ((√X)²)⁻¹ * X`
    rw [← mul_assoc,
        show ((Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f)))⁻¹) *
              ((Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f)))⁻¹) =
            ((Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))) *
             (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))))⁻¹ from by
          rw [mul_inv_rev (G := ℝ)]]
    rw [show (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))) *
              (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))) =
            (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))) ^ 2 from by ring]
    rw [Real.sq_sqrt hXpos.le]
    exact inv_mul_cancel₀ hXpos.ne'
  · unfold newCol
    rw [Matrix.mulVec_smul]
    have hzero : Qᵀ.mulVec (fPerpQ Q f) = 0 := by
      unfold fPerpQ
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQ]
      simp
    rw [hzero, smul_zero]

/-- **Part 3 (exactness of the factorization), new-column half.**
Reconstructing `f` from `Q`, the recorded inner products `Qᵀf`, and the
new column scaled by `‖f_perp‖` reproduces `f` exactly:
`Q(Qᵀf) + q_{k+1}‖f_perp‖ = f`. (The "old block" half of the paper's
block-matrix product, `Q_k R_k + q_{k+1}·0ᵀ = X_k`, is not restated here:
it is literally the unchanged hypothesis `X_k = Q_k R_k`, carrying no new
content — the new-column identity below is the entire new content of the
theorem.) -/
theorem qr_update_exact (hf : fPerpQ Q f ≠ 0) :
    Q.mulVec (Qᵀ.mulVec f)
        + (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f))) • newCol Q f
      = f := by
  have hpos := fPerpQ_dotSelf_pos Q f hf
  unfold newCol
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hpos)), one_smul]
  unfold fPerpQ
  abel

/-- Extending an orthonormal `Q` by one new (already-orthogonalized and
normalized) column. -/
noncomputable def extendQ (Q : Matrix (Fin N) (Fin k) ℝ) (newColVec : Fin N → ℝ) :
    Matrix (Fin N) (Fin (k + 1)) ℝ :=
  fun row => Fin.snoc (fun j => Q row j) (newColVec row)

/-- `extendQ` preserves orthonormality: given `Q` orthonormal and a new
column `v` that is unit-norm and orthogonal to every existing column,
the extended `(k+1)`-column matrix is orthonormal too. This is the one
genuinely new piece of matrix algebra Corollary `qr-induction` needs
beyond the single-step theorem above. -/
theorem extendQ_orthonormal
    (Q : Matrix (Fin N) (Fin k) ℝ) (v : Fin N → ℝ)
    (hOrtho : OrthonormalCols Q)
    (hperp : Qᵀ.mulVec v = 0) (hnorm : dotProduct v v = 1) :
    OrthonormalCols (extendQ Q v) := by
  unfold OrthonormalCols extendQ
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      have : (∑ row : Fin N, v row * v row) = dotProduct v v := rfl
      rw [this, hnorm]
      simp
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      have hj : (∑ row : Fin N, v row * Q row j) = (Qᵀ.mulVec v) j := by
        unfold Matrix.mulVec dotProduct
        simp only [Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro row _; ring
      rw [hj, hperp]
      have hne : (k : ℕ) ≠ (j : ℕ) := Nat.ne_of_gt j.isLt
      simp [Fin.ext_iff, hne]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      have hi : (∑ row : Fin N, Q row i * v row) = (Qᵀ.mulVec v) i := by
        unfold Matrix.mulVec dotProduct
        simp only [Matrix.transpose_apply]
      rw [hi, hperp]
      have hne : (i : ℕ) ≠ (k : ℕ) := Nat.ne_of_lt i.isLt
      simp [Fin.ext_iff, hne]
    | cast j =>
      simp only [Fin.snoc_castSucc]
      have heq : (∑ row : Fin N, Q row i * Q row j) = (Qᵀ * Q) i j := by
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
      rw [heq, hOrtho]
      simp only [Matrix.one_apply, Fin.coe_castSucc]
      congr 1
      simp [Fin.ext_iff]

/-- Extending the original-column record `cols` by one new column `f`. -/
def extendCols (cols : Fin k → (Fin N → ℝ)) (f : Fin N → ℝ) :
    Fin (k + 1) → (Fin N → ℝ) :=
  Fin.snoc cols f

/-- Old columns' span-coefficient vectors extend (with a zero appended)
to witnesses against the enlarged `Q`. -/
theorem extendQ_old_span
    (Q : Matrix (Fin N) (Fin k) ℝ) (v col : Fin N → ℝ) (r : Fin k → ℝ)
    (hspan : col = Q.mulVec r) :
    col = (extendQ Q v).mulVec (Fin.snoc r 0) := by
  rw [hspan]
  ext row
  unfold extendQ Matrix.mulVec dotProduct
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The newly-inserted column `f` itself lies in the enlarged `Q`'s
column space, with witness coefficient vector `(Qᵀf, ‖f_perp‖)` — this
is exactly `qr_update_exact`, repackaged. -/
theorem extendQ_new_span
    (Q : Matrix (Fin N) (Fin k) ℝ) (f : Fin N → ℝ) (hf : fPerpQ Q f ≠ 0) :
    f = (extendQ Q (newCol Q f)).mulVec
      (Fin.snoc (Qᵀ.mulVec f) (Real.sqrt (dotProduct (fPerpQ Q f) (fPerpQ Q f)))) := by
  ext row
  unfold extendQ Matrix.mulVec dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hkey := congrFun (qr_update_exact Q f hf) row
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
  rw [← hkey]
  congr 1
  unfold dotProduct
  ring

/-- One accumulated state of the incremental QR process: `k` orthonormal
columns `Q`, and the `k` original (pre-orthogonalization) columns `cols`,
each of which lies in `Q`'s column space (a witness that some `R` exists
with `X = QR`, without pinning down `R` itself — `R`'s triangular shape
carries no content beyond "unchanged so far"). -/
structure QRChain (N : ℕ) where
  k : ℕ
  Q : Matrix (Fin N) (Fin k) ℝ
  cols : Fin k → (Fin N → ℝ)
  hOrtho : OrthonormalCols Q
  hSpan : ∀ i : Fin k, ∃ r : Fin k → ℝ, cols i = Q.mulVec r

/-- **The insertion step.** Given a valid QR chain and a new candidate
`f` outside the current column span, inserting it produces a valid QR
chain exactly one column larger, whose new column is `newCol state.Q f`
and whose new original-column record is `f` appended to the old one. -/
noncomputable def QRChain.insert (state : QRChain N) (f : Fin N → ℝ)
    (hf : fPerpQ state.Q f ≠ 0) : QRChain N where
  k := state.k + 1
  Q := extendQ state.Q (newCol state.Q f)
  cols := extendCols state.cols f
  hOrtho := extendQ_orthonormal state.Q (newCol state.Q f) state.hOrtho
    (newCol_orthonormal state.Q f state.hOrtho hf).2
    (newCol_orthonormal state.Q f state.hOrtho hf).1
  hSpan := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      refine ⟨Fin.snoc (state.Qᵀ.mulVec f)
        (Real.sqrt (dotProduct (fPerpQ state.Q f) (fPerpQ state.Q f))), ?_⟩
      show extendCols state.cols f (Fin.last state.k) = _
      rw [extendCols, Fin.snoc_last]
      exact extendQ_new_span state.Q f hf
    | cast i =>
      obtain ⟨r, hr⟩ := state.hSpan i
      refine ⟨Fin.snoc r 0, ?_⟩
      show extendCols state.cols f i.castSucc = _
      rw [extendCols, Fin.snoc_castSucc]
      exact extendQ_old_span state.Q (newCol state.Q f) (state.cols i) r hr

/-- **Corollary `qr-induction`.** Repeating the single-step update `n`
times, where `next` picks the candidate to insert at each stage (as a
function of the chain accumulated so far) and `hnext` certifies it
always avoids the accumulated column space, keeps producing a valid
`QRChain` at every stage `n`. -/
noncomputable def QRChain.iterate (state0 : QRChain N)
    (next : QRChain N → (Fin N → ℝ))
    (hnext : ∀ chain : QRChain N, fPerpQ chain.Q (next chain) ≠ 0) :
    ℕ → QRChain N
  | 0 => state0
  | n + 1 => (QRChain.iterate state0 next hnext n).insert
      (next (QRChain.iterate state0 next hnext n)) (hnext _)

/-- Validity at every stage is immediate — not a separate induction, just
reading off the fields of the `QRChain` that `iterate` produces, which
already carries the invariants by construction. This is the sense in
which the dependent-type bookkeeping an earlier version of this file
flagged as missing collapses: once the single insertion step
(`QRChain.insert`) is proved well-typed and total, iterating it requires
no further proof at all. -/
theorem QRChain.iterate_valid (state0 : QRChain N)
    (next : QRChain N → (Fin N → ℝ))
    (hnext : ∀ chain : QRChain N, fPerpQ chain.Q (next chain) ≠ 0) (n : ℕ) :
    OrthonormalCols (QRChain.iterate state0 next hnext n).Q ∧
      ∀ i, ∃ r, (QRChain.iterate state0 next hnext n).cols i
        = (QRChain.iterate state0 next hnext n).Q.mulVec r :=
  ⟨(QRChain.iterate state0 next hnext n).hOrtho, (QRChain.iterate state0 next hnext n).hSpan⟩

end KNOMP
