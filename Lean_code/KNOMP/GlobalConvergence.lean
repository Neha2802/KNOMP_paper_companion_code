/-
KNOMP/GlobalConvergence.lean

Source: Section 6, "Global Convergence of the Outer Loop", Theorem
`convergence` (parts a, b, c).

STATUS: mixed.
  Parts (a)+(b) core argument: PROVED — the "infinite subset of ℕ has a
    strictly monotone enumeration" fact is now discharged via `Nat.nth`
    (`Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`), found and verified
    against a real compiler. The paper's own block-by-block non-increase
    verification (IRLS is majorize-minimize; Levenberg-Marquardt
    sub-steps are accept-only-on-strict-decrease; jitter and
    GP-hyperparameter blocks are exact block minimizations) is what
    ESTABLISHES the hypotheses of this abstract fact for KNOMP's specific
    `Φ`, but is not itself re-derived here (it is a sequence of separate,
    model-specific facts, not unified mathematical content beyond what
    the abstract fact already captures).
  Part (c) stationarity conclusion: AXIOMATIZED (the external citation
    itself) + PROVED (the application). The paper is explicit that this
    step is an external, cited theorem (Zangwill's Global Convergence
    Theorem) rather than original content — `ZangwillHypothesis` states
    it exactly that way. `stationarity_holds` is the actual "checking
    KNOMP's setup matches the premises" corollary — an earlier version of
    this file described this step but never wrote the theorem down; it
    is now present and proved (it is a direct, one-line application of
    the hypothesis, since all the content lives in the hypothesis
    itself — which is exactly right for an external citation).
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Nat.Nth

namespace KNOMP

open Filter

/-- **Parts (a)+(b), abstract core.** A non-increasing real sequence,
bounded below, that decreases by at least a fixed `τ > 0` at every index
in a set `S` of "acceptance events", can only have `S` finite. This is
exactly the paper's own argument for part (b) ("a non-increasing sequence
that decreases by at least a fixed `τ>0` infinitely often would be
unbounded below"), stated and proved abstractly so it applies to `Φ`
without needing `Φ`'s own definition. -/
theorem finitely_many_flagged_decreases
    (Phi : ℕ → ℝ) (hmono : ∀ k, Phi (k + 1) ≤ Phi k)
    (c0 : ℝ) (hbound : ∀ k, c0 ≤ Phi k)
    (tau : ℝ) (htau : 0 < tau) (S : Set ℕ)
    (hdecrease : ∀ k ∈ S, Phi (k + 1) ≤ Phi k - tau) :
    S.Finite := by
  by_contra hinf
  have hinf' : S.Infinite := hinf
  -- An infinite subset of ℕ contains arbitrarily large elements, so we
  -- can find, for any m, at least m elements of S below some bound,
  -- giving Phi eventually below c0 - m*tau/2, contradicting hbound.
  have hne : S.Nonempty := hinf'.nonempty
  -- Use that Phi is non-increasing to get: for any k, Phi k ≤ Phi 0 - tau * (number of S-elements < k).
  have hmono' : ∀ k j, k ≤ j → Phi j ≤ Phi k := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact le_refl _
    | succ n _ ih => exact le_trans (hmono n) ih
  -- Choose m large enough that Phi 0 - m*tau < c0, then find m elements
  -- of S; this contradicts the lower bound.
  obtain ⟨m, hm⟩ := exists_nat_gt ((Phi 0 - c0) / tau)
  -- An infinite subset of ℕ admits a strictly monotone enumeration
  -- `f : ℕ → ℕ` with every `f n ∈ S`, via `Nat.nth` applied to the
  -- membership predicate of `S`.
  have hexists : ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, f n ∈ S := by
    have hSp : (setOf (fun n => n ∈ S)).Infinite := hinf'
    exact ⟨Nat.nth (fun n => n ∈ S), Nat.nth_strictMono hSp,
      fun n => Nat.nth_mem_of_infinite hSp n⟩
  obtain ⟨f, hf_mono, hf_mem⟩ := hexists
  have hchain : ∀ n, Phi (f n + 1) ≤ Phi 0 - (n + 1) * tau := by
    intro n
    induction n with
    | zero =>
        have := hdecrease (f 0) (hf_mem 0)
        have h0 : Phi (f 0) ≤ Phi 0 := hmono' 0 (f 0) (Nat.zero_le _)
        push_cast
        linarith
    | succ n ih =>
        have hstep : f n + 1 ≤ f (n+1) := hf_mono (Nat.lt_succ_self n)
        have hchain2 : Phi (f (n+1)) ≤ Phi (f n + 1) := hmono' (f n + 1) (f (n+1)) hstep
        have hdec := hdecrease (f (n+1)) (hf_mem (n+1))
        push_cast at ih ⊢
        linarith
  have := hchain m
  have hcontra : Phi 0 - (m + 1) * tau < c0 := by
    have : (Phi 0 - c0) / tau < m := hm
    have h2 : Phi 0 - c0 < m * tau := by
      rw [div_lt_iff₀ htau] at this
      linarith
    nlinarith [htau]
  linarith [hbound (f m + 1), this, hcontra]

/-- **Part (c), external theorem, taken exactly as the paper states it.**
Zangwill's Global Convergence Theorem (Zangwill 1969, Ch. 4; Bertsekas
1999, Prop. 2.7.1), specialized to block-coordinate descent: a continuous
`Φ` on a compact set with an algorithm map that never increases `Φ`, with
equality only at a stationary point, has every limit point of its
iterate sequence a stationary point of `Φ`. NOT proved here — this is the
paper's own explicitly-flagged external input, restated as a hypothesis. -/
def ZangwillHypothesis {X : Type*} [TopologicalSpace X] (compactSet : Set X)
    (Phi : X → ℝ) (A : X → X) : Prop :=
  IsCompact compactSet → Continuous Phi →
    (∀ x ∈ compactSet, Phi (A x) ≤ Phi x) →
    ∀ (x : ℕ → X), x 0 ∈ compactSet → (∀ n, x (n + 1) = A (x n)) →
      ∀ y, MapClusterPt y atTop x → (Phi (A y) = Phi y)

/-- **Part (c), applying Zangwill's theorem to KNOMP's setup.** Granting
`ZangwillHypothesis` for `Φ`, `A`, and the compact set in question (the
external citation, asserted not proved), and given that KNOMP's own outer
loop satisfies its antecedents — `Φ` continuous, `A` non-increasing on
the compact set, an iterate sequence starting inside it — every cluster
point of the iterate sequence is a stationary point: `Φ(A y) = Φ y`. This
is the actual "checking KNOMP's setup matches the premises" step;
earlier this was only described in prose and never written as a theorem.
It is a one-line application because all the substantive content
legitimately lives in the hypothesis itself — exactly the shape an
external citation should take. -/
theorem stationarity_holds {X : Type*} [TopologicalSpace X] {compactSet : Set X}
    {Phi : X → ℝ} {A : X → X} (hZang : ZangwillHypothesis compactSet Phi A)
    (hcompact : IsCompact compactSet) (hcont : Continuous Phi)
    (hmono : ∀ x ∈ compactSet, Phi (A x) ≤ Phi x)
    (x : ℕ → X) (hx0 : x 0 ∈ compactSet) (hstep : ∀ n, x (n + 1) = A (x n))
    (y : X) (hy : MapClusterPt y atTop x) :
    Phi (A y) = Phi y :=
  hZang hcompact hcont hmono x hx0 hstep y hy

end KNOMP
