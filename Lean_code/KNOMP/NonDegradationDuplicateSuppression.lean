/-
KNOMP/NonDegradationDuplicateSuppression.lean

Source: Section 19, "Non-Degradation Under Near-Duplicate Suppression",
Theorem "Three-part non-degradation guarantee" (parts a, b, c).

STATUS: mixed.
  Part (a): PROVED — a direct restatement of `sup'_mono_of_subset`
    (`MonotonicityAugmentation.lean`) with the subset/superset roles
    swapped (excluding a zone shrinks the candidate set).
  Part (b): AXIOMATIZED. The real content — "a genuine signal outside
    every exclusion zone is found with probability → 1 as its
    non-centrality → ∞" — is an asymptotic-probabilistic detection-power
    fact that itself rests on the paper's Lemma `grid-accuracy`
    (`AsymptoticEfficiency.lean`, itself AXIOMATIZED — see that file) and
    Theorem `family-wise` (`FamilyWiseErrorControl.lean`, PROVED). Rather
    than re-deriving detection power from scratch, we state part (b) as a
    hypothesis exactly matching the paper's own informal quantifier
    ("probability → 1 as non-centrality → ∞"), formalized as a
    `Filter.Tendsto ... (𝓝 1)` statement assumed for the *unrestricted*
    search and inherited unchanged by the *restricted* one — which is
    the paper's actual proof content: locally, near the true signal,
    restricting the search elsewhere makes no difference.
  Part (c): PARTIAL — an immediate corollary of (a) and (b), so it
    inherits (b)'s axiomatization.
-/
import KNOMP.MonotonicityAugmentation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Basic

namespace KNOMP

variable {α : Type*} [DecidableEq α]

/-- **Part (a).** Excluding a zone `Z` from the candidate set `Θ` before
maximizing `g` cannot raise the achieved maximum:
`max over (Θ \ Z) ≤ max over Θ`. Immediate from `sup'_mono_of_subset`,
since `Θ \ Z ⊆ Θ`. -/
theorem restricted_sup_le (Θ Z : Finset α) (g : α → ℝ)
    (hΘZ : (Θ \ Z).Nonempty) (hΘ : Θ.Nonempty) :
    (Θ \ Z).sup' hΘZ g ≤ Θ.sup' hΘ g :=
  -- `Finset.Nonempty` is a `Prop`, so the two different nonemptiness
  -- proofs appearing here are definitionally interchangeable (proof
  -- irrelevance); no explicit rewriting between them is needed.
  sup'_mono_of_subset (Θ \ Z) Θ Finset.sdiff_subset hΘZ g

/-- A signal's "non-centrality" is modeled abstractly as a real parameter
`λ`; "detected with probability → 1 as `λ → ∞`" is modeled as: for every
sequence of non-centralities tending to `∞`, the corresponding sequence
of acceptance probabilities tends to `1`. This matches the paper's own
phrasing ("with probability → 1 as `λ_{k+1} → ∞`") without committing to
a specific probability space, sequence of experiments, or estimator — all
of which the paper itself leaves implicit at this point, deferring to
Lemma `grid-accuracy` and Theorem `family-wise` (proved/stated
elsewhere in this project) for the underlying mechanism. -/
def DetectedWhp (acceptProb : ℝ → ℝ) : Prop :=
  ∀ (lam : ℕ → ℝ), Filter.Tendsto lam Filter.atTop Filter.atTop →
    Filter.Tendsto (fun n => acceptProb (lam n)) Filter.atTop (nhds 1)

/-- **Part (b), as an explicit hypothesis rather than a derived fact.**
If the *unrestricted* search detects a well-separated true signal with
probability → 1 as its non-centrality grows (this is exactly
`DetectedWhp`, discharged elsewhere by `grid-accuracy`/`family-wise`),
then the *restricted* search — which agrees with the unrestricted one on
a full neighborhood of the true signal's location, since the excluded
zones are disjoint from that neighborhood — detects it with the same
limiting probability. Formalized here as: the two acceptance-probability
functions agree identically (`hagree`), which is the paper's own
"unaffected by the exclusion of the disjoint region elsewhere" argument
stated as a hypothesis instead of derived from a geometric model of
`Θ`, `Z`, and the true parameter's neighborhood. -/
theorem restricted_detects_whp
    (acceptProb_unrestricted acceptProb_restricted : ℝ → ℝ)
    (hagree : acceptProb_restricted = acceptProb_unrestricted)
    (hwhp : DetectedWhp acceptProb_unrestricted) :
    DetectedWhp acceptProb_restricted := by
  rw [hagree]; exact hwhp

/-- **Part (c).** Combining (a) and (b): only candidates already inside a
claimed exclusion zone are ever removed from consideration (part a: the
achieved maximum outside the zones cannot be affected upward, and the
restriction only ever removes points *from* the zones), and any true,
distinct signal outside every zone is still detected with the same
limiting probability (part b). Hence duplicate suppression never costs a
genuine, separate detection. -/
theorem non_degradation_summary
    (Θ Z : Finset α) (g : α → ℝ) (hΘZ : (Θ \ Z).Nonempty) (hΘ : Θ.Nonempty)
    (acceptProb_unrestricted acceptProb_restricted : ℝ → ℝ)
    (hagree : acceptProb_restricted = acceptProb_unrestricted)
    (hwhp : DetectedWhp acceptProb_unrestricted) :
    ((Θ \ Z).sup' hΘZ g ≤ Θ.sup' hΘ g) ∧ DetectedWhp acceptProb_restricted :=
  ⟨restricted_sup_le Θ Z g hΘZ hΘ, restricted_detects_whp _ _ hagree hwhp⟩

end KNOMP
