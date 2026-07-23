/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.Defs
import DescriptiveComplexity.Problems.Feedback.Reductions
import DescriptiveComplexity.Problems.Feedback.Membership
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.Composition

/-!
# The feedback problems are NP-complete

Umbrella file for Feedback Vertex Set and Feedback Arc Set
(`DescriptiveComplexity.FeedbackVertexSet`, `DescriptiveComplexity.FeedbackArcSet`, defined
in `DescriptiveComplexity.Problems.Feedback.Defs`), collecting the quantifier-free
reductions of `DescriptiveComplexity.Problems.Feedback.Reductions` and deriving
NP-completeness from

* `DescriptiveComplexity.feedbackVertexSet_sigmaSODefinable` and
  `DescriptiveComplexity.feedbackArcSet_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.Feedback.Membership`): membership, by guessing the
  removed object, an order certifying acyclicity, and the threshold injection;
* `DescriptiveComplexity.vertexCover_fo_reduction_feedbackVertexSet`: hardness of
  Feedback Vertex Set, from the NP-hardness of Vertex Cover
  (`DescriptiveComplexity.Problems.CliqueFamily`), and so ultimately from the
  Cook–Levin theorem, with no machine model anywhere;
* `DescriptiveComplexity.feedbackVertexSet_fo_reduction_feedbackArcSet`: hardness of
  Feedback Arc Set, one step further along the chain.

The two problems live over *different* vocabularies – Feedback Vertex Set
over marked graphs, Feedback Arc Set over arc-marked digraphs – because their
thresholds count different things, so there is no analogue here of the
transposition inside the set family: the chain
`Vertex Cover ≤ᶠᵒ Feedback Vertex Set ≤ᶠᵒ Feedback Arc Set` is one-way.
As with any complexity-theoretic statement, these results are about finite
structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- **Vertex Cover FO-reduces to Feedback Arc Set**, by composing the
symmetrization with the vertex splitting. -/
noncomputable def vertexCover_fo_reduction_feedbackArcSet : VertexCover ≤ᶠᵒ FeedbackArcSet :=
  vertexCover_fo_reduction_feedbackVertexSet.trans feedbackVertexSet_fo_reduction_feedbackArcSet

/-! ### NP-completeness -/

/-- Feedback Vertex Set is in NP: it is `Σ₁`-definable. -/
theorem feedbackVertexSet_mem_NP : FeedbackVertexSet ∈ NP :=
  feedbackVertexSet_sigmaSODefinable

/-- Feedback Vertex Set is NP-hard: Vertex Cover, which is NP-hard, reduces
to it by symmetrizing the adjacency relation. -/
theorem feedbackVertexSet_NP_hard : NP.Hard FeedbackVertexSet :=
  NP.hard_of_foReduction vertexCover_fo_reduction_feedbackVertexSet vertexCover_NP_hard

/-- **Feedback Vertex Set is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem feedbackVertexSet_NP_complete : NP.Complete FeedbackVertexSet :=
  ⟨feedbackVertexSet_mem_NP, feedbackVertexSet_NP_hard⟩

/-- Feedback Arc Set is in NP: it is `Σ₁`-definable. -/
theorem feedbackArcSet_mem_NP : FeedbackArcSet ∈ NP :=
  feedbackArcSet_sigmaSODefinable

/-- Feedback Arc Set is NP-hard: Feedback Vertex Set, which is NP-hard,
reduces to it by vertex splitting. -/
theorem feedbackArcSet_NP_hard : NP.Hard FeedbackArcSet :=
  NP.hard_of_foReduction feedbackVertexSet_fo_reduction_feedbackArcSet feedbackVertexSet_NP_hard

/-- **Feedback Arc Set is NP-complete**. -/
theorem feedbackArcSet_NP_complete : NP.Complete FeedbackArcSet :=
  ⟨feedbackArcSet_mem_NP, feedbackArcSet_NP_hard⟩

end DescriptiveComplexity
