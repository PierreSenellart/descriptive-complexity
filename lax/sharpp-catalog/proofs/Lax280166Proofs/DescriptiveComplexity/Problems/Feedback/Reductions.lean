/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.Defs
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Feedback (HasSmallFeedbackArcSet HasSmallFeedbackSet MAGAdj MAGMarked SurvivingArc UncutArc)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (HasSmallVertexCover MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Feedback (magAdj magMarked markedArcGraph)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Hardness of the feedback problems

Two quantifier-free first-order reductions, both of dimension 1:

* `DescriptiveComplexity.vertexCover_fo_reduction_feedbackVertexSet`: **Vertex Cover
  reduces to Feedback Vertex Set**, by *symmetrizing* the adjacency relation
  off the diagonal (`DescriptiveComplexity.symmetrizeInterp`, tag `Unit`). Every edge
  of the input becomes a 2-cycle, so a set of vertices kills every cycle iff
  it meets every edge – killing all 2-cycles already removes every arc
  (`DescriptiveComplexity.coverOn_iff_feedbackOn`). The marked set is copied, so there
  is no counting step at all.

* `DescriptiveComplexity.feedbackVertexSet_fo_reduction_feedbackArcSet`: **Feedback
  Vertex Set reduces to Feedback Arc Set**, by the classical *vertex
  splitting* (`DescriptiveComplexity.splitInterp`, tag `Bool`): each vertex `v` becomes
  an in-copy `DescriptiveComplexity.inPt` and an out-copy `DescriptiveComplexity.outPt`
  joined by an internal arc, and each arc `(u, v)` of the input becomes the
  crossing arc from `u`'s out-copy to `v`'s in-copy. Cutting the internal arc
  of `v` is deleting the vertex `v`; the marked relation marks exactly the
  internal arcs of the marked vertices, so the threshold is preserved on the
  nose.

## Splitting, without ever manipulating a cycle

The correctness of the splitting is where the certificate form of acyclicity
(`DescriptiveComplexity.acyclicRel_iff_exists_order`) pays off: both directions build a
strict partial order out of another one, and no cycle is ever decomposed.

* Forward, a feedback vertex set `C` of the input with certificate order `Lt`
  gives the order `DescriptiveComplexity.splitLt`: the out-copies of `C` go to the
  bottom, the in-copies of `C` to the top, and everything else keeps `Lt`
  (with the in-copy of a vertex just below its out-copy). Every uncut arc goes
  forward in it – the case that needs `Lt` is exactly a crossing arc between
  two vertices outside `C`, which is a surviving arc of the input.
* Backward, a feedback arc set `F` of the split graph gives back the set of
  *source vertices* of the arcs in `F`, which is no larger
  (`Set.ncard_image_le`), and the order `fun u v => Lt' (inPt u) (inPt v)`.
  For an input arc `(u, v)` with both endpoints outside that set, neither the
  internal arc of `u` nor the crossing arc `(u_out, v_in)` can be in `F`,
  since both have source vertex `u`; so both go forward in `Lt'`, and
  transitivity closes the case.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Vertex Cover reduces to Feedback Vertex Set -/

/-- The symmetrizing interpretation: adjacency becomes off-diagonal adjacency
in either direction – so every edge becomes a 2-cycle – and marks are
kept. -/
def symmetrizeInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.CliqueFamily.markedGraph Lax799700.CliqueFamily.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ => FirstOrder.Language.BoundedFormula.not
                                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))) ⊓
                              (FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0))
                                  (FirstOrder.Language.Term.var (1, 0)) ⊔
                                FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (1, 0))
                                  (FirstOrder.Language.Term.var (0, 0)))
    | _, .marked => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0))

section SymmetrizeCharacterizations

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

@[simp]
theorem symmetrize_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := symmetrizeInterp.Map A) Lax799700.CliqueFamily.mgAdj ![((), w₁), ((), w₂)] ↔
      w₁ 0 ≠ w₂ 0 ∧ (RelMap Lax799700.CliqueFamily.mgAdj ![w₁ 0, w₂ 0] ∨ RelMap Lax799700.CliqueFamily.mgAdj ![w₂ 0, w₁ 0]) := by
  rw [FOInterpretation.relMap_map]
  simp [symmetrizeInterp, Formula.realize_rel₂]

@[simp]
theorem symmetrize_marked (w : Fin 1 → A) :
    RelMap (M := symmetrizeInterp.Map A) Lax799700.CliqueFamily.mgMarked ![((), w)] ↔ RelMap Lax799700.CliqueFamily.mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [symmetrizeInterp, Formula.realize_rel₁]

end SymmetrizeCharacterizations

section SymmetrizeCorrectness

end SymmetrizeCorrectness

/-! ### Feedback Vertex Set reduces to Feedback Arc Set

The vertex-splitting interpretation: the tag `true` carries the in-copy of a
vertex and the tag `false` its out-copy. -/

/-! #### The two copies of a vertex -/

section Copies

end Copies

/-! #### The arcs and marks of the split digraph -/

section SplitCharacterizations

/-! #### The interface used by the correctness proofs

Rather than the raw characterizations, the proofs below use the two arc
constructors and the two “only these” lemmas, which never mention the shape of
an element of the interpreted universe. -/

end SplitCharacterizations

/-! #### Counting on the internal arcs -/

section SplitCounting

end SplitCounting

/-! #### Correctness of the splitting -/

section SplitOrder

end SplitOrder

section SplitCorrectness

end SplitCorrectness

end Lax280166Proofs.DescriptiveComplexity


