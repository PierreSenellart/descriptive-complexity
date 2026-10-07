/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (CliqueOn CoverOn HasLargeClique HasLargeIndependentSet HasSmallVertexCover IndepOn MGAdj MGMarked)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Reductions between Clique, Independent Set and Vertex Cover

The classical reductions inside the clique family, as quantifier-free
first-order reductions on marked graphs (all of tag `Unit` and dimension 1):

* `DescriptiveComplexity.indSet_fo_reduction_clique` and
  `DescriptiveComplexity.clique_fo_reduction_indSet`: complementing the edges (off the
  diagonal) exchanges cliques and independent sets, keeping the marked set;
* `DescriptiveComplexity.vertexCover_fo_reduction_indSet` and
  `DescriptiveComplexity.indSet_fo_reduction_vertexCover`: complementing the *marked
  set* exchanges vertex covers and independent sets, keeping the edges – a
  set is a vertex cover iff its complement is independent, and (on a finite
  universe) it is at most as large as the marked set iff its complement is at
  least as large as the complement of the marked set;
* composites `DescriptiveComplexity.vertexCover_fo_reduction_clique` and
  `DescriptiveComplexity.clique_fo_reduction_vertexCover`.

The counting step of the vertex-cover reductions
(`DescriptiveComplexity.coverOn_iff_indepOn_not`) is the only place where finiteness is
used; it enters through the finiteness conjunct of the problems themselves. That
step is pure unary-representation arithmetic – complementing a marked set
subtracts its decoded number from the size of the universe, hence reverses
comparisons – and is discharged by
`DescriptiveComplexity.ncard_compl_le_ncard_compl_iff` and
`DescriptiveComplexity.ncard_compl_le_iff` of `DescriptiveComplexity.Numbers.Unary`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### Complementation lemmas for the generic properties -/

section Complement

end Complement

/-! ### The two interpretations -/

/-- The edge-complementing interpretation: adjacency becomes off-diagonal
non-adjacency, marks are kept. -/
def complEdgeInterp :
    Lax904597.Interpretations.FOInterpretation Lax799700.CliqueFamily.markedGraph Lax799700.CliqueFamily.markedGraph Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun _ => FirstOrder.Language.BoundedFormula.not
                                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))) ⊓
                              FirstOrder.Language.BoundedFormula.not
                                (FirstOrder.Language.Relations.formula₂ Lax799700.CliqueFamily.mgAdj (FirstOrder.Language.Term.var (0, 0))
                                  (FirstOrder.Language.Term.var (1, 0)))
    | _, .marked => fun _ => FirstOrder.Language.Relations.formula₁ Lax799700.CliqueFamily.mgMarked (FirstOrder.Language.Term.var (0, 0))

/-! ### Characterizations of the interpreted relations -/

section Characterizations

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

@[simp]
theorem complEdge_adj (w₁ w₂ : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) Lax799700.CliqueFamily.mgAdj ![((), w₁), ((), w₂)] ↔
      w₁ 0 ≠ w₂ 0 ∧ ¬RelMap Lax799700.CliqueFamily.mgAdj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₂]

@[simp]
theorem complEdge_marked (w : Fin 1 → A) :
    RelMap (M := complEdgeInterp.Map A) Lax799700.CliqueFamily.mgMarked ![((), w)] ↔ RelMap Lax799700.CliqueFamily.mgMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [complEdgeInterp, Formula.realize_rel₁]

end Characterizations

/-! ### Correctness -/

section Correctness

end Correctness

/-! ### The reductions -/

end Lax794877Proofs.DescriptiveComplexity


