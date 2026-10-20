/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Vocabulary
import Lax794877Proofs.DescriptiveComplexity.Interpretation
import Lax794877Proofs.DescriptiveComplexity.Numbers.Unary
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

namespace Lax794877Proofs.DescriptiveComplexity.CliqueOn
end Lax794877Proofs.DescriptiveComplexity.CliqueOn

namespace Lax794877Proofs.DescriptiveComplexity.CoverOn
end Lax794877Proofs.DescriptiveComplexity.CoverOn

namespace Lax794877Proofs.DescriptiveComplexity.IndepOn
end Lax794877Proofs.DescriptiveComplexity.IndepOn

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (CliqueOn CoverOn HasLargeClique HasLargeIndependentSet HasSmallVertexCover IndepOn MGAdj MGMarked)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# Clique, Independent Set and Vertex Cover: definitions

The three classical threshold problems on graphs, as decision problems on
*marked graphs*: `FirstOrder.Language.markedGraph`-structures, carrying a
binary adjacency relation and a unary mark. The marked set carries the numeric
threshold `k` of the textbook problems in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary`: the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free.

* `DescriptiveComplexity.Clique`: some clique is at least as large as the marked set;
* `DescriptiveComplexity.IndependentSet`: some independent set is at least as large as
  the marked set;
* `DescriptiveComplexity.VertexCover`: some vertex cover is at most as large as the
  marked set.

The threshold comparisons are comparisons of decoded numbers, and the
cardinality arithmetic they need is the shared kit of
`DescriptiveComplexity.Numbers.Unary`: invariance of a decoded number under an
equivalence of universes (`DescriptiveComplexity.ncard_image_equiv`) for the
isomorphism-invariance proofs, the reversal of a comparison under
complementation (`DescriptiveComplexity.ncard_compl_le_ncard_compl_iff`) for the
Vertex Cover ↔ Independent Set reductions, and the equivalence with the
existence of an injection (`DescriptiveComplexity.nonempty_embedding_iff_ncard_le`,
here `DescriptiveComplexity.cliqueOn_iff_embedding`) for the second-order definition,
which guesses that injection as a relation variable. Since cardinality
thresholds are only meaningful on finite structures, finiteness of the
universe is part of the yes-instances; by `ComplexityClass.mem_congr_finite`
this does not affect any complexity-theoretic statement.

Self-loops are ignored (all three properties are about the underlying
loopless graph), and adjacency is required in both directions on ordered
pairs, so the problems agree with their standard versions on (structures
encoding) simple graphs.

The three predicates are instances of generic properties `DescriptiveComplexity.CliqueOn`
/ `IndepOn` / `CoverOn` of a binary and a unary predicate on a type; the
generic form is shared by the isomorphism-invariance proofs and by the
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions`.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Generic threshold properties

The properties underlying the three problems, for an arbitrary binary
predicate `Adjp` (adjacency) and unary predicate `Kp` (marks) on a type. -/

section Generic

/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold conditions can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/

section Embedding

end Embedding

end Generic

/-! ### The three problems -/

section Problems

section Shorthands

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

end Shorthands

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

end Iso

end Lax794877Proofs.DescriptiveComplexity


