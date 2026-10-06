/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Vocabulary
import Lax859101Proofs.DescriptiveComplexity.Interpretation
import Lax859101Proofs.DescriptiveComplexity.Numbers.Unary
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

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax859101Proofs.DescriptiveComplexity.CoversOn
end Lax859101Proofs.DescriptiveComplexity.CoversOn

namespace Lax859101Proofs.DescriptiveComplexity.ExactlyCoversOn
end Lax859101Proofs.DescriptiveComplexity.ExactlyCoversOn

namespace Lax859101Proofs.DescriptiveComplexity.HitsOn
end Lax859101Proofs.DescriptiveComplexity.HitsOn

namespace Lax859101Proofs.DescriptiveComplexity.PacksOn
end Lax859101Proofs.DescriptiveComplexity.PacksOn

namespace Lax859101Proofs.DescriptiveComplexity.SplitsOn
end Lax859101Proofs.DescriptiveComplexity.SplitsOn

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.SetFamily (CoversOn ExactlyCoversOn HasExactCover HasLargeSetPacking HasSetSplitting HasSmallHittingSet HasSmallSetCover HitsOn PacksOn SSElem SSFam SSMarked SSMem SplitsOn)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem ssElem ssFam ssMarked ssMem)
end FirstOrder.Language

/-!
# Set Cover, Hitting Set and Set Packing: definitions

The three classical problems on set systems ([Karp 1972][karp1972reducibility]),
as decision problems on `FirstOrder.Language.setSystem`-structures: a universe
carrying two unary marks separating the ground *elements* from the *sets* of a
family, a binary incidence relation between them, and a third unary mark
carrying the numeric threshold `k` in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary` (the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free).

* `DescriptiveComplexity.SetCover`: some subfamily of at most `k` sets covers every
  element;
* `DescriptiveComplexity.HittingSet`: some set of at most `k` elements meets every
  set of the family;
* `DescriptiveComplexity.SetPacking`: some subfamily of at least `k` pairwise
  disjoint sets exists.

They are the set-system counterparts of the clique family
(`DescriptiveComplexity.Problems.CliqueFamily`), and are organized the same way: the
semantics is carried by generic properties of predicates on a type –
`DescriptiveComplexity.CoversOn`, its transpose `DescriptiveComplexity.HitsOn` (elements
and sets exchanged, incidence read backwards) and `DescriptiveComplexity.PacksOn` –
which the isomorphism-invariance proofs and the reductions share. Set Cover
and Hitting Set being literally one property read in two directions is what
makes them inter-reducible by a single interpretation
(`DescriptiveComplexity.Problems.SetFamily.Reductions`), just as complementation
relates Clique and Independent Set.

Two conventions worth stating once:

* Nothing forces an element of the universe to be an element or a set, or
  forbids it to be both: elements outside both marks are junk that no
  condition mentions, which is what lets a first-order interpretation build a
  set system inside a tagged power of its input universe without a
  definable-subset mechanism. Junk *marked* elements would change the
  threshold, so interpretations remain responsible for the mark they define.
* Disjointness in `DescriptiveComplexity.PacksOn` is required of the ground
  elements only. This is not cosmetic: the interpretation of
  `DescriptiveComplexity.Problems.SetFamily.FromGraphs` produces junk tuples incident
  to two sets each, and those must not count as witnesses of an intersection.

As with the clique family, cardinality thresholds are only meaningful on
finite structures, so finiteness of the universe is part of the yes-instances;
by `DescriptiveComplexity.ComplexityClass.mem_congr_finite` this does not affect
any complexity-theoretic statement.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic covering property

The property underlying both problems, for arbitrary unary predicates `Ep`
(ground elements), `Fp` (sets of the family) and `Kp` (marks), and an
arbitrary binary predicate `Mp` (incidence) on a type. -/

section Generic

/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold condition can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/

section Embedding

end Embedding

end Generic

/-! ### The two problems -/

section Problems

section Shorthands

variable {A : Type} [Lax799700.SetFamily.setSystem.Structure A]

end Shorthands

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

end Iso

end Lax859101Proofs.DescriptiveComplexity


