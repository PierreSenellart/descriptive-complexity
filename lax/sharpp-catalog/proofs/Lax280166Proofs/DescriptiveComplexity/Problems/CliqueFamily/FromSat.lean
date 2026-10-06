/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax280166Proofs.DescriptiveComplexity.OccurrenceFormulas
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

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (HasLargeClique MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# SAT reduces to Clique by an ordered FO reduction

The classical reduction from satisfiability to the clique threshold problem,
as a first-order interpretation over the ordered expansion of the language of
CNF instances:
`DescriptiveComplexity.sat_ordered_fo_reduction_clique : SAT ≤ᶠᵒ[≤] Clique`.

Vertices of the interpreted marked graph are tagged pairs of elements of the
CNF structure (`DescriptiveComplexity.SatCliqueTag`, dimension 2):

* `(pos, (c, x))` / `(neg, (c, x))`: a positive/negative occurrence of the
  variable `x` in the clause `c`; two occurrence vertices are adjacent iff
  both are genuine, they belong to *distinct* clauses, and they are not
  conflicting – the same variable with opposite signs
  (`DescriptiveComplexity.SatToClique.Compat`);
* `(cl, (c, c))`: one *marked* vertex per clause, isolated in the graph, so
  that the cardinality of the marked set is the number of clauses.

A clique at least as large as the marked set must pick one occurrence per
clause, pairwise non-conflicting, which is exactly a satisfying assignment;
conversely, choosing a true literal in each clause under a satisfying
assignment yields such a clique. Empty clauses – which make the CNF
unsatisfiable but carry no occurrence vertex – are handled by a spoiler in
the mark formula: if some clause is empty, *every* vertex is marked, and no
clique can be as large as the whole universe since clause vertices are
isolated.

The formulas do not mention the order. The reduction is nevertheless packaged
as an ordered one because `DescriptiveComplexity.Clique` folds finiteness of the
universe into its yes-instances, so correctness can only hold on finite
structures – exactly the correctness contract of
`DescriptiveComplexity.OrderedFOReduction` (a plain `FOReduction` would have to be
correct on infinite structures as well, where SAT can hold while no clique
instance is a yes-instance).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-- Tags of the clique instance interpreted in a CNF structure. -/
inductive SatCliqueTag : Type
  /-- Positive-occurrence vertex, at pairs `(c, x)`. -/
  | pos
  /-- Negative-occurrence vertex, at pairs `(c, x)`. -/
  | neg
  /-- Marked clause vertex, at diagonal pairs `(c, c)`. -/
  | cl
  deriving DecidableEq, Nonempty

instance : Fintype SatCliqueTag where
  elems := {.pos, .neg, .cl}
  complete x := by cases x <;> decide

/-- The occurrence tag of a sign. -/
def SatCliqueTag.ofSign : Bool → SatCliqueTag
  | true => .pos
  | false => .neg

namespace SatToClique

/-! ### The semantic side -/

section Semantics

end Semantics

/-! ### The formulas and the interpretation -/

/-! ### Characterizations of the interpreted relations -/

section Characterization

end Characterization

/-! ### Correctness -/

section Correctness

end Correctness

end SatToClique

end Lax280166Proofs.DescriptiveComplexity


