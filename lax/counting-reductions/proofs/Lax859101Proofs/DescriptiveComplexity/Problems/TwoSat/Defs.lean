/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat
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

namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax859101.CountingRestrictedSat
end Lax859101.CountingRestrictedSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax859101Proofs.DescriptiveComplexity
export Lax859101.CountingRestrictedSat (WidthAtMostTwo)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax485149.TwoSat (TwoSatisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax859101Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (OccIn)
end Lax859101Proofs.DescriptiveComplexity.SatOcc

/-!
# 2SAT: definition

The problem 2SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT and
3SAT: a CNF structure is a yes-instance iff every clause has at most two
literal occurrences (`DescriptiveComplexity.WidthAtMostTwo`) *and* the CNF is
satisfiable (`DescriptiveComplexity.TwoSatisfiable`, bundled as
`DescriptiveComplexity.TwoSAT`).

As for 3SAT, folding the width bound into the yes-instances rather than into
the vocabulary is what keeps 2SAT a decision problem on arbitrary
`Language.sat`-structures, and the bound “at most two” is expressed without
counting: among any three literal occurrences of a clause, two coincide.

Two facts about the bound are needed by the Krom program of
`DescriptiveComplexity.Problems.TwoSat.Membership`, and both are here: the bound is
first-order expressible over the ordered expansion
(`DescriptiveComplexity.wideTwoOrdF`, its violation), and a clause of a width-two
structure has *two signed occurrences covering all of them*
(`DescriptiveComplexity.exists_covering_pair`), the shape a 2-clause can talk about.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

section TwoSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end TwoSat

section Basic

end Basic

section Iso

end Iso

/-! ### The width bound as a formula

The Krom program defining 2SAT enforces the width bound by a *guard*: guards
are first-order over the input vocabulary, so the bound costs nothing beyond
one goal clause. The formula is the width-two analogue of
`DescriptiveComplexity.ThreeSatToSat.wideOrdF`. -/

section Formula

end Formula

end Lax859101Proofs.DescriptiveComplexity


