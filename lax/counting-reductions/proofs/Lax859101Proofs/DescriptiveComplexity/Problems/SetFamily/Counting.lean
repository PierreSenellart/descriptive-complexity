/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Problems.SetFamily.Membership
import Lax859101Proofs.DescriptiveComplexity.Counting.Class
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem)
end FirstOrder.Language

/-!
# #ExactCover: counting exact covers

The counting version of `DescriptiveComplexity.ExactCover`: the number of subfamilies
of a set system covering every ground element exactly once
(`DescriptiveComplexity.ExactCoverBy`). A cover is a set of members of the family, so
nothing has to be said about the other elements of the instance.

`DescriptiveComplexity.SharpExactCover` is in `#P`
(`DescriptiveComplexity.sharpExactCover_mem_sharpP`); its parsimonious hardness is in
`DescriptiveComplexity.Problems.ExactCoverCounting`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- Subfamilies, as assignments of the guess block with an empty binary
relation. -/
def familyGuessOf {A : Type} (G : A → Prop) : familyGuessBlock.Assignment A :=
  fun i => match i with
    | .guess => fun w : Fin 1 → A => G (w 0)
    | .inj => fun _ : Fin 2 → A => False

end Lax859101Proofs.DescriptiveComplexity


