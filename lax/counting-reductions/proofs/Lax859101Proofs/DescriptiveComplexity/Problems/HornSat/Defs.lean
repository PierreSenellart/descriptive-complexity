/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
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

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax859101.CountingRestrictedSat
end Lax859101.CountingRestrictedSat

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax859101Proofs.DescriptiveComplexity
export Lax859101.CountingRestrictedSat (AtMostOnePositive)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Sat (Satisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax535992.HornSat (HornSatisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satPosIn)
end FirstOrder.Language

/-!
# HORN-SAT: definition

The problem HORN-SAT, over the same vocabulary `FirstOrder.Language.sat` as SAT:
a CNF structure is a yes-instance iff every clause contains at most one
positive literal (`DescriptiveComplexity.AtMostOnePositive`) *and* the CNF is
satisfiable (`DescriptiveComplexity.HornSatisfiable`, bundled as
`DescriptiveComplexity.HORNSAT`).

Folding the Horn condition into the yes-instances rather than into the
vocabulary is the same choice as for 3SAT and its width bound
(`DescriptiveComplexity.WidthAtMostThree`): it keeps HORN-SAT a decision problem on
arbitrary `Language.sat`-structures, so that it lives in the same catalog and
composes with the same reductions.

Horn formulas are the tractable case of propositional satisfiability – a
satisfiable Horn formula has a *least* model, computed by unit propagation in
linear time ([Dowling & Gallier 1984][dowling1984linear]) – and HORN-SAT is the
canonical complete problem for polynomial time. The corresponding hardness
statement, machine-free and one level below the Cook–Levin discharge, is in
`DescriptiveComplexity.Problems.HornSat.Hardness`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [Lax904597.Sat.sat.Structure A]

end HornSat

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

end Iso

end Lax859101Proofs.DescriptiveComplexity


