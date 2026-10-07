/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import Lax794877Proofs.DescriptiveComplexity.Counting.Class
import Lax794877Proofs.DescriptiveComplexity.FixedPointStep
import Lax794877Proofs.DescriptiveComplexity.OrderedComposition
import Lax794877Proofs.DescriptiveComplexity.RelComposition
import Lax794877Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax794877Proofs.DescriptiveComplexity.SecondOrderLift
import Lax794877Proofs.DescriptiveComplexity.SecondOrderPull
import Lax794877Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax794877Proofs.DescriptiveComplexity.FOInterpretation
end Lax794877Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.ParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.ParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction
end Lax794877Proofs.DescriptiveComplexity.RelOrderedParsimoniousReduction

namespace Lax794877Proofs.DescriptiveComplexity.SharpPDefinable
end Lax794877Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax794877Proofs.DescriptiveComplexity.StrongSubtractiveReduction
end Lax794877Proofs.DescriptiveComplexity.StrongSubtractiveReduction

namespace Lax794877Proofs.DescriptiveComplexity.SubtractiveReducible
end Lax794877Proofs.DescriptiveComplexity.SubtractiveReducible

namespace Lax859101.SubtractiveReductions
end Lax859101.SubtractiveReductions

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation sumOrderStructure)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable witnessCount)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax859101.SubtractiveReductions (StrongSubtractiveReduction SubtractiveReducible)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation
export Lax859101.SubtractiveReductions.FOInterpretation (WitAt ordExtend)
end Lax904597.Interpretations.FOInterpretation

/-!
# Subtractive reductions

The reductions of [Durand, Hermann, Kolaitis 2005][durand2005subtractive],
which sit between the parsimonious reductions and the one-call reductions of
`DescriptiveComplexity.Counting.Reduction`, and under which `#P` is closed.

A **strong subtractive reduction** from `C` to `D`
(`DescriptiveComplexity.StrongSubtractiveReduction`) draws two instances of
`D`, the *subtrahend* and the *minuend*, such that the solutions of the first
are among those of the second and

`C A = D (minuend A) - D (subtrahend A)`.

The condition on solutions is what keeps the difference inside `#P`, and it is
about solutions, not counts. So `D` comes with a *presentation*: a second-order
block and a first-order kernel whose witnesses it counts
(`DescriptiveComplexity.StrongSubtractiveReduction.present`), which plays the
part of the relation `B` in the paper's `#·B`. The two interpretations share
their tags and their dimension, so the two instances have the same universe,
ordered the same way, and a witness of one can be compared with a witness of
the other (`DescriptiveComplexity.FOInterpretation.WitAt`).

Strong subtractive reductions do not compose, and a **subtractive reduction**
`C ≤ˢ D` (`DescriptiveComplexity.SubtractiveReducible`) is a finite chain of
steps, as in the paper. Two departures from it, both forced:

* a step is a strong subtractive reduction *or a parsimonious reduction*, in
  its most general form, relativized and ordered. The paper obtains the second
  as the special case of the first whose subtrahend has no solution, which
  needs the target to have such an instance, definably; admitting the step
  directly asks for nothing;
* the target of a strong step is presented by a first-order kernel, hence is
  itself in `#P`. The paper's relations are arbitrary, which is what lets it
  speak of the classes above `#P`; the library has no such classes yet.

`#P` is closed under subtractive reductions
(`DescriptiveComplexity.SharpPDefinable.of_subtractive`, Theorem 3.3 of the
paper): the witnesses of the minuend that are not witnesses of the subtrahend
are the witnesses of one kernel, the conjunction of the pulled kernel of the
first with the negated pulled kernel of the second. So this is the widest
notion of the library under which the class is closed, and the plain words go
to it, as on the decision side they go to reductions the classes are closed
under: `DescriptiveComplexity.CountingClass.Hard` and
`DescriptiveComplexity.CountingClass.Complete` are hardness and completeness
under subtractive reductions. Parsimonious hardness and completeness imply
them (`DescriptiveComplexity.hard_sharpP_of_parsimoniousHard`,
`DescriptiveComplexity.complete_sharpP_of_parsimoniousComplete`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Witnesses at an interpreted instance -/

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

end WitAt

/-! ### Strong subtractive reductions -/

section Closure

end Closure

/-! ### Subtractive reductions -/

@[inherit_doc]
scoped notation:50 C:51 " ≤ˢ " D:51 => Lax859101.SubtractiveReductions.SubtractiveReducible C D

section Reducible

end Reducible

/-! ### Hardness and completeness -/

namespace CountingClass

end CountingClass

end Lax794877Proofs.DescriptiveComplexity


