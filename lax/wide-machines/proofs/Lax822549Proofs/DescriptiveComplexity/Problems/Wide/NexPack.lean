/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawPack
import Lax822549Proofs.DescriptiveComplexity.Exponential.Kernel
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# A kernel, packed as the data of a wide program

The source side of the NEXPTIME reduction, in the record the machine layer is
already written against. A `DescriptiveComplexity.NexKernel` is an expansion, a
block of relation variables to guess and a first-order sentence to check of the
guess; a `DescriptiveComplexity.Draw.Data` is an expansion, a
`DescriptiveComplexity.StepDef` – a block, a step formula per variable, an
output sentence – and the packs and layout the program computes with.

**The kernel is a step definition whose steps are never read.** Put the guessed
block where the fixed-point variables go and the kernel where the output
sentence goes, and the two records are the same record: the tracks a symbol
carries are indexed by the block either way, the atoms of the sentence classify
by `DescriptiveComplexity.Draw.MatAtom` – which reads a *block*, not an
iteration – and `DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` is already
what the output evaluation of a fixed-point program computes. So the whole
address, control and evaluation layer above `Draw.Data` serves a nondeterministic
program with nothing added, and what is new is the program alone: it guesses the
tracks the iteration would have written, then runs the output evaluation once.

The step formulas of a packed kernel are `⊥`, and the only trace they leave is
in the *sizes*: the derived dimensions of
`DescriptiveComplexity.Draw.Data` are maxima over the variables, so each of
them is the kernel's own value or the (vacuous) demand of an unread step,
whichever is larger. A larger inventory costs a wider control and nothing else.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **A kernel as a step definition**: the guessed block, the kernel as the
output sentence, and step formulas that no nondeterministic program reads. -/
def NexKernel.toStepDef (K : NexKernel L) : Lax535992.InflationaryFixedPoint.StepDef (K.X.E.sum Language.order) where
  B := K.B
  step _ := ⊥
  out := K.ker

@[simp]
theorem NexKernel.toStepDef_B (K : NexKernel L) : K.toStepDef.B = K.B := rfl

@[simp]
theorem NexKernel.toStepDef_out (K : NexKernel L) : K.toStepDef.out = K.ker := rfl

namespace Draw

/-! ### What a nondeterministic program has to decide

The evaluation the machine performs, stated where it can be read off the record:
the guess of an assignment of the block for which the **gated alternating
prefix** of the output sentence's matrix holds. A fixed-point program computes
one such prefix per stage and one for its output; a nondeterministic one
computes only the second, over tracks it guessed rather than iterated, so the
statement below is `DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` under an
existential and nothing else. -/

section Eval

end Eval

end Draw

end Lax822549Proofs.DescriptiveComplexity


