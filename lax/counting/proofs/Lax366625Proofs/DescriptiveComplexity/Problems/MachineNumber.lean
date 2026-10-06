/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.MachineNumber.Membership
import Lax366625Proofs.DescriptiveComplexity.Problems.MachineNumber.Hardness
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.NumberHardness
import Lax366625Proofs.DescriptiveComplexity.Counting.Digits.NormalForm
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

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

/-!
# The number written by a machine is complete for FP

The machine bridge for FP, the class of the functions computable in
polynomial time (`DescriptiveComplexity.FP`), which the library defines by a
logic: `DescriptiveComplexity.DTMNumber` – the number a deterministic machine,
carried by the instance, leaves on its marked output cells, read in tape
order, when it halts and accepts within its clock – is complete for FP under parsimonious reductions
(`DescriptiveComplexity.dtmNumber_FP_parsimoniousComplete`). Hence the machine
characterization of the class
(`DescriptiveComplexity.mem_FP_iff_le_dtmNumber`): a function is in FP exactly
when it parsimoniously reduces to the number written by a machine. This is
the analogue, for functions, of
`DescriptiveComplexity.dtmAccept_PTIME_complete` and
`DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`.

## The proof

* **Membership** (`DescriptiveComplexity.dtmNumber_mem_FP`): the run of a
  deterministic machine is a least fixed point, and the number is one
  quantitative term over it.
* **Hardness**, in three steps:
  - every problem of FP has its binary digits defined by a least fixed point
    (`DescriptiveComplexity.FPDefinable.digitDefinable`);
  - the least fixed point of a system of rules is the least model of a Horn
    formula, so such a problem reduces to
    `DescriptiveComplexity.HornNumber`, the number written by unit propagation
    (`DescriptiveComplexity.DigitLFPDef.orderedParsimoniousHorn`);
  - the unit-propagation machine of the PTIME bridge leaves the least model on
    its tape
    (`DescriptiveComplexity.MachNum.hornNumber_ordered_parsimonious_dtmNumber`).

The intermediate problem is complete for FP as well
(`DescriptiveComplexity.hornNumber_FP_parsimoniousComplete`): the function
counterpart of HORN-SAT.

## The output convention

The output cells are marked in the instance, as are the symbols read as the
digit `1`, and the digits are read **in tape order**: the first output cell
holds the least significant digit. The reduction from the number written by
unit propagation, whose output variables are compared by a relation of the
instance, is where the two conventions meet: the reduction first reorders its
input so that the output variables come first, in the order of significance
(`DescriptiveComplexity.FOInterpretation.reorder`), and the machine then lays
its cells out in that order.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- **The number written by unit propagation is in FP**: it reduces to the
number written by a machine. -/
theorem hornNumber_mem_FP : HornNumber ∈ FP :=
  FP.mem_of_orderedParsimonious MachNum.hornNumber_ordered_parsimonious_dtmNumber
    dtmNumber_mem_FP

/-- **The number written by unit propagation is hard for FP under parsimonious
reductions.** -/
theorem hornNumber_FP_parsimoniousHard : FP.ParsimoniousHard HornNumber :=
  fun _ hD => ⟨(FPDefinable.digitDefinable hD).nonempty_orderedParsimoniousHorn.some.toRel⟩

/-- **The number written by unit propagation is complete for FP under
parsimonious reductions.** -/
theorem hornNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete HornNumber :=
  ⟨hornNumber_mem_FP, hornNumber_FP_parsimoniousHard⟩

/-- **The number written by a deterministic machine is hard for FP under
parsimonious reductions.** -/
theorem dtmNumber_FP_parsimoniousHard : FP.ParsimoniousHard DTMNumber :=
  FP.parsimoniousHard_of_orderedParsimonious
    MachNum.hornNumber_ordered_parsimonious_dtmNumber hornNumber_FP_parsimoniousHard

/-- **The number written by a deterministic machine is complete for FP under
parsimonious reductions**: the library's FP, defined by a logic, is the
machine one. -/
theorem dtmNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete DTMNumber :=
  ⟨dtmNumber_mem_FP, dtmNumber_FP_parsimoniousHard⟩

/-- **The machine characterization of FP**: a counting problem is in FP exactly
when it reduces, by an ordered parsimonious reduction, to the number written
by a deterministic machine. -/
theorem mem_FP_iff_le_dtmNumber {L : Language.{0, 0}} [L.IsRelational]
    (C : Lax366625.CountingProblems.CountingProblem L) : C ∈ FP ↔ Nonempty (C ≤ᵖ[≤] DTMNumber) :=
  ⟨fun h => ⟨(FPDefinable.digitDefinable h).nonempty_orderedParsimoniousHorn.some.trans
      MachNum.hornNumber_ordered_parsimonious_dtmNumber⟩,
    fun ⟨f⟩ => FP.mem_of_orderedParsimonious f dtmNumber_mem_FP⟩

end Lax366625Proofs.DescriptiveComplexity


