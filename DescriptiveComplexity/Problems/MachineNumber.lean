/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MachineNumber.Membership
import DescriptiveComplexity.Problems.MachineNumber.Hardness
import DescriptiveComplexity.Problems.HornSat.NumberHardness
import DescriptiveComplexity.Counting.Digits.NormalForm

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

namespace DescriptiveComplexity

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
    (C : CountingProblem L) : C ∈ FP ↔ Nonempty (C ≤ᵖ[≤] DTMNumber) :=
  ⟨fun h => ⟨(FPDefinable.digitDefinable h).nonempty_orderedParsimoniousHorn.some.trans
      MachNum.hornNumber_ordered_parsimonious_dtmNumber⟩,
    fun ⟨f⟩ => FP.mem_of_orderedParsimonious f dtmNumber_mem_FP⟩

end DescriptiveComplexity
