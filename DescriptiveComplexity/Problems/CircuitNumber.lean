/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CircuitNumber.Membership
import DescriptiveComplexity.Problems.CircuitNumber.Hardness
import DescriptiveComplexity.Problems.CircuitNumber.Junk
import DescriptiveComplexity.Counting.Digits.NormalForm

/-!
# The number written by a circuit is complete for FP

`DescriptiveComplexity.CircuitNumber`: given a Boolean circuit with several
output gates and a comparison of them, compute the number whose binary digits
are the values of the outputs. It is the function counterpart of the circuit
value problem (`DescriptiveComplexity.CVP`), and plays for FP, under
parsimonious reductions, the part `CVP` plays for PTIME:
`DescriptiveComplexity.circuitNumber_FP_parsimoniousComplete`.

## The proof

* **Membership**: `DescriptiveComplexity.circuitNumber_mem_FP`. The fixed
  point is the evaluation of the gates, and the output is one quantitative
  term, `Σg. [g holds the digit 1] · Πh. ([h is an output below g] + 1)`.
* **Hardness for the functions given by their digits**:
  `DescriptiveComplexity.DigitDefinable.nonempty_orderedParsimonious`. A
  function whose binary digits are relations of a least fixed point
  (`DescriptiveComplexity.DigitDefinable`) reduces to the problem by an ordered
  parsimonious reduction: the rules are drawn as a monotone circuit, one
  disjunction gate per atom and one conjunction chain per rule instance
  (`DescriptiveComplexity.CircNum.drawInterp`).
* **The normal form**: `DescriptiveComplexity.FPDefinable.digitDefinable`.
  Every problem of FP – a quantitative term, with sums and products over the
  universe, read at a least fixed point – has its binary digits defined by a
  least fixed point. This is where the work is: the digits of iterated sums and
  products are computed by a tower of inflationary inductions
  (`DescriptiveComplexity.Counting.Digits`).

So the digit-definable problems are exactly those of FP
(`DescriptiveComplexity.digitDefinable_iff_mem_FP`): the normal form in the
proof that QFO(LFP) captures FP
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4), here a
theorem about the logic with no machine in it.

## Relativized reductions

FP is closed under *relativized* parsimonious reductions as well
(`DescriptiveComplexity.mem_FP_of_relOrderedParsimonious`), those whose target
universe is a definable set of tagged tuples. No pullback of a quantitative
term through such a reduction is needed: the reduction is composed down to
this problem, which ignores isolated elements
(`DescriptiveComplexity.circuitNumber_of_embedding`), so that the tuples
outside the domain can be kept.

## Attribution

The statement that this problem is complete for FP under first-order
parsimonious reductions was not found in the literature. Under polynomial-time
reductions every function of FP is complete for it, so the question only
arises for reductions this weak; the proof combines the normal form of
Arenas, Muñoz and Riveros with the classical completeness of circuit value
for PTIME.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **A digit-definable problem is in FP**: it reduces to the number written
by a circuit, which is. -/
theorem DigitDefinable.mem_FP {C : CountingProblem L} (h : DigitDefinable C) : C ∈ FP := by
  obtain ⟨f⟩ := h.nonempty_orderedParsimonious
  exact FP.mem_of_orderedParsimonious f circuitNumber_mem_FP

/-- **The digit-definable problems are those of FP.** -/
theorem digitDefinable_iff_mem_FP (C : CountingProblem L) : DigitDefinable C ↔ C ∈ FP :=
  ⟨DigitDefinable.mem_FP, fun h => FPDefinable.digitDefinable h⟩

/-- **The number written by a circuit is hard for FP under parsimonious
reductions.** -/
theorem circuitNumber_FP_parsimoniousHard : FP.ParsimoniousHard CircuitNumber :=
  fun _ hD => ⟨(FPDefinable.digitDefinable hD).nonempty_orderedParsimonious.some.toRel⟩

/-- **The number written by a circuit is complete for FP under parsimonious
reductions.** -/
theorem circuitNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete CircuitNumber :=
  ⟨circuitNumber_mem_FP, circuitNumber_FP_parsimoniousHard⟩

/-- **FP is closed under relativized ordered parsimonious reductions.** -/
theorem mem_FP_of_relOrderedParsimonious {L' : Language.{0, 0}} [L'.IsRelational]
    {C : CountingProblem L} {D : CountingProblem L'} (f : C ≤ʳᵖ[≤] D) (h : D ∈ FP) :
    C ∈ FP := by
  obtain ⟨g⟩ := (FPDefinable.digitDefinable h).nonempty_orderedParsimonious
  exact FP.mem_of_orderedParsimonious (f.trans g.toRel).unrelCircuitNumber
    circuitNumber_mem_FP

end DescriptiveComplexity
