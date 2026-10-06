/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Membership
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Hardness
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Junk
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

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625Proofs.DescriptiveComplexity.DigitDefinable
end Lax366625Proofs.DescriptiveComplexity.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (DigitDefinable)
end Lax366625Proofs.DescriptiveComplexity

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

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **A digit-definable problem is in FP**: it reduces to the number written
by a circuit, which is. -/
theorem DigitDefinable.mem_FP {C : Lax366625.CountingProblems.CountingProblem L} (h : Lax366625.QuantitativeLogic.DigitDefinable C) : C ∈ FP := by
  obtain ⟨f⟩ := h.nonempty_orderedParsimonious
  exact FP.mem_of_orderedParsimonious f circuitNumber_mem_FP

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.DigitDefinable

export Lax366625Proofs.DescriptiveComplexity.DigitDefinable (mem_FP)

end Lax366625.QuantitativeLogic.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The digit-definable problems are those of FP.** -/
theorem digitDefinable_iff_mem_FP (C : Lax366625.CountingProblems.CountingProblem L) : Lax366625.QuantitativeLogic.DigitDefinable C ↔ C ∈ FP :=
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
    {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'} (f : C ≤ʳᵖ[≤] D) (h : D ∈ FP) :
    C ∈ FP := by
  obtain ⟨g⟩ := (FPDefinable.digitDefinable h).nonempty_orderedParsimonious
  exact FP.mem_of_orderedParsimonious (f.trans g.toRel).unrelCircuitNumber
    circuitNumber_mem_FP

end Lax366625Proofs.DescriptiveComplexity


