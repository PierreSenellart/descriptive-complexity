/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.FirstOrderDefinable
import Lax945089Proofs.DescriptiveComplexity.SecondOrderPull
import Lax945089Proofs.DescriptiveComplexity.OrderedComposition
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax945089.OrderFreeFirstOrder
end Lax945089.OrderFreeFirstOrder

namespace Lax945089Proofs.DescriptiveComplexity.FODefinable
end Lax945089Proofs.DescriptiveComplexity.FODefinable

namespace Lax945089Proofs.DescriptiveComplexity.FODefinableFree
end Lax945089Proofs.DescriptiveComplexity.FODefinableFree

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.OrderFreeFirstOrder (FODefinableFree)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.FirstOrderDefinability (FODefinable)
end Lax945089Proofs.DescriptiveComplexity

/-!
# First-order definability travels backward along reductions

The bottom of the ladder is closed under reductions, exactly as every class
above it is: pull the defining sentence of the target back through the
interpretation (`DescriptiveComplexity.FOInterpretation.pullSentence`) and it
defines the source. For the order-invariant notion the interpretation is first
extended with the lexicographic order of its tagged tuples
(`DescriptiveComplexity.FOInterpretation.ordExtend`), so that the pulled
sentence may mention the order the target's sentence mentions.

The point of these lemmas is their **contrapositive**
(`DescriptiveComplexity.not_le_of_not_foDefinable` and its order-free twin): a
problem that is not first-order definable reduces to no problem that is. This
is what turns an inexpressibility result into a *non-reducibility* result, and
so the only route this library has to a negative statement about the reduction
order – everything else it proves is the existence of a reduction. It is
applied to `DescriptiveComplexity.EVEN`
(`DescriptiveComplexity.even_not_foDefinable`), whence
`DescriptiveComplexity.even_not_le_of_foDefinable`.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

/-! ### Closure under reductions -/

/-- **Order-invariant first-order definability travels backward along ordered
FO reductions**. The interpretation is extended with the lexicographic order on
its tagged tuples, so the pulled sentence can still read an order; the
extension is definable from the order of the input, which is what keeps the
result inside FO(≤). -/
theorem FODefinable.of_orderedReduction (h : Lax485149.FirstOrderDefinability.FODefinable Q) (f : P ≤ᶠᵒ[≤] Q) :
    Lax485149.FirstOrderDefinability.FODefinable P := by
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  obtain ⟨φ, hφ⟩ := h
  refine ⟨f.toInterpretation.ordExtend.pullSentence φ, fun A _ _ _ _ => ?_⟩
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  rw [f.toInterpretation.ordExtend.realize_pullSentence φ A,
    StrongHomClass.realize_sentence (f.toInterpretation.ordExtendLEquiv A) φ]
  exact (f.correct A).trans (hφ _)

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.FirstOrderDefinability.FODefinable

export Lax945089Proofs.DescriptiveComplexity.FODefinable (of_orderedReduction)

end Lax485149.FirstOrderDefinability.FODefinable

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

/-- Order-invariant definability travels backward along plain FO reductions
too, a plain reduction being an ordered one. -/
theorem FODefinable.of_foReduction (h : Lax485149.FirstOrderDefinability.FODefinable Q) (f : P ≤ᶠᵒ Q) : Lax485149.FirstOrderDefinability.FODefinable P :=
  h.of_orderedReduction f.toOrdered

end Lax945089Proofs.DescriptiveComplexity

namespace Lax485149.FirstOrderDefinability.FODefinable

export Lax945089Proofs.DescriptiveComplexity.FODefinable (of_foReduction)

end Lax485149.FirstOrderDefinability.FODefinable

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

variable {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

/-! ### Non-reducibility -/

/-- **A problem that is not FO(≤)-definable reduces to no problem that is.**
The contrapositive of `DescriptiveComplexity.FODefinable.of_orderedReduction`,
and the shape in which an inexpressibility result becomes a statement about the
reduction order. -/
theorem not_le_of_not_foDefinable (hP : ¬Lax485149.FirstOrderDefinability.FODefinable P) (hQ : Lax485149.FirstOrderDefinability.FODefinable Q) :
    IsEmpty (P ≤ᶠᵒ[≤] Q) :=
  ⟨fun f => hP (hQ.of_orderedReduction f)⟩

end Lax945089Proofs.DescriptiveComplexity


