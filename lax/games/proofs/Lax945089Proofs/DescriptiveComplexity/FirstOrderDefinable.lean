/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Ordered
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
# Plain first-order definability of a decision problem

The bottom of every ladder in this library: a problem is first-order definable
when a single sentence decides it on finite structures. The two variants are
the usual ones, and are named as everywhere else here –
`DescriptiveComplexity.FODefinableFree` is the order-free notion,
`DescriptiveComplexity.FODefinable` the order-invariant one, whose sentence
may mention a linear order on the universe but whose truth value may not
depend on which one.

Nothing is *proved* first-order definable by these notions – they exist to be
*refuted*. Every logic of this library extends first-order logic, so a problem
shown here to escape it (`DescriptiveComplexity.EVEN`, in
`DescriptiveComplexity.Problems.Even`) separates first-order logic from all of
them unconditionally, with no complexity-theoretic assumption. The refutations
themselves are Ehrenfeucht–Fraïssé arguments
(`DescriptiveComplexity.Games.Ehrenfeucht`).
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Order-free first-order definability only depends on the finite instances
of a problem. -/
theorem foDefinableFree_congr {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax945089.OrderFreeFirstOrder.FODefinableFree P ↔ Lax945089.OrderFreeFirstOrder.FODefinableFree Q := by
  constructor <;> rintro ⟨φ, hφ⟩ <;> refine ⟨φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- FO(≤) definability only depends on the finite instances of a problem. -/
theorem foDefinable_congr {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax485149.FirstOrderDefinability.FODefinable P ↔ Lax485149.FirstOrderDefinability.FODefinable Q := by
  constructor <;> rintro ⟨φ, hφ⟩ <;> refine ⟨φ, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-- An order-free first-order definition is in particular an order-invariant
one: the order symbol is simply not used. -/
theorem FODefinableFree.foDefinable {P : Lax904597.Problems.DecisionProblem L} (h : Lax945089.OrderFreeFirstOrder.FODefinableFree P) :
    Lax485149.FirstOrderDefinability.FODefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(LHom.sumInl : L →ᴸ L.sum Language.order).onSentence φ, ?_⟩
  intro A _ _ _ _
  let := orderStructure (M := A)
  rw [hφ A]
  exact (LHom.realize_onSentence A LHom.sumInl φ).symm

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.OrderFreeFirstOrder.FODefinableFree

export Lax945089Proofs.DescriptiveComplexity.FODefinableFree (foDefinable)

end Lax945089.OrderFreeFirstOrder.FODefinableFree

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax945089Proofs.DescriptiveComplexity


