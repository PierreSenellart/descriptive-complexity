/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.FixedPointInflationary
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

namespace Lax366625Proofs.DescriptiveComplexity.DecisionProblem
end Lax366625Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax366625Proofs.DescriptiveComplexity.StepDef
end Lax366625Proofs.DescriptiveComplexity.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Order relativization: moving the order between the instance and the vocabulary

The ordered fixed-point definability notions
(`DescriptiveComplexity.IFPDefinable`, `DescriptiveComplexity.PFPDefinable`)
quantify over every linear order on the universe of an `L`-structure; the
order-free notions over the *ordered expansion* `L.sum Language.order` instead
see the order as one more relation of the instance. This file proves the two
readings interchangeable, the bookkeeping the unordered Abiteboul–Vianu
theorem (`DescriptiveComplexity.AbiteboulVianu`) threads its right-to-left
direction through:

* `DescriptiveComplexity.DecisionProblem.withOrder` – the problem «the order
  symbol is a linear order, and `P` holds on the `L`-reduct», over
  `L.sum Language.order`;
* `DescriptiveComplexity.ifpDefinable_iff_ifpDefinableFree_withOrder` and
  `DescriptiveComplexity.pfpDefinable_iff_pfpDefinableFree_withOrder` – `P` is
  FO(≤, IFP) (resp. FO(≤, PFP)) definable exactly when `P.withOrder` is
  *order-free* FO(IFP) (resp. FO(PFP)) definable.

Left to right, the induction is reused as is and its output is guarded by the
first-order sentence «the order symbol is a linear order»
(`DescriptiveComplexity.leLinearS`, via
`DescriptiveComplexity.StepDef.guardOut`); on an instance whose order symbol
does satisfy the guard, the promoted order
(`DescriptiveComplexity.LeLinearOn.linearOrder`) rebuilds the ordered
instance, identical to the given one through the identity isomorphism
(`DescriptiveComplexity.relMapIffEquiv`). Right to left is immediate: an
ordered `L`-structure *is* an instance of the expansion whose order symbol is
a linear order (`DescriptiveComplexity.sumOrderStructure`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Identity isomorphisms between structures with the same relations -/

/-- An isomorphism over an expanded vocabulary is an isomorphism of the
reducts. -/
def reductSumInlEquiv {L' : Language.{0, 0}} {A B : Type}
    [instA : (L.sum L').Structure A] [instB : (L.sum L').Structure B]
    (e : A ≃[L.sum L'] B) :
    @Language.Equiv L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
      ((LHom.sumInl : L →ᴸ L.sum L').reduct B) :=
  @Language.Equiv.mk L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
    ((LHom.sumInl : L →ᴸ L.sum L').reduct B) e.toEquiv
    (fun {_} f x => e.map_fun' (Sum.inl f) x)
    (fun {_} r x => e.map_rel' (Sum.inl r) x)

/-! ### «The order symbol is a linear order» -/

section LeLinear

end LeLinear

/-! ### The problem, moved to the ordered expansion -/

section WithOrder

end WithOrder

/-! ### Guarding the output of an induction -/

namespace StepDef

end StepDef

/-! ### The transfer -/

section Transfer

end Transfer

/-! ### Order-free definability implies ordered definability -/

namespace StepDef

end StepDef

end Lax366625Proofs.DescriptiveComplexity


