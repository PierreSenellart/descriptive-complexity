/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.Ordered
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

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax485149.FirstOrderDefinability (FODefinable)
end Lax895169Proofs.DescriptiveComplexity

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

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax895169Proofs.DescriptiveComplexity


