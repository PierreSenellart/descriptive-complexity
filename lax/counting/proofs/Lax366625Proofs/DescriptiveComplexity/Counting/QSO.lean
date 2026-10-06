/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.KernelPair
import Lax366625Proofs.DescriptiveComplexity.SecondOrderMerge
import Mathlib.Algebra.BigOperators.Finprod
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

namespace Lax366625.SecondOrderCounting
end Lax366625.SecondOrderCounting

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.SecondOrderCounting (SQTerm)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

/-!
# ΣQSO(FO): quantitative second-order logic with second-order sums

The fragment ΣQSO(FO) of the quantitative second-order logic of
[Arenas, Muñoz, Riveros 2020][arenas2020descriptive]: above a Boolean layer
of first-order formulas, terms denoting natural numbers,

`α ::= φ | s | α + α | α · α | Σx. α | Πx. α | ΣX. α`,

the first-order quantitative terms of `DescriptiveComplexity.QTerm` together
with the **second-order sum** `ΣX. α`, the sum over the relations `X` of the
value of `α` in the structure expanded by `X`
(`DescriptiveComplexity.SQTerm`, `DescriptiveComplexity.SQTerm.eval`). The
second-order product `ΠX` of the full logic QSO is left out: ΣQSO(FO) is the
fragment that captures `#P` over ordered structures, which is
`DescriptiveComplexity.mem_sharpP_iff_sqDefinable`.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SQTerm

end SQTerm

end Lax366625Proofs.DescriptiveComplexity


