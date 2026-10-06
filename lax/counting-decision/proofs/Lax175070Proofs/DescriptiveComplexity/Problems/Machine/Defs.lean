/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Machines
import Lax175070Proofs.DescriptiveComplexity.Interpretation
import Lax175070.CountDefinability
import Lax175070.SelectedSat
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Machines (TMAcc TMBlank TMData TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax175070Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing turingRel)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

/-!
# Machine acceptance as a decision problem

The vocabulary of the machine bridge, and the problem the bridge is about: a
nondeterministic Turing machine is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.NTMAccept`, an ordinary iso-invariant problem of the catalog.
The semantics it reads is `DescriptiveComplexity.TMData`, defined without a vocabulary
in `DescriptiveComplexity.Machines`.

## The vocabulary

`FirstOrder.Language.turing` carries, following design decision (a) of the
plan, **no relation of arity above two**: a transition is an *element* `τ` of
the universe with four binary attributes `tsrc`/`tread`/`tdst`/`twrite` and a
unary mark `right`, rather than a single 5-ary symbol. An
`FOInterpretation` supplies one defining formula per tuple of tags, so a 5-ary
symbol would mean `|Tag|⁵` formula cases; keeping every symbol binary keeps the
reductions of stages 3 and 4 in the regime the rest of the catalog lives in.

Positions are both tape cells and time steps (design decision (b)), so the
budget of `DescriptiveComplexity.TMData.Accepts` is unary by construction and no
arithmetic is needed anywhere.

## Well-formedness

Being a linear order is not automatic for a relation symbol, so – exactly as
`DescriptiveComplexity.IsLinOrd` for Knapsack, and `WidthAtMostThree` for 3SAT – it is
folded into the yes-instances, together with the other promises of
`DescriptiveComplexity.TMData.WellFormed`. All of them are first-order, so the `Σ₁`
kernel of the membership proof can check them.

## Why there are no state and symbol sorts

The vocabulary marks positions (`posn`) and transitions (`tr`) and nothing else.
Sorts of states and of symbols are omitted because nothing in the semantics or
in the membership proof reads them: a junk element is harmless as a state, since
it is reachable only through a transition, and a reduction controls which
elements it marks accepting. Should a construction want them, adding a unary
symbol is a local change to this file and to the well-formedness predicate.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax904597.Machines.turing.Structure A]

end Shorthands

/-! ### The problem -/

section Problem

end Problem

end Lax175070Proofs.DescriptiveComplexity


