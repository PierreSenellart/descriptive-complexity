import Mathlib.ModelTheory.Order
import Mathlib.Order.Defs.LinearOrder
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax485149.Problems
import Lax485149.FirstOrderDefinability
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.InflationaryFixedPoint
import Lax535992.ClassPTIME
import Lax134656.PartialFixedPoint
import Lax895169.ArithmeticLogic
import Lax945089.OrderFreeFirstOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.PebbleGames
import Lax945089.Even
import Lax945089.Parity
import Lax945089.TransitiveClosureReductions

/-!
---
title: First-order reductions are strictly weaker than logarithmic-space reductions
type: theorem
---
There is a problem $Q$ to which EVEN reduces by an FO(DTC) reduction but by
no ordered first-order reduction. The first-order reductions under which
the complete problems of these submissions are complete are therefore
strictly weaker than deterministic logarithmic-space reductions, in their
logical form.
-/

namespace Lax945089.ReductionsBelowLogSpace

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes
open Lax485149.Problems Lax485149.FirstOrderDefinability Lax485149.TransitiveClosure
open Lax485149.DeterministicTransitiveClosure Lax485149.ClassNL Lax485149.ClassL
open Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax134656.PartialFixedPoint Lax895169.ArithmeticLogic
open Lax945089.OrderFreeFirstOrder Lax945089.EhrenfeuchtGames Lax945089.PebbleGames
open Lax945089.Even Lax945089.Parity
open Lax945089.TransitiveClosureReductions

/-- Some problem receives EVEN by an FO(DTC) reduction and by no ordered
first-order reduction. -/
axiom exists_dtcReduction_not_orderedReduction :
  ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (Q : DecisionProblem L),
  Nonempty (DTCReduction EVEN Q) ∧ IsEmpty (OrderedFOReduction EVEN Q)

end Lax945089.ReductionsBelowLogSpace
