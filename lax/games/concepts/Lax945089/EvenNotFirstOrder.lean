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
title: EVEN is not first-order definable, even with an order
type: theorem
---
EVEN is not order-free first-order definable, bare sets of different
parities being equivalent for any number of rounds once they are large
enough; and it is not FO($\le$) definable either, by Ehrenfeucht's theorem
on linear orders. An order-free definition is in particular an ordered
one.
-/

namespace Lax945089.EvenNotFirstOrder

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

/-- Every order-free first-order definable problem is FO(≤) definable. -/
axiom foDefinableFree_foDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  FODefinableFree P → FODefinable P

/-- EVEN is not order-free first-order definable. -/
axiom even_not_foDefinableFree : ¬FODefinableFree EVEN

/-- EVEN is not FO(≤) definable. -/
axiom even_not_foDefinable : ¬FODefinable EVEN

end Lax945089.EvenNotFirstOrder
