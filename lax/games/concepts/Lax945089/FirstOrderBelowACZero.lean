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
title: FO(≤) ⊊ AC⁰: EVEN with arithmetic
type: theorem
---
EVEN is AC⁰ definable: with the arithmetic of the order, the greatest
element has rank one less than the size of the universe, and a sentence
states its parity. Since EVEN is not FO($\le$) definable, the inclusion of
FO($\le$) in AC⁰ is strict. This is the parity of the size of the input;
the parity of a marked subset is PARITY, about which no bound is claimed
here.
-/

namespace Lax945089.FirstOrderBelowACZero

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

/-- EVEN is AC⁰ definable. -/
axiom even_ac0Definable : AC0Definable EVEN

/-- Some AC⁰ definable problem is not FO(≤) definable. -/
axiom exists_ac0Definable_not_foDefinable :
  ∃ P : DecisionProblem Language.empty, AC0Definable P ∧ ¬FODefinable P

end Lax945089.FirstOrderBelowACZero
