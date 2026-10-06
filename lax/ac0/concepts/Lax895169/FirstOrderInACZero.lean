import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Complement
import Lax485149.FirstOrderDefinability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.LeastFixedPoint
import Lax535992.InflationaryFixedPoint
import Lax535992.ClassPTIME
import Lax895169.BitPredicate
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.LogTimeMachines

/-!
---
title: FO(≤) ⊆ AC⁰
type: theorem
---
Every FO($\le$) definable problem is AC⁰ definable: a sentence over the
order is read over the arithmetic vocabulary, whose $\le$ is the order.
-/

namespace Lax895169.FirstOrderInACZero

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every FO(≤) definable problem is AC⁰ definable. -/
axiom foDefinable_ac0Definable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  FODefinable P → AC0Definable P

end Lax895169.FirstOrderInACZero
