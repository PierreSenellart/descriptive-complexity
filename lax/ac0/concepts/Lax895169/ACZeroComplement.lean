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
title: AC⁰ is closed under complement
type: theorem
---
If a decision problem $P$ is AC⁰ definable, then so is its complement
$P^c$: it suffices to negate the defining sentence.
-/

namespace Lax895169.ACZeroComplement

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- The complement of an AC⁰ definable problem is AC⁰ definable. -/
axiom ac0Definable_compl : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → AC0Definable (DecisionProblem.compl P)

end Lax895169.ACZeroComplement
