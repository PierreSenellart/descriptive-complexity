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
title: AC⁰ ⊆ L
type: theorem
---
Every AC⁰ definable problem is FO(DTC) definable, hence in L and in NL. The
sentence is evaluated by a deterministic multihead automaton whose number of
heads is the quantifier depth plus a constant; addition and multiplication
of ranks are not relations of the instance, so they are computed by walking
heads along the order.
-/

namespace Lax895169.ACZeroInLogSpace

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every AC⁰ definable problem is FO(DTC) definable. -/
axiom ac0Definable_dtcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → DTCDefinable P

/-- Every AC⁰ definable problem is in L. -/
axiom ac0Definable_mem_LOGSPACE : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → LOGSPACE.Mem P

/-- Every AC⁰ definable problem is in NL. -/
axiom ac0Definable_mem_NL : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → NL.Mem P

end Lax895169.ACZeroInLogSpace
