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
title: AC⁰ ⊆ PTIME, by fixed points
type: theorem
---
Every AC⁰ definable problem is FO($\le$, IFP) definable and FO(LFP)
definable, hence in PTIME. The numeric predicates are themselves an
induction: one simultaneous induction on two ternary relation variables
defines addition by walking two arguments down the order in lockstep and
multiplication by repeated addition, and the AC⁰ sentence is its output
sentence. This gives the inclusion directly, without going through
logarithmic space.
-/

namespace Lax895169.ACZeroInPTIME

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every AC⁰ definable problem is FO(≤, IFP) definable. -/
axiom ac0Definable_ifpDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → IFPDefinable P

/-- Every AC⁰ definable problem is FO(LFP) definable. -/
axiom ac0Definable_lfpDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → LFPDefinable P

/-- Every AC⁰ definable problem is in PTIME. -/
axiom ac0Definable_mem_PTIME : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → PTIME.Mem P

end Lax895169.ACZeroInPTIME
