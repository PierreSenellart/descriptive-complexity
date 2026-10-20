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
title: AC⁰ is the logarithmic-time hierarchy
type: theorem
---
A decision problem is AC⁰ definable if and only if it is decidable in
logarithmic time with constantly many alternations, and if and only if it
is bit-definable. A sentence of the bit-level logic is compiled into a
machine atom by atom, the order and the addition being decided by sweeps.
Conversely, a sweep carries a constant number of state bits past each of
the $\log n$ positions, so its whole history is a constant number of bit
vectors over the positions, each of which is an element of the universe:
the sentence guesses those elements and checks the transitions.
-/

namespace Lax895169.ACZeroIsLogTime

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every problem decidable in logarithmic time is bit-definable. -/
axiom ltDecidable_bitDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  LTDecidable P → BitDefinable P

/-- Every bit-definable problem is decidable in logarithmic time. -/
axiom bitDefinable_ltDecidable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  BitDefinable P → LTDecidable P

/-- AC⁰ definability is decidability in logarithmic time. -/
axiom ac0Definable_iff_ltDecidable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P ↔ LTDecidable P

end Lax895169.ACZeroIsLogTime
