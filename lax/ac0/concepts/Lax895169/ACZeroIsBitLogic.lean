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
title: FO(≤, +, ×) = FO(≤, +, BIT)
type: theorem
---
A decision problem is AC⁰ definable, that is, definable in
FO($\le, +, \times$), if and only if it is bit-definable, that is,
definable by a prenex sentence of FO($\le, +$, BIT). One direction defines
the map $i \mapsto 2^i$ from addition and multiplication, by guessing a
doubling chain. The other defines multiplication from BIT, which rests on
the Bit Sum Lemma, counting the ones of a word of logarithmic length; the
product is then assembled from its columns with guessed carry chains. This
is the identification of the two vocabularies in Immerman's Descriptive
Complexity, Theorem 1.17.
-/

namespace Lax895169.ACZeroIsBitLogic

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes
open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every AC⁰ definable problem is bit-definable. -/
axiom ac0Definable_bitDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → BitDefinable P

/-- Every bit-definable problem is AC⁰ definable. -/
axiom bitDefinable_ac0Definable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  BitDefinable P → AC0Definable P

end Lax895169.ACZeroIsBitLogic
