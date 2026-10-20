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
title: Ehrenfeucht’s theorem on linear orders
type: theorem
---
Two finite linear orders with at least $2^n$ elements each are $n$-round
equivalent, as structures over the vocabulary of the order. The duplicator
maintains that the distances between pebbled points, the two ends of the
order included, are equal up to truncation at a threshold that halves at
each round.
-/

namespace Lax945089.GamesOnLinearOrders

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

/-- Two linear orders with at least `2 ^ n` elements are `n`-round equivalent. -/
axiom efEquiv_linearOrder :
  ∀ {A B : Type} [Language.empty.Structure A] [Language.empty.Structure B] [LinearOrder A]
    [LinearOrder B]
  [Finite A] [Finite B] (n : ℕ), 2 ^ n ≤ Nat.card A → 2 ^ n ≤ Nat.card B →
    EFEquiv (Language.empty.sum Language.order) A B n

end Lax945089.GamesOnLinearOrders
