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
title: No order-free induction defines a linear order
type: theorem
---
On a bare set with at least as many elements as its variable budget, no
binary relation defined by an order-free inflationary induction is a linear
order: a transposition of the universe preserves every stage of the
induction, so the relation is symmetric. The order that the logics of
polynomial time are given cannot be built by an isomorphism-invariant
induction.
-/

namespace Lax945089.NoDefinableOrder

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

/-- No binary variable of an order-free inflationary limit is a linear order on a
large enough bare set. -/
axiom not_isLinearOrder_inflLimit :
  ∀ {k : ℕ} (d : StepDef Language.empty) {i : d.B.ι}, StepDef.VarBound d k →
  ∀ (harity : d.B.arity i = 2) (A : Type) [Language.empty.Structure A] [Finite A], k ≤ Nat.card A →
    ¬IsLinearOrder A fun x y => d.inflLimit A i fun p => ![x, y] (Fin.cast harity p)

end Lax945089.NoDefinableOrder
