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
title: First-order logic cannot count: games on bare sets
type: theorem
---
Two finite sets with at least $n$ elements each, as structures over the
empty vocabulary, are $n$-round equivalent: the duplicator answers a new
element by a new element and an old one by its match. Hence an order-free
first-order definable property of bare sets is constant on the sets beyond
some size: first-order logic counts up to its quantifier depth and no
further.
-/

namespace Lax945089.GamesOnSets

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

/-- Two sets with at least `n` elements are `n`-round equivalent. -/
axiom efEquiv_bare :
  ∀ {M N : Type} [Language.empty.Structure M] [Language.empty.Structure N] [Finite M] [Finite N]
    (n : ℕ),
  n ≤ Nat.card M → n ≤ Nat.card N → EFEquiv Language.empty M N n

/-- An order-free first-order property of bare sets is eventually constant. -/
axiom exists_card_bound_of_foDefinableFree :
  ∀ {P : DecisionProblem Language.empty}, FODefinableFree P →
  ∃ N : ℕ, ∀ (A B : Type) [Language.empty.Structure A] [Language.empty.Structure B] [Finite A]
    [Finite B]
    [Nonempty A] [Nonempty B], N ≤ Nat.card A → N ≤ Nat.card B → (P A ↔ P B)

end Lax945089.GamesOnSets
