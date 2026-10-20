import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems

/-!
---
title: First-order definability without an order
type: definition
---
A decision problem $P$ over a relational vocabulary $L$ is order-free
first-order definable when there is a first-order sentence $\varphi$ over
$L$ alone such that every nonempty finite $L$-structure is a yes-instance of
$P$ if and only if it satisfies $\varphi$. No order is available to the
sentence, in contrast with FO($\le$) definability.
-/

namespace Lax945089.OrderFreeFirstOrder

open Lax904597.Problems

open FirstOrder

open Language

/-- A decision problem is *order-free first-order definable* if a single
sentence over its own vocabulary decides it on nonempty finite structures. -/
def FODefinableFree {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : L.Sentence, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

end Lax945089.OrderFreeFirstOrder
