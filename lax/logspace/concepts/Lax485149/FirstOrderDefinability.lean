import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax904597.Interpretations

/-!
---
title: First-order definability on ordered structures
type: definition
---
A decision problem $P$ over a relational vocabulary $L$ is FO($\le$)
definable when there is a first-order sentence $\varphi$ over
$L \cup \{\le\}$ such that, for every nonempty finite $L$-structure $A$
and every linear order on $A$, $A$ is a yes-instance of $P$ if and only if
$(A, \le) \models \varphi$. The sentence may use the order; the problem
does not depend on it.
-/

namespace Lax485149.FirstOrderDefinability

open Lax904597.Problems

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A decision problem is *FO(≤) definable* if a single sentence over the
ordered expansion of its vocabulary decides it on nonempty finite ordered
structures. The equivalence is required for
*every* linear order, so the notion is order-invariant: the sentence sees the
order, the problem does not. -/
def FODefinable (P : DecisionProblem L) : Prop :=
  ∃ φ : (L.sum Language.order).Sentence,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

end Lax485149.FirstOrderDefinability
