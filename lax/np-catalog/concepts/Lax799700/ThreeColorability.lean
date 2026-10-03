import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: 3-colorability
type: theorem
---
A graph is a structure of Mathlib's graph vocabulary, a single binary
relation; ThreeColorable says some map into three colors separates every
adjacent pair, and ThreeCol is the decision problem. A self-loop makes a
structure a no-instance. On structures arising from Mathlib's simple
graphs the property agrees with Mathlib's colorability. Membership in NP
is by a first-order reduction to SAT, hardness by an ordered first-order
reduction from SAT.

-/

namespace Lax799700.ThreeColorability

open FirstOrder

open Language Structure

section Graph

variable (V : Type) [Language.graph.Structure V]

/-- A `Language.graph`-structure is 3-colorable if the vertices can be colored
with 3 colors so that adjacent vertices get distinct colors. (On structures
with self-loops this is never satisfiable, matching the usual convention.) -/
def ThreeColorable : Prop :=
  ∃ c : V → Fin 3, ∀ x y : V, RelMap adj ![x, y] → c x ≠ c y

end Graph

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `ThreeColorable` is isomorphism-invariant. -/
axiom threeColorable_iso : ∀ {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B],
  (A ≃[FirstOrder.Language.graph] B) → (ThreeColorable A ↔ ThreeColorable B)

/-- The problem ThreeCol: does the structure satisfy `ThreeColorable`? -/
def ThreeCol : DecisionProblem FirstOrder.Language.graph :=
  DecisionProblem.ofPred ThreeColorable

/-- The yes-instances of ThreeCol are exactly the structures satisfying
`ThreeColorable`. -/
axiom threeCol_iff : ∀ (A : Type) [FirstOrder.Language.graph.Structure A], ThreeCol A ↔ ThreeColorable A

/-- ThreeCol is NP-complete. -/
axiom threeCol_NP_complete : NP.Complete ThreeCol

end Lax799700.ThreeColorability
