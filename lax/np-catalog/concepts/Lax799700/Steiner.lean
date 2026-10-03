import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Steiner Tree
type: theorem
---
STEINER TREE: given a graph, a set of terminals and a threshold $k$, is
there a connected set of vertices containing every terminal and using at
most $k$ non-terminals (SteinerTree, the node-weighted form with unit
weights), or a set of at most $k$ arcs of the graph connecting a set of
vertices that contains every terminal (EdgeSteinerTree, the edge-weighted
form, arcs counted as ordered pairs)? The vocabulary is that of graphs
with two unary marks, the terminals and the marked set carrying $k$ in
unary representation. Connectivity (ConnectedOn) is not first-order; the
membership proofs certify it by a root of the chosen set and a strict
partial order in which every other chosen vertex has a chosen neighbor
strictly below it. Both forms are NP-hard by ordered first-order
reductions from Vertex Cover.

-/

namespace Lax799700.Steiner

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive steinerGraphRel : ℕ → Type where
/-- `adj a b`: there is an edge between `a` and `b`. -/
  | adj : steinerGraphRel 2
/-- `terminal a`: the vertex `a` must be spanned. -/
  | terminal : steinerGraphRel 1
/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
  | marked : steinerGraphRel 1
  deriving DecidableEq

/-- The relational language of graphs with terminals: adjacency, a set of
terminals to be spanned, and a marked set whose cardinality is the budget of
non-terminals. -/
def steinerGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, steinerGraphRel⟩

instance instIsRelationalSteinerGraph : FirstOrder.Language.IsRelational steinerGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `adj a b`: there is an edge between `a` and `b`. -/
abbrev stAdj : steinerGraph.Relations 2 :=
  .adj

/-- `terminal a`: the vertex `a` must be spanned. -/
abbrev stTerminal : steinerGraph.Relations 1 :=
  .terminal

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
abbrev stMarked : steinerGraph.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Connectivity

variable {A : Type}

/-- The edges available inside a chosen set: adjacency in either direction,
restricted to the set. -/
def Link (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ (Adjp a b ∨ Adjp b a)

/-- A set of vertices is connected if any two of its members are joined by a
path inside it. -/
def ConnectedOn (Adjp : A → A → Prop) (S : A → Prop) : Prop :=
  ∀ x y, S x → S y → Relation.ReflTransGen (Link Adjp S) x y

end Connectivity

section Generic

variable {A : Type}

/-- Some connected set contains every terminal and uses at most as many
non-terminals as the number encoded by the marked set. -/
def SteinerOn (Adjp : A → A → Prop) (Term Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard ≤ {x | Kp x}.ncard

variable {B : Type}

/-- Some set of edges of the graph, connecting a set that contains every
terminal, is at most as large as the number encoded by the marked set: the
*edge-weighted* Steiner tree with unit weights, Karp's original reading.

The chosen edges are given as a set of ordered pairs, one per edge, and
connectivity reads them symmetrically
(`DescriptiveComplexity.ConnectedOn`); a witness listing both orientations of an edge
merely pays for it twice, so the yes-instances are unaffected. The threshold
compares a count of *pairs* with a count of *elements*, which is meaningful
because a threshold is just a number – and necessary here, since an edge set
can be quadratically larger than the universe. -/
def SteinerEdgeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) : Prop :=
  ∃ T : A → A → Prop, ∃ S : A → Prop,
    (∀ a b, T a b → Adjp a b) ∧ (∀ x, Term x → S x) ∧ ConnectedOn T S ∧
    {p : A × A | T p.1 p.2}.ncard ≤ {x | Kp x}.ncard

end Generic

section Problem

section Shorthands

variable {A : Type} [steinerGraph.Structure A]

/-- `adj a b`: there is an edge between `a` and `b`.  -/
def STAdj {A : Type} [steinerGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stAdj ![a0, a1]

/-- `terminal a`: the vertex `a` must be spanned.  -/
def STTerminal {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stTerminal ![a0]

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
threshold.  -/
def STMarked {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stMarked ![a0]

end Shorthands

variable (A : Type) [steinerGraph.Structure A]

/-- A graph with terminals admits a connected set spanning the terminals and
using at most as many non-terminals as its marked set has elements.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSteinerTree : Prop :=
  Finite A ∧ SteinerOn (STAdj (A := A)) STTerminal STMarked

end Problem

/-- A graph with terminals admits a set of edges connecting its terminals, of
size at most the number encoded by the marked set. -/
def HasSmallEdgeSteinerTree (A : Type) [steinerGraph.Structure A] : Prop :=
  Finite A ∧ SteinerEdgeOn (STAdj (A := A)) STTerminal STMarked

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSmallEdgeSteinerTree` is isomorphism-invariant. -/
axiom hasSmallEdgeSteinerTree_iso : ∀ {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A] [Lax799700.Steiner.steinerGraph.Structure B],
  (A ≃[Lax799700.Steiner.steinerGraph] B) → (HasSmallEdgeSteinerTree A ↔ HasSmallEdgeSteinerTree B)

/-- The problem EdgeSteinerTree: does the structure satisfy `HasSmallEdgeSteinerTree`? -/
def EdgeSteinerTree : DecisionProblem Lax799700.Steiner.steinerGraph :=
  DecisionProblem.ofPred HasSmallEdgeSteinerTree

/-- The yes-instances of EdgeSteinerTree are exactly the structures satisfying `HasSmallEdgeSteinerTree`. -/
axiom edgeSteinerTree_iff : ∀ (A : Type) [Lax799700.Steiner.steinerGraph.Structure A], EdgeSteinerTree A ↔ HasSmallEdgeSteinerTree A

/-- EdgeSteinerTree is NP-complete. -/
axiom edgeSteinerTree_NP_complete : NP.Complete EdgeSteinerTree

/-- The property `HasSmallSteinerTree` is isomorphism-invariant. -/
axiom hasSmallSteinerTree_iso : ∀ {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A] [Lax799700.Steiner.steinerGraph.Structure B],
  (A ≃[Lax799700.Steiner.steinerGraph] B) → (HasSmallSteinerTree A ↔ HasSmallSteinerTree B)

/-- The problem SteinerTree: does the structure satisfy `HasSmallSteinerTree`? -/
def SteinerTree : DecisionProblem Lax799700.Steiner.steinerGraph :=
  DecisionProblem.ofPred HasSmallSteinerTree

/-- The yes-instances of SteinerTree are exactly the structures satisfying `HasSmallSteinerTree`. -/
axiom steinerTree_iff : ∀ (A : Type) [Lax799700.Steiner.steinerGraph.Structure A], SteinerTree A ↔ HasSmallSteinerTree A

/-- SteinerTree is NP-complete. -/
axiom steinerTree_NP_complete : NP.Complete SteinerTree

end Lax799700.Steiner
