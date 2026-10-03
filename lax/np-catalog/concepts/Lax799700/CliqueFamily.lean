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
title: Clique, Independent Set and Vertex Cover
type: theorem
---
The three classical threshold problems on graphs, as decision problems on
marked graphs: a binary adjacency relation and a unary mark whose
cardinality is the threshold $k$ of the textbook problems, in unary
representation, order-free and isomorphism-invariant. Clique asks for a
clique at least as large as the marked set, IndependentSet for an
independent set at least as large, VertexCover for a vertex cover at most
as large. Self-loops are ignored and adjacency is required in both
directions, so the problems agree with their standard versions on simple
graphs. Finiteness of the universe is part of the yes-instances, since
cardinality thresholds only mean something on finite structures.

Clique is in NP by an existential second-order definition that guesses
an injection of the marked set into a clique, and NP-hard by an ordered
first-order reduction from SAT. Independent Set reduces to and from
Clique by complementing the edges, and Vertex Cover to and from
Independent Set by complementing the chosen set; these two first-order
reductions give both their membership and their hardness.

-/

namespace Lax799700.CliqueFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedGraphRel : ℕ → Type where
/-- `adj a b`: there is an edge from `a` to `b`. -/
  | adj : markedGraphRel 2
/-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : markedGraphRel 1
  deriving DecidableEq

/-- The relational language of marked graphs: a graph together with a marked
subset of its vertices, whose cardinality serves as threshold. -/
def markedGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, markedGraphRel⟩

instance instIsRelationalMarkedGraph : FirstOrder.Language.IsRelational markedGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `adj a b`: there is an edge from `a` to `b`. -/
abbrev mgAdj : markedGraph.Relations 2 :=
  .adj

/-- `marked a`: the element `a` belongs to the marked set. -/
abbrev mgMarked : markedGraph.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

/-- Some set that is pairwise `Adjp`-related (off the diagonal) is at least as
large as the number encoded by the `Kp`-marked elements: “some clique is at
least as large as the marked set”. -/
def CliqueOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧
    {x | Kp x}.ncard ≤ {x | S x}.ncard

/-- Some set that is pairwise non-`Adjp`-related (off the diagonal) is at least
as large as the number encoded by the `Kp`-marked elements: “some independent
set is at least as large as the marked set”. -/
def IndepOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CliqueOn (fun x y => ¬Adjp x y) Kp

/-- Some set meeting every (off-diagonal) `Adjp`-edge is at most as large as
the number encoded by the `Kp`-marked elements: “some vertex cover is at most
as large as the marked set”. -/
def CoverOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ∧
    {x | C x}.ncard ≤ {x | Kp x}.ncard

end Generic

section Problems

section Shorthands

variable {A : Type} [markedGraph.Structure A]

/-- `adj a b`: there is an edge from `a` to `b`.  -/
def MGAdj {A : Type} [markedGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap mgAdj ![a0, a1]

/-- `marked a`: the element `a` belongs to the marked set.  -/
def MGMarked {A : Type} [markedGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap mgMarked ![a0]

end Shorthands

variable (A : Type) [markedGraph.Structure A]

/-- A marked graph contains a clique at least as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeClique : Prop :=
  Finite A ∧ CliqueOn (MGAdj (A := A)) (MGMarked (A := A))

/-- A marked graph contains an independent set at least as large as its
marked set. -/
def HasLargeIndependentSet : Prop :=
  Finite A ∧ IndepOn (MGAdj (A := A)) (MGMarked (A := A))

/-- A marked graph contains a vertex cover at most as large as its marked
set. -/
def HasSmallVertexCover : Prop :=
  Finite A ∧ CoverOn (MGAdj (A := A)) (MGMarked (A := A))

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasLargeClique` is isomorphism-invariant. -/
axiom hasLargeClique_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasLargeClique A ↔ HasLargeClique B)

/-- The problem Clique: does the structure satisfy `HasLargeClique`? -/
def Clique : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasLargeClique

/-- The yes-instances of Clique are exactly the structures satisfying `HasLargeClique`. -/
axiom clique_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], Clique A ↔ HasLargeClique A

/-- Clique is NP-complete. -/
axiom clique_NP_complete : NP.Complete Clique

/-- The property `HasLargeIndependentSet` is isomorphism-invariant. -/
axiom hasLargeIndependentSet_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasLargeIndependentSet A ↔ HasLargeIndependentSet B)

/-- The problem IndependentSet: does the structure satisfy `HasLargeIndependentSet`? -/
def IndependentSet : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasLargeIndependentSet

/-- The yes-instances of IndependentSet are exactly the structures satisfying `HasLargeIndependentSet`. -/
axiom indSet_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], IndependentSet A ↔ HasLargeIndependentSet A

/-- IndependentSet is NP-complete. -/
axiom indSet_NP_complete : NP.Complete IndependentSet

/-- The property `HasSmallVertexCover` is isomorphism-invariant. -/
axiom hasSmallVertexCover_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasSmallVertexCover A ↔ HasSmallVertexCover B)

/-- The problem VertexCover: does the structure satisfy `HasSmallVertexCover`? -/
def VertexCover : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasSmallVertexCover

/-- The yes-instances of VertexCover are exactly the structures satisfying `HasSmallVertexCover`. -/
axiom vertexCover_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], VertexCover A ↔ HasSmallVertexCover A

/-- VertexCover is NP-complete. -/
axiom vertexCover_NP_complete : NP.Complete VertexCover

end Lax799700.CliqueFamily
