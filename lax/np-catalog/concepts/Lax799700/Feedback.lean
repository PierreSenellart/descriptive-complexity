import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Lax799700.CliqueFamily
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Feedback Vertex Set and Feedback Arc Set
type: theorem
---
The two feedback problems of Karp on directed graphs, the adjacency
relation of a structure being an arbitrary binary relation.
FeedbackVertexSet asks for at most $k$ vertices whose removal leaves an
acyclic digraph, $k$ the cardinality of the marked set of a marked graph.
FeedbackArcSet asks for at most $k$ arcs; a set of arcs can have
quadratically many elements, so its threshold moves one arity up, to the
vocabulary of graphs with a marked binary relation, the number being the
cardinality of the marked set of pairs. Self-loops are cycles, as they
should be. Acyclicity (AcyclicRel) is a transitive-closure condition,
not first-order, but it is equivalent to the existence of a strict
partial order containing every surviving arc; guessing that order is
what puts both problems in NP, and what makes the reductions provable
without manipulating cycles. Hardness is by first-order reductions, of
Feedback Vertex Set from Vertex Cover and of Feedback Arc Set from
Feedback Vertex Set.

-/

namespace Lax799700.Feedback

open Lax799700.CliqueFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedArcGraphRel : ℕ → Type where
/-- `adj a b`: there is an arc from `a` to `b`. -/
  | adj : markedArcGraphRel 2
/-- `marked a b`: the pair `(a, b)` belongs to the marked relation. -/
  | marked : markedArcGraphRel 2
  deriving DecidableEq

/-- The relational language of arc-marked digraphs: a digraph together with a
marked binary relation, whose cardinality (as a set of pairs) serves as
threshold. -/
def markedArcGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, markedArcGraphRel⟩

instance instIsRelationalMarkedArcGraph : FirstOrder.Language.IsRelational markedArcGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `adj a b`: there is an arc from `a` to `b`. -/
abbrev magAdj : markedArcGraph.Relations 2 :=
  .adj

/-- `marked a b`: the pair `(a, b)` belongs to the marked relation. -/
abbrev magMarked : markedArcGraph.Relations 2 :=
  .marked

open FirstOrder

open Language Structure

section Acyclicity

variable {A : Type}

/-- A relation is acyclic if no element is reachable from itself along a
nonempty path. -/
def AcyclicRel (R : A → A → Prop) : Prop :=
  ∀ x, ¬Relation.TransGen R x x

end Acyclicity

section Generic

variable {A : Type}

/-- An arc surviving the removal of the `Cp`-vertices: both endpoints are
outside `Cp` and the arc is present. -/
def SurvivingArc (Adjp : A → A → Prop) (Cp : A → Prop) (a b : A) : Prop :=
  ¬Cp a ∧ ¬Cp b ∧ Adjp a b

/-- An arc surviving the removal of the `Fp`-arcs: the arc is present and not
removed. -/
def UncutArc (Adjp : A → A → Prop) (Fp : A → A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ ¬Fp a b

/-- Some set of vertices whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked elements: “some feedback vertex
set is at most as large as the marked set”. -/
def FeedbackOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, AcyclicRel (SurvivingArc Adjp C) ∧ {x | C x}.ncard ≤ {x | Kp x}.ncard

/-- Some set of arcs whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked pairs: “some feedback arc set
is at most as large as the marked relation”. -/
def FeedbackArcOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ F : A → A → Prop, AcyclicRel (UncutArc Adjp F) ∧
    {p : A × A | F p.1 p.2}.ncard ≤ {p : A × A | Kp p.1 p.2}.ncard

end Generic

section Problems

section Shorthands

variable {A : Type} [markedArcGraph.Structure A]

/-- `adj a b`: there is an arc from `a` to `b`.  -/
def MAGAdj {A : Type} [markedArcGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap magAdj ![a0, a1]

/-- `marked a b`: the pair `(a, b)` belongs to the marked relation.  -/
def MAGMarked {A : Type} [markedArcGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap magMarked ![a0, a1]

end Shorthands

/-- A marked graph has a feedback vertex set at most as large as its marked
set. (Finiteness of the universe is part of the property: cardinality
thresholds are only meaningful on finite structures.) -/
def HasSmallFeedbackSet (A : Type) [markedGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackOn (MGAdj (A := A)) (MGMarked (A := A))

/-- An arc-marked digraph has a feedback arc set at most as large as its
marked relation. -/
def HasSmallFeedbackArcSet (A : Type) [markedArcGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackArcOn (MAGAdj (A := A)) (MAGMarked (A := A))

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSmallFeedbackSet` is isomorphism-invariant. -/
axiom hasSmallFeedbackSet_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasSmallFeedbackSet A ↔ HasSmallFeedbackSet B)

/-- The problem FeedbackVertexSet: does the structure satisfy `HasSmallFeedbackSet`? -/
def FeedbackVertexSet : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasSmallFeedbackSet

/-- The yes-instances of FeedbackVertexSet are exactly the structures
satisfying `HasSmallFeedbackSet`. -/
axiom feedbackVertexSet_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], FeedbackVertexSet A ↔ HasSmallFeedbackSet A

/-- FeedbackVertexSet is NP-complete. -/
axiom feedbackVertexSet_NP_complete : NP.Complete FeedbackVertexSet

/-- The property `HasSmallFeedbackArcSet` is isomorphism-invariant. -/
axiom hasSmallFeedbackArcSet_iso : ∀ {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A] [Lax799700.Feedback.markedArcGraph.Structure B],
  (A ≃[Lax799700.Feedback.markedArcGraph] B) → (HasSmallFeedbackArcSet A ↔ HasSmallFeedbackArcSet B)

/-- The problem FeedbackArcSet: does the structure satisfy `HasSmallFeedbackArcSet`? -/
def FeedbackArcSet : DecisionProblem Lax799700.Feedback.markedArcGraph :=
  DecisionProblem.ofPred HasSmallFeedbackArcSet

/-- The yes-instances of FeedbackArcSet are exactly the structures satisfying
`HasSmallFeedbackArcSet`. -/
axiom feedbackArcSet_iff : ∀ (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A], FeedbackArcSet A ↔ HasSmallFeedbackArcSet A

/-- FeedbackArcSet is NP-complete. -/
axiom feedbackArcSet_NP_complete : NP.Complete FeedbackArcSet

end Lax799700.Feedback
