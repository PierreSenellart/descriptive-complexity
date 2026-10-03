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
title: Dominating Set
type: theorem
---
DOMINATING SET: is there a set of vertices, at most as large as the
marked set, such that every vertex is in it or adjacent to it? The
vocabulary is that of marked graphs, the one Clique and Vertex Cover use.
Domination ranges over every element of the universe, so a reduction
into it cannot leave junk tuples behind: the first-order reduction from
Set Cover makes the junk adjacent to the vertices that a solution always
contains. Membership is by an existential second-order definition.

-/

namespace Lax799700.DominatingSet

open Lax799700.CliqueFamily

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

/-- Some set of vertices dominating the whole graph – every vertex belongs to
it or has a neighbor in it – is at most as large as the number encoded by the
`Kp`-marked elements. -/
def DominatesOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ D : A → Prop, (∀ v, D v ∨ ∃ u, D u ∧ Adjp u v) ∧
    {v | D v}.ncard ≤ {v | Kp v}.ncard

end Generic

section Problem

variable (A : Type) [markedGraph.Structure A]

/-- A marked graph has a dominating set at most as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallDominatingSet : Prop :=
  Finite A ∧ DominatesOn (MGAdj (A := A)) (MGMarked (A := A))

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSmallDominatingSet` is isomorphism-invariant. -/
axiom hasSmallDominatingSet_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasSmallDominatingSet A ↔ HasSmallDominatingSet B)

/-- The problem DominatingSet: does the structure satisfy `HasSmallDominatingSet`? -/
def DominatingSet : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasSmallDominatingSet

/-- The yes-instances of DominatingSet are exactly the structures satisfying `HasSmallDominatingSet`. -/
axiom dominatingSet_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], DominatingSet A ↔ HasSmallDominatingSet A

/-- DominatingSet is NP-complete. -/
axiom dominatingSet_NP_complete : NP.Complete DominatingSet

end Lax799700.DominatingSet
