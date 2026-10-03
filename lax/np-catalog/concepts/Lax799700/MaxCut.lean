import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Lax799700.Feedback
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Max Cut
type: theorem
---
MAX CUT: is there a set $S$ of vertices such that at least $k$ edges have
exactly one endpoint in $S$? Since a cut can have quadratically many
edges, the threshold is carried at arity two, as the cardinality of a
marked binary relation, on the vocabulary Feedback Arc Set uses. The cut
is read as a set of ordered pairs (CutRel), $u$ adjacent to $v$ with $u$
inside $S$ and $v$ outside, which on a symmetric adjacency relation
counts every cut edge exactly once. Membership is by an existential
second-order definition, hardness by an ordered first-order reduction
from NAE-3SAT.

-/

namespace Lax799700.MaxCut

open Lax799700.Feedback

open FirstOrder

open Language Structure

section Semantics

variable {A : Type}

/-- The cut determined by `S`, as a relation: `a` is adjacent to `b`, `a` lies
inside `S` and `b` outside. Reading the cut as a set of ordered pairs of this
shape counts every cut edge of a symmetric adjacency relation once. -/
def CutRel (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ S a ∧ ¬S b

/-- Some cut is at least as large as the number encoded by the `Kp`-marked
pairs: “some cut has at least `k` edges”. -/
def MaxCutOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ S : A → Prop,
    {p : A × A | Kp p.1 p.2}.ncard ≤ {p : A × A | CutRel Adjp S p.1 p.2}.ncard

end Semantics

section Problem

/-- An arc-marked graph has a cut at least as large as its marked relation.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeCut (A : Type) [markedArcGraph.Structure A] : Prop :=
  Finite A ∧ MaxCutOn (MAGAdj (A := A)) (MAGMarked (A := A))

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasLargeCut` is isomorphism-invariant. -/
axiom hasLargeCut_iso : ∀ {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A] [Lax799700.Feedback.markedArcGraph.Structure B],
  (A ≃[Lax799700.Feedback.markedArcGraph] B) → (HasLargeCut A ↔ HasLargeCut B)

/-- The problem MaxCut: does the structure satisfy `HasLargeCut`? -/
def MaxCut : DecisionProblem Lax799700.Feedback.markedArcGraph :=
  DecisionProblem.ofPred HasLargeCut

/-- The yes-instances of MaxCut are exactly the structures satisfying `HasLargeCut`. -/
axiom maxCut_iff : ∀ (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A], MaxCut A ↔ HasLargeCut A

/-- MaxCut is NP-complete. -/
axiom maxCut_NP_complete : NP.Complete MaxCut

end Lax799700.MaxCut
