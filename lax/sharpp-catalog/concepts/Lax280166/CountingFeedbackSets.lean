import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Set.Finite.Lemmas
import Lax799700.CliqueFamily
import Lax799700.Feedback
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting feedback vertex and arc sets
type: definition
---
On a finite directed graph with $k$ marked vertices, #Feedback Vertex Set
counts the sets of exactly $k$ vertices whose removal leaves no directed
cycle. On a finite directed graph with a marked relation of $k$ pairs,
#Feedback Arc Set counts the sets of exactly $k$ arcs whose removal leaves no
directed cycle.
-/

namespace Lax280166.CountingFeedbackSets

open Lax799700.CliqueFamily Lax799700.Feedback

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The removal of the set `C` leaves an acyclic digraph, and `C` has exactly
as many elements as the `Kp`-marked set. -/
def FeedbackOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (C : A → Prop) : Prop :=
  AcyclicRel (SurvivingArc Adjp C) ∧ {x | C x}.ncard = {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [markedGraph.Structure A]

/-- The set `C` is a feedback vertex set with exactly as many vertices as the
marked set, in a finite marked digraph. -/
def FvsOfSize (C : A → Prop) : Prop :=
  Finite A ∧ FeedbackOfSizeOn (fun x y : A => MGAdj x y) (fun x => MGMarked x) C

end Problem

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The relation `F` is a set of arcs whose removal leaves an acyclic digraph,
with exactly as many pairs as the marked relation. -/
def FasOfSizeOn (Adjp Kp : A → A → Prop) (F : A → A → Prop) : Prop :=
  (∀ a b, F a b → Adjp a b) ∧ AcyclicRel (UncutArc Adjp F) ∧
    {p : A × A | F p.1 p.2}.ncard = {p : A × A | Kp p.1 p.2}.ncard

end Generic

section Problem

variable (A : Type) [markedArcGraph.Structure A]

/-- The relation `F` is a feedback arc set with exactly as many arcs as the
marked relation has pairs, in a finite arc-marked digraph. -/
def FasOfSize (F : A → A → Prop) : Prop :=
  Finite A ∧ FasOfSizeOn (fun a b : A => MAGAdj a b) (fun a b => MAGMarked a b) F

end Problem

open Lax366625.CountingProblems

/-- **#Feedback Vertex Set**, as a counting problem. -/
noncomputable def SharpFeedbackVertexSet : CountingProblem Lax799700.CliqueFamily.markedGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {C : A → Prop // FvsOfSize A C}

/-- **#Feedback Arc Set**, as a counting problem. -/
noncomputable def SharpFeedbackArcSet : CountingProblem Lax799700.Feedback.markedArcGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {F : A → A → Prop // FasOfSize A F}

end Lax280166.CountingFeedbackSets
