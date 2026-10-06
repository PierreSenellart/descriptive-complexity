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
import Lax799700.CliqueFamily
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting dominating sets
type: definition
---
On a finite marked graph with $k$ marked vertices, #Dominating Set counts the
sets of exactly $k$ vertices such that every vertex is in the set or adjacent
to one of its elements.
-/

namespace Lax280166.CountingDominatingSets

open Lax799700.CliqueFamily

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `D` dominates every vertex and has exactly as many elements as the
`Kp`-marked set. -/
def DomOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (D : A → Prop) : Prop :=
  (∀ v, D v ∨ ∃ u, D u ∧ Adjp u v) ∧ {v | D v}.ncard = {v | Kp v}.ncard

end Generic

section Solutions

variable (A : Type) [markedGraph.Structure A]

/-- The set `D` is a dominating set with exactly as many vertices as the marked
set, in a finite marked graph. -/
def DomSetOfSize (D : A → Prop) : Prop :=
  Finite A ∧ DomOfSizeOn (fun u v : A => MGAdj u v) (fun v => MGMarked v) D

end Solutions

open Lax366625.CountingProblems

/-- **#Dominating Set**, as a counting problem. -/
noncomputable def SharpDominatingSet : CountingProblem Lax799700.CliqueFamily.markedGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {D : A → Prop // DomSetOfSize A D}

end Lax280166.CountingDominatingSets
