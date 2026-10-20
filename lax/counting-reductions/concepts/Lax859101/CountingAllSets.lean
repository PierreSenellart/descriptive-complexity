import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Mathlib.ModelTheory.Graph
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Hom.Set
import Lax366625.CountingProblems

/-!
---
title: Counting all independent sets, vertex covers, and 3-colorings
type: definition
---
On a graph, counting all independent sets counts the sets of vertices
without an edge between two of their elements, and counting all vertex
covers the sets of vertices meeting every edge, whatever their size.
#3-Colorability counts the proper colorings with three colors.
-/

namespace Lax859101.CountingAllSets

/-- The set `S` is independent for `Adj`: no two distinct elements of it are
related. -/
def IndepSet {T : Type} (Adj : T → T → Prop) (S : T → Prop) : Prop :=
  ∀ x y, S x → S y → x ≠ y → ¬Adj x y

open FirstOrder

open Language Structure

section Graph

variable {A : Type} [Language.graph.Structure A]

/-- A **vertex cover**: every edge has an end in it. -/
def GVertexCover (A : Type) [Language.graph.Structure A] (C : A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → RelMap Language.adj ![x, y] → C x ∨ C y

end Graph

open Lax366625.CountingProblems

/-- **#3-Colorability**, as a counting problem. -/
noncomputable def SharpThreeCol : CountingProblem FirstOrder.Language.graph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {χ : A → Fin 3 // ∀ x y : A, RelMap Language.adj ![x, y] → χ x ≠ χ y}

/-- **Counting all independent sets**, as a counting problem. -/
noncomputable def SharpAllIndependentSets : CountingProblem FirstOrder.Language.graph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S}

/-- **Counting all vertex covers**, as a counting problem. -/
noncomputable def SharpAllVertexCovers : CountingProblem FirstOrder.Language.graph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {C : A → Prop // GVertexCover A C}

end Lax859101.CountingAllSets
