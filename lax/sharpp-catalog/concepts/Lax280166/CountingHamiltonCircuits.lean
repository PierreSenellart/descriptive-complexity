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
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.OrderOfElement
import Lax799700.Hamilton
import Lax904597.Machines
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting Hamilton circuits
type: definition
---
On a finite directed graph, #Directed Hamilton Circuit counts the directed
Hamilton circuits, each given by its successor relation: a relation along
the arcs that is a single cycle through every vertex. #Hamilton Circuit
counts the undirected Hamilton circuits of the symmetric closure, each given
by its set of edges, so that a circuit and its reverse count once.
-/

namespace Lax280166.CountingHamiltonCircuits

open Lax799700.Hamilton Lax904597.Machines

open FirstOrder

open Language Structure

section Circuit

variable {A : Type}

/-- `y` comes next after `x` on the circuit a linear order is a cut of: it is
the immediate successor of `x`, or `x` is the last element and `y` the
first. -/
def CycSucc (Le : A → A → Prop) (x y : A) : Prop :=
  SuccOf Le x y ∨ ((∀ z, Le z x) ∧ ∀ z, Le y z)

/-- The relation `Nxt` is a Hamilton circuit of `R`: the cyclic successor
relation of a linear order of the universe, included in `R`. -/
def IsCircuit (R : A → A → Prop) (Nxt : A → A → Prop) : Prop :=
  ∃ Le : A → A → Prop, IsLinOrd Le ∧ (∀ x y, Nxt x y ↔ CycSucc Le x y) ∧
    ∀ x y, Nxt x y → R x y

end Circuit

section Problem

variable (A : Type) [digraph.Structure A]

/-- The relation `Nxt` is a Hamilton circuit of a finite digraph. -/
def DirCircuit (Nxt : A → A → Prop) : Prop :=
  Finite A ∧ IsCircuit (fun x y : A => DGArc x y) Nxt

end Problem

open FirstOrder

open Language Structure

section UCircuit

variable {A : Type}

/-- The relation `E` is the edge set of a Hamilton circuit of `R`: the
symmetric closure of a circuit of `R`. -/
def IsUCircuit (R : A → A → Prop) (E : A → A → Prop) : Prop :=
  ∃ Nxt : A → A → Prop, IsCircuit R Nxt ∧ ∀ x y, E x y ↔ (Nxt x y ∨ Nxt y x)

end UCircuit

section Problem

variable (A : Type) [digraph.Structure A]

/-- The relation `E` is the edge set of a Hamilton circuit of a finite
graph. -/
def UCircuit (E : A → A → Prop) : Prop :=
  Finite A ∧ IsUCircuit (fun x y : A => DGEdge x y) E

end Problem

open Lax366625.CountingProblems

/-- **#Directed Hamilton Circuit**, as a counting problem. -/
noncomputable def SharpDirHamCircuit : CountingProblem Lax799700.Hamilton.digraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt}

/-- **#Hamilton Circuit**, as a counting problem. -/
noncomputable def SharpHamCircuit : CountingProblem Lax799700.Hamilton.digraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {E : A → A → Prop // UCircuit A E}

end Lax280166.CountingHamiltonCircuits
