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
import Lax799700.Steiner
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting Steiner trees
type: definition
---
On a finite graph with terminals and $k$ marked vertices, #Steiner Tree counts
the sets of exactly $k$ non-terminal vertices which, with the terminals,
induce a connected subgraph.
-/

namespace Lax280166.CountingSteinerTrees

open Lax799700.Steiner

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `S` contains every terminal, is connected, and has exactly as many
non-terminals as the `Kp`-marked set has elements. -/
def SteinerOfSizeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard = {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [steinerGraph.Structure A]

/-- The set `S` is a connected set containing every terminal and using exactly
as many non-terminals as the marked set has elements, in a finite graph. -/
def SteinerOfSize (S : A → Prop) : Prop :=
  Finite A ∧ SteinerOfSizeOn (fun a b : A => STAdj a b) (fun a => STTerminal a)
    (fun a => STMarked a) S

end Problem

open Lax366625.CountingProblems

/-- **#Steiner Tree**, as a counting problem. -/
noncomputable def SharpSteinerTree : CountingProblem Lax799700.Steiner.steinerGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // SteinerOfSize A S}

end Lax280166.CountingSteinerTrees
