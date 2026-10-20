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
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems

/-!
---
title: Counting cliques, independent sets, and vertex covers
type: definition
---
On a finite marked graph with $k$ marked vertices, #Clique counts the cliques
of exactly $k$ vertices, #Independent Set the independent sets of exactly $k$
vertices, and #Vertex Cover the vertex covers of exactly $k$ vertices. The
count is taken at the threshold size: a set larger or smaller than the
marked set is not counted.
-/

namespace Lax280166.CountingCliques

open Lax799700.CliqueFamily

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [markedGraph.Structure A]

/-- The set `S` is a clique with exactly as many vertices as the marked set, in
a finite marked graph. -/
def CliqueOfSize (S : A → Prop) : Prop :=
  Finite A ∧ (∀ x y, S x → S y → x ≠ y → MGAdj x y) ∧
    {x | S x}.ncard = {x : A | MGMarked x}.ncard

end Solutions

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `S` is pairwise `Adjp`-related off the diagonal and has exactly as
many elements as the `Kp`-marked set. -/
def CliqueOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧ {x | S x}.ncard = {x | Kp x}.ncard

/-- The set `C` meets every off-diagonal `Adjp`-edge and has exactly as many
elements as the `Kp`-marked set. -/
def CoverOfSizeOn (Adjp : A → A → Prop) (Kp : A → Prop) (C : A → Prop) : Prop :=
  (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ∧ {x | C x}.ncard = {x | Kp x}.ncard

end Generic

section Problems

variable (A : Type) [markedGraph.Structure A]

/-- The set `S` is an independent set with exactly as many vertices as the
marked set, in a finite marked graph. -/
def IndepOfSize (S : A → Prop) : Prop :=
  Finite A ∧ CliqueOfSizeOn (fun x y : A => ¬MGAdj x y) (fun x => MGMarked x) S

/-- The set `C` is a vertex cover with exactly as many vertices as the marked
set, in a finite marked graph. -/
def CoverOfSize (C : A → Prop) : Prop :=
  Finite A ∧ CoverOfSizeOn (fun x y : A => MGAdj x y) (fun x => MGMarked x) C

end Problems

open Lax366625.CountingProblems

/-- **#Clique**, as a counting problem. -/
noncomputable def SharpClique : CountingProblem Lax799700.CliqueFamily.markedGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // CliqueOfSize A S}

/-- **#Independent Set**, as a counting problem. -/
noncomputable def SharpIndependentSet : CountingProblem Lax799700.CliqueFamily.markedGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // IndepOfSize A S}

/-- **#Vertex Cover**, as a counting problem. -/
noncomputable def SharpVertexCover : CountingProblem Lax799700.CliqueFamily.markedGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {C : A → Prop // CoverOfSize A C}

end Lax280166.CountingCliques
