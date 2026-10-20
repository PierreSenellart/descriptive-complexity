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
title: #BIS and #PP2DNF
type: definition
---
A bipartite graph is given with its bipartition, a mark on the left side,
and its edges, read from left to right. #BIS counts the independent sets:
the sets of vertices with no edge from a left member to a right member.
#PP2DNF counts the models of the partitioned positive 2-DNF formula of the
graph, with one variable per vertex and one term $x \wedge y$ per edge from
$x$ to $y$: the sets of vertices containing both ends of some edge.
-/

namespace Lax859101.CountingBipartite

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive bipGraphRel : ℕ → Type where
/-- `left a`: the vertex `a` is on the left side. -/
  | left : bipGraphRel 1
/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
  | edge : bipGraphRel 2
  deriving DecidableEq

/-- The relational language of bipartite graphs given with their bipartition. -/
def bipGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, bipGraphRel⟩

instance instIsRelationalBipGraph : FirstOrder.Language.IsRelational bipGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `left a`: the vertex `a` is on the left side. -/
abbrev bgLeft : bipGraph.Relations 1 :=
  .left

/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
abbrev bgEdge : bipGraph.Relations 2 :=
  .edge

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [bipGraph.Structure A]

/-- `left a`: the vertex `a` is on the left side.  -/
def BGLeft {A : Type} [bipGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bgLeft ![a0]

/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
left and `b` on the right.  -/
def BGEdge {A : Type} [bipGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bgEdge ![a0, a1]

end Shorthands

/-- The set `S` is independent in a bipartite graph: no edge goes from a left
member of `S` to a right member of `S`. -/
def BipIndep (A : Type) [bipGraph.Structure A] (S : A → Prop) : Prop :=
  ∀ x y : A, S x → S y → BGLeft x → ¬BGLeft y → ¬BGEdge x y

/-- The set `S` of true variables satisfies the partitioned positive 2-DNF
formula of a bipartite graph – one variable per vertex, one term `x ∧ y` per
edge from a left vertex `x` to a right vertex `y`: some term has both its
variables true. -/
def Pp2dnfModel (A : Type) [bipGraph.Structure A] (S : A → Prop) : Prop :=
  ∃ x y : A, S x ∧ S y ∧ BGLeft x ∧ ¬BGLeft y ∧ BGEdge x y

open Lax366625.CountingProblems

/-- **#BIS**, as a counting problem. -/
noncomputable def SharpBIS : CountingProblem Lax859101.CountingBipartite.bipGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // BipIndep A S}

/-- **#PP2DNF**, as a counting problem. -/
noncomputable def SharpPP2DNF : CountingProblem Lax859101.CountingBipartite.bipGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // Pp2dnfModel A S}

end Lax859101.CountingBipartite
