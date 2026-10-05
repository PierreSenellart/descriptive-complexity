import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement

/-!
---
title: Reachability and unreachability in directed graphs
type: definition
---
An instance is a directed graph with marked source vertices and marked target
vertices: a structure over the vocabulary with a binary relation of edges
and two unary relations of sources and targets. It is a yes-instance of
REACH when some marked target is reachable from some marked source by a
directed path, possibly empty; REACH is the decision problem of the
structures isomorphic to such an instance. UNREACH is the complement of
REACH: no marked target is reachable from a marked source.
-/

namespace Lax485149.Reachability

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax485149.Problems Lax485149.Complement

/-- The relation symbols of graphs with marked sources and targets. -/
inductive stGraphRel : ℕ → Type where
  /-- `edge a b`: there is an edge from `a` to `b`. -/
  | edge : stGraphRel 2
  /-- `source a`: the vertex `a` is a marked source. -/
  | source : stGraphRel 1
  /-- `target a`: the vertex `a` is a marked target. -/
  | target : stGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of directed graphs with marked sources and
targets. -/
def stGraph : Language :=
  ⟨fun _ => Empty, stGraphRel⟩

instance instIsRelationalStGraph : IsRelational stGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `edge a b`: there is an edge from `a` to `b`. -/
abbrev sgEdge : stGraph.Relations 2 := .edge

/-- `source a`: the vertex `a` is a marked source. -/
abbrev sgSource : stGraph.Relations 1 := .source

/-- `target a`: the vertex `a` is a marked target. -/
abbrev sgTarget : stGraph.Relations 1 := .target

/-- `edge a b`: there is an edge from `a` to `b`. -/
def SGEdge {A : Type} [stGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  RelMap sgEdge ![a0, a1]

/-- `source a`: the vertex `a` is a marked source. -/
def SGSource {A : Type} [stGraph.Structure A] (a0 : A) : Prop :=
  RelMap sgSource ![a0]

/-- `target a`: the vertex `a` is a marked target. -/
def SGTarget {A : Type} [stGraph.Structure A] (a0 : A) : Prop :=
  RelMap sgTarget ![a0]

/-- Some marked target is reachable from some marked source, along a
(possibly empty) directed path. -/
def Reachable (A : Type) [stGraph.Structure A] : Prop :=
  ∃ s t : A, SGSource s ∧ SGTarget t ∧ Relation.ReflTransGen SGEdge s t

/-- REACH: is some marked target reachable from some marked source? -/
def REACH : DecisionProblem stGraph := DecisionProblem.ofPred fun A _ => Reachable A

/-- UNREACH, the complement of REACH: no marked target is reachable from a
marked source. -/
def UNREACH : DecisionProblem stGraph := DecisionProblem.compl REACH

end Lax485149.Reachability
