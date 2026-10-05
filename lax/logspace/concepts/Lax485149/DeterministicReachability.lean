import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.Reachability

/-!
---
title: Deterministic reachability in directed graphs
type: definition
---
In a directed graph with marked sources and targets, an edge $(a, b)$ is
forced when it is the only edge leaving $a$. An instance is a yes-instance
of REACHd when some marked target is reachable from some marked source by a
possibly empty path of forced edges; no promise is made on the instance,
whose vertices may have any outdegree. REACHd is the decision problem of the
structures isomorphic to such an instance, and UNREACHd is its complement.
-/

namespace Lax485149.DeterministicReachability

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax485149.Problems Lax485149.Complement Lax485149.Reachability

/-- A *forced* arc: an arc that is the only one out of its source. Following
these is the deterministic walk on a marked graph, with no promise on the
instance. -/
def DetEdge {A : Type} [stGraph.Structure A] (a b : A) : Prop :=
  SGEdge a b ∧ ∀ c : A, SGEdge a c → c = b

/-- Some marked target is reachable from some marked source along a (possibly
empty) path of forced arcs. -/
def DetReachable (A : Type) [stGraph.Structure A] : Prop :=
  ∃ s t : A, SGSource s ∧ SGTarget t ∧ Relation.ReflTransGen DetEdge s t

/-- REACHd, deterministic reachability: is a marked target reachable from a
marked source along forced arcs? -/
def REACHd : DecisionProblem stGraph := DecisionProblem.ofPred fun A _ => DetReachable A

/-- UNREACHd, the complement of REACHd. -/
def UNREACHd : DecisionProblem stGraph := DecisionProblem.compl REACHd

end Lax485149.DeterministicReachability
