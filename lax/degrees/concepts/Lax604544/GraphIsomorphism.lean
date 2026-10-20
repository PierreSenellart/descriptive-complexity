import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Classes
import Lax799700.SubgraphIso
import Lax604544.RelationIsomorphism
import Lax604544.Degrees

/-!
---
title: Graph isomorphism and the class GI
type: definition
---
An instance is a pair of graphs on one universe, as for the subgraph
isomorphism problem of the catalog of NP-complete problems: a structure
with two unary marks, the vertices of the pattern and of the host, and two
binary relations, their edges. It is a yes-instance of Digraph Isomorphism
when it is finite and the two marked relations are isomorphic. It is a
yes-instance of Graph Isomorphism when moreover both relations are simple
graphs on their vertices, symmetric and irreflexive. Each problem is the
decision problem of the structures isomorphic to such an instance.

GI is the degree of Graph Isomorphism: the class of the problems that
reduce to it by an ordered first-order reduction. The degree is defined on
the undirected problem, the one the literature calls GI.
-/

namespace Lax604544.GraphIsomorphism

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax485149.Problems Lax799700.SubgraphIso
open Lax604544.RelationIsomorphism Lax604544.Degrees

section Problem

variable (A : Type) [twoGraphs.Structure A]

/-- The two marked graphs of the instance are isomorphic. -/
def HasDigraphIso : Prop :=
  Finite A ∧ RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Generic

variable {A : Type}

/-- The relation `E` is symmetric and irreflexive on the marked set `V`: a
simple graph, as opposed to an arbitrary binary relation. -/
def SimpleOn (V : A → Prop) (E : A → A → Prop) : Prop :=
  (∀ x y, V x → V y → E x y → E y x) ∧ ∀ x, V x → ¬E x x

end Generic

section Problem

variable (A : Type) [twoGraphs.Structure A]

/-- Both marked graphs are simple, and they are isomorphic. -/
def HasGraphIso : Prop :=
  Finite A ∧ SimpleOn (TGPatV (A := A)) TGPatE ∧ SimpleOn (TGHostV (A := A)) TGHostE ∧
    RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

/-- Digraph Isomorphism: are the two marked directed graphs of the instance
isomorphic? -/
def DigraphIso : DecisionProblem twoGraphs :=
  DecisionProblem.ofPred fun A _ => HasDigraphIso A

/-- Graph Isomorphism: are the two marked graphs simple and isomorphic? -/
def GraphIso : DecisionProblem twoGraphs :=
  DecisionProblem.ofPred fun A _ => HasGraphIso A

/-- **GI**: the degree of Graph Isomorphism. -/
def GI : ComplexityClass := below GraphIso

end Lax604544.GraphIsomorphism
