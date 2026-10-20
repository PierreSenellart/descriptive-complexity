import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax604544.RelationIsomorphism

/-!
---
title: Isomorphism of directed acyclic graphs
type: definition
---
An instance is a pair of directed graphs on one universe, each with a mark
on its vertices, a relation of arcs, and a further binary relation given as a
witness of acyclicity. That relation is a topological order of the arcs
when it is a strict partial order on the marked vertices containing the
arcs; the instance carries one because acyclicity is not first-order
definable, so a first-order reduction could not test it. The instance is a
yes-instance of DAG Isomorphism when it is finite, both witnesses are
topological orders, and the two marked arc relations are isomorphic; the
isomorphism is not required to respect the witnesses. DAG Isomorphism is the
decision problem of the structures isomorphic to such an instance.
-/

namespace Lax604544.DagIsomorphism

open Lax904597.Problems Lax485149.Problems Lax604544.RelationIsomorphism

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoDagsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern DAG. -/
  | patV : twoDagsRel 1
/-- `hostV a`: `a` is a vertex of the host DAG. -/
  | hostV : twoDagsRel 1
/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
  | patArc : twoDagsRel 2
/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
  | hostArc : twoDagsRel 2
/-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
  | patLt : twoDagsRel 2
/-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
  | hostLt : twoDagsRel 2
  deriving DecidableEq

/-- The relational language of two directed acyclic graphs: two arc relations
sharing a universe, each with its own vertex mark and its own topological
order. -/
def twoDags : FirstOrder.Language :=
  ⟨fun _ => Empty, twoDagsRel⟩

instance instIsRelationalTwoDags : FirstOrder.Language.IsRelational twoDags := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `patV a`: `a` is a vertex of the pattern DAG. -/
abbrev tdPatV : twoDags.Relations 1 :=
  .patV

/-- `hostV a`: `a` is a vertex of the host DAG. -/
abbrev tdHostV : twoDags.Relations 1 :=
  .hostV

/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
abbrev tdPatArc : twoDags.Relations 2 :=
  .patArc

/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
abbrev tdHostArc : twoDags.Relations 2 :=
  .hostArc

/-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
abbrev tdPatLt : twoDags.Relations 2 :=
  .patLt

/-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
abbrev tdHostLt : twoDags.Relations 2 :=
  .hostLt

open FirstOrder

open Language Structure

section Topo

variable {A : Type}

/-- `Lt` is a topological order for the arcs `Arc` on the marked set `V`: a
strict partial order (on `V`) containing the arcs. Its existence is exactly the
acyclicity of the arcs, and it is first-order checkable, which acyclicity
itself is not. -/
def TopoOn (V : A → Prop) (Lt Arc : A → A → Prop) : Prop :=
  (∀ x, V x → ¬Lt x x) ∧
    (∀ x y z, V x → V y → V z → Lt x y → Lt y z → Lt x z) ∧
    ∀ x y, V x → V y → Arc x y → Lt x y

end Topo

section Shorthands

variable {A : Type} [twoDags.Structure A]

/-- `patV a`: `a` is a vertex of the pattern DAG.  -/
def TDPatV {A : Type} [twoDags.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatV ![a0]

/-- `hostV a`: `a` is a vertex of the host DAG.  -/
def TDHostV {A : Type} [twoDags.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostV ![a0]

/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`.  -/
def TDPatArc {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatArc ![a0, a1]

/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`.  -/
def TDHostArc {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostArc ![a0, a1]

/-- `patLt a b`: `a` precedes `b` in the pattern's topological order.  -/
def TDPatLt {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdPatLt ![a0, a1]

/-- `hostLt a b`: `a` precedes `b` in the host's topological order.  -/
def TDHostLt {A : Type} [twoDags.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tdHostLt ![a0, a1]

end Shorthands

section Problem

variable (A : Type) [twoDags.Structure A]

/-- Both sides are well-formed – each order relation is a topological order of
its arcs, so both marked arc relations are acyclic – and the two DAGs are
isomorphic. The isomorphism relates the arcs only: the two orders are the
instance's acyclicity witnesses, not part of the structure being matched. -/
def HasDagIso : Prop :=
  Finite A ∧ TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
    TopoOn (TDHostV (A := A)) TDHostLt TDHostArc ∧
    RelIsoOn (TDPatV (A := A)) TDHostV TDPatArc TDHostArc

end Problem

/-- DAG Isomorphism: are the two marked acyclic graphs of the instance, given
with topological orders, isomorphic? -/
def DagIso : DecisionProblem twoDags :=
  DecisionProblem.ofPred fun A _ => HasDagIso A

end Lax604544.DagIsomorphism
