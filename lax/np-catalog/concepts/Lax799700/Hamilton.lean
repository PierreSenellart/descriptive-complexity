import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Syntax
import Lax904597.Machines
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Hamilton circuits
type: theorem
---
DIRECTED HAMILTON CIRCUIT and HAMILTON CIRCUIT: does a graph have a
circuit visiting every vertex exactly once? Both live on the vocabulary
of digraphs, a single binary relation; the undirected problem reads that
relation symmetrically (DGEdge). A circuit is read, after cutting it
anywhere, as a linear order whose consecutive elements are adjacent and
whose last element is adjacent to its first (TourOn); a relation is what
an existential second-order block can guess, and the rest is first-order,
so both problems are in NP. The empty graph is a yes-instance and a
one-element graph is one exactly when it has a self-loop. Hardness of
the undirected problem is a relativized ordered first-order reduction
from Vertex Cover, the one reduction of the catalog that needs the
relativized form; the directed problem is NP-hard by a first-order
reduction from the undirected one.

-/

namespace Lax799700.Hamilton

open Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digraphRel : ℕ → Type where
/-- `arc a b`: there is an arc from `a` to `b`. -/
  | arc : digraphRel 2
  deriving DecidableEq

/-- The relational language of digraphs: one binary relation. The undirected
problem reads it symmetrically rather than on a vocabulary of its own. -/
def digraph : FirstOrder.Language :=
  ⟨fun _ => Empty, digraphRel⟩

instance instIsRelationalDigraph : FirstOrder.Language.IsRelational digraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `arc a b`: there is an arc from `a` to `b`. -/
abbrev dgArc : digraph.Relations 2 :=
  .arc

open FirstOrder

open Language Structure

section Tour

variable {A : Type}

/-- `y` is the immediate `Le`-successor of `x`: above it, distinct from it,
and with nothing strictly in between. -/
def SuccOf (Le : A → A → Prop) (x y : A) : Prop :=
  Le x y ∧ x ≠ y ∧ ∀ z, Le x z → Le z y → z = x ∨ z = y

/-- A **tour** of a relation: a linear order of the universe whose
consecutive elements are related and whose last element is related to its
first. On a finite universe this is exactly a Hamilton circuit, cut open at
one place. -/
def TourOn (R : A → A → Prop) : Prop :=
  ∃ Le : A → A → Prop, IsLinOrd Le ∧ (∀ x y, SuccOf Le x y → R x y) ∧
    ∀ x y, (∀ z, Le x z) → (∀ z, Le z y) → R y x

end Tour

section Problems

variable {A : Type} [digraph.Structure A]

/-- `arc a b`: there is an arc from `a` to `b`.  -/
def DGArc {A : Type} [digraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap dgArc ![a0, a1]

/-- There is an edge between `a` and `b`: the arc relation read
symmetrically, which is how the undirected problem reads its instance. -/
def DGEdge (a b : A) : Prop := DGArc a b ∨ DGArc b a

variable (A) in
/-- A digraph is a yes-instance of DIRECTED HAMILTON CIRCUIT when its arcs
carry a tour of the universe. -/
def HasDirHamCircuit : Prop := Finite A ∧ TourOn (DGArc (A := A))

variable (A) in
/-- A graph is a yes-instance of HAMILTON CIRCUIT when its edges – the arcs
read symmetrically – carry a tour of the universe. -/
def HasHamCircuit : Prop := Finite A ∧ TourOn (DGEdge (A := A))

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasHamCircuit` is isomorphism-invariant. -/
axiom hasHamCircuit_iso : ∀ {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B],
  (A ≃[Lax799700.Hamilton.digraph] B) → (HasHamCircuit A ↔ HasHamCircuit B)

/-- The problem HamCircuit: does the structure satisfy `HasHamCircuit`? -/
def HamCircuit : DecisionProblem Lax799700.Hamilton.digraph :=
  DecisionProblem.ofPred HasHamCircuit

/-- The yes-instances of HamCircuit are exactly the structures satisfying `HasHamCircuit`. -/
axiom hamCircuit_iff : ∀ (A : Type) [Lax799700.Hamilton.digraph.Structure A], HamCircuit A ↔ HasHamCircuit A

/-- HamCircuit is NP-complete. -/
axiom hamCircuit_NP_complete : NP.Complete HamCircuit

/-- The property `HasDirHamCircuit` is isomorphism-invariant. -/
axiom hasDirHamCircuit_iso : ∀ {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B],
  (A ≃[Lax799700.Hamilton.digraph] B) → (HasDirHamCircuit A ↔ HasDirHamCircuit B)

/-- The problem DirHamCircuit: does the structure satisfy `HasDirHamCircuit`? -/
def DirHamCircuit : DecisionProblem Lax799700.Hamilton.digraph :=
  DecisionProblem.ofPred HasDirHamCircuit

/-- The yes-instances of DirHamCircuit are exactly the structures satisfying `HasDirHamCircuit`. -/
axiom dirHamCircuit_iff : ∀ (A : Type) [Lax799700.Hamilton.digraph.Structure A], DirHamCircuit A ↔ HasDirHamCircuit A

/-- DirHamCircuit is NP-complete. -/
axiom dirHamCircuit_NP_complete : NP.Complete DirHamCircuit

end Lax799700.Hamilton
