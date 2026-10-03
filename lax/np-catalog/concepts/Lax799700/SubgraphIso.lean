import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Subgraph Isomorphism
type: theorem
---
SUBGRAPH ISOMORPHISM: does the host graph contain a subgraph isomorphic
to the pattern graph, that is, is there an injective homomorphism of the
pattern into the host (SubgraphIsoOn)? Non-edges of the pattern are
unconstrained, the standard reading and the one that makes Clique a
special case. An instance carries two graphs in one universe: two unary
marks separate the pattern vertices from the host vertices, and two
binary relations are their adjacencies; elements outside both marks are
junk no condition mentions. Membership is by an existential second-order
definition guessing the map; hardness is a quantifier-free first-order
reduction from Clique, the host being the input graph and the pattern
the complete graph on its marked set.

-/

namespace Lax799700.SubgraphIso

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoGraphsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern graph. -/
  | patV : twoGraphsRel 1
/-- `hostV a`: `a` is a vertex of the host graph. -/
  | hostV : twoGraphsRel 1
/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
  | patE : twoGraphsRel 2
/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
  | hostE : twoGraphsRel 2
  deriving DecidableEq

/-- The relational language of pattern-and-host graphs: two graphs sharing a
universe, each with its own vertex mark and adjacency relation. -/
def twoGraphs : FirstOrder.Language :=
  ⟨fun _ => Empty, twoGraphsRel⟩

instance instIsRelationalTwoGraphs : FirstOrder.Language.IsRelational twoGraphs := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `patV a`: `a` is a vertex of the pattern graph. -/
abbrev tgPatV : twoGraphs.Relations 1 :=
  .patV

/-- `hostV a`: `a` is a vertex of the host graph. -/
abbrev tgHostV : twoGraphs.Relations 1 :=
  .hostV

/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
abbrev tgPatE : twoGraphs.Relations 2 :=
  .patE

/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
abbrev tgHostE : twoGraphs.Relations 2 :=
  .hostE

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

/-- Some map sends the `PV`-vertices injectively into the `HV`-vertices,
carrying `PE`-edges to `HE`-edges: an injective homomorphism of the pattern
into the host. -/
def SubgraphIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    ∀ x y, PV x → PV y → PE x y → HE (f x) (f y)

end Generic

section Problem

section Shorthands

variable {A : Type} [twoGraphs.Structure A]

/-- `patV a`: `a` is a vertex of the pattern graph.  -/
def TGPatV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatV ![a0]

/-- `hostV a`: `a` is a vertex of the host graph.  -/
def TGHostV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostV ![a0]

/-- `patE a b`: there is an edge of the pattern from `a` to `b`.  -/
def TGPatE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatE ![a0, a1]

/-- `hostE a b`: there is an edge of the host from `a` to `b`.  -/
def TGHostE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostE ![a0, a1]

end Shorthands

variable (A : Type) [twoGraphs.Structure A]

/-- The host graph contains a subgraph isomorphic to the pattern graph.
(Finiteness of the universe is required only for uniformity with the rest of
the catalog; the property itself makes sense in general.) -/
def HasSubgraphIso : Prop :=
  Finite A ∧ SubgraphIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSubgraphIso` is isomorphism-invariant. -/
axiom hasSubgraphIso_iso : ∀ {A B : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] [Lax799700.SubgraphIso.twoGraphs.Structure B],
  (A ≃[Lax799700.SubgraphIso.twoGraphs] B) → (HasSubgraphIso A ↔ HasSubgraphIso B)

/-- The problem SubgraphIso: does the structure satisfy `HasSubgraphIso`? -/
def SubgraphIso : DecisionProblem Lax799700.SubgraphIso.twoGraphs :=
  DecisionProblem.ofPred HasSubgraphIso

/-- The yes-instances of SubgraphIso are exactly the structures satisfying `HasSubgraphIso`. -/
axiom subgraphIso_iff : ∀ (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A], SubgraphIso A ↔ HasSubgraphIso A

/-- SubgraphIso is NP-complete. -/
axiom subgraphIso_NP_complete : NP.Complete SubgraphIso

end Lax799700.SubgraphIso
