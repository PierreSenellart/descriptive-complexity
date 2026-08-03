/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.GraphIso
import DescriptiveComplexity.Problems.Feedback.Defs

/-!
# DAG Isomorphism: vocabulary and semantics

DAG ISOMORPHISM: are the two directed acyclic graphs of the instance
isomorphic? This file fixes the vocabulary and the yes-instance predicate; the
two halves of GI-completeness live in
`DescriptiveComplexity.Problems.DagIso.ToGraphIso` and
`DescriptiveComplexity.Problems.DagIso.FromGraphIso`.

## Why the instances carry a topological order

Acyclicity is **not first-order definable**, so a problem whose yes-instances
are “both sides acyclic *and* isomorphic” could not be reduced back to
`DescriptiveComplexity.GraphIso`: the reduction would have to decide acyclicity
first-order, and no first-order interpretation can (a directed cycle is a
reachability question). A classical polynomial-time reduction simply tests
acyclicity and maps a cyclic instance to a fixed no-instance; an FO reduction,
computable in AC⁰, cannot.

The instances therefore *carry* their acyclicity witness: besides the two arc
relations, each side has a relation asked to be a strict partial order
containing its arcs (`DescriptiveComplexity.TopoOn`) – a topological order of
the DAG, in the partial-order form, which is exactly what
`DescriptiveComplexity.acyclicRel_iff_exists_order` certifies acyclicity by.
Being a strict partial order containing the arcs is first-order, so a reduction
*can* test it, and the well-formed instances are precisely the pairs of DAGs
(`DescriptiveComplexity.acyclicOn_iff_exists_topoOn`: a finite relation admits
such a witness exactly when it is acyclic). The witness is data of the
instance, not of the problem: the isomorphism asked for by
`DescriptiveComplexity.HasDagIso` relates the *arcs* only and may ignore the two
orders entirely, so this is DAG isomorphism and not isomorphism of ordered
DAGs.

This is the same “junk is ignorable” discipline as everywhere in the catalog,
one level up: elements outside both marks are junk, and instances whose order
relation is not a witness are no-instances.
-/

/- The language of two-DAG structures lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.twoGraphs`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of two directed acyclic graphs. -/
inductive twoDagsRel : ℕ → Type
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
protected def twoDags : Language :=
  ⟨fun _ => Empty, twoDagsRel⟩
  deriving IsRelational

/-- The pattern-vertex symbol. -/
abbrev tdPatV : Language.twoDags.Relations 1 := .patV

/-- The host-vertex symbol. -/
abbrev tdHostV : Language.twoDags.Relations 1 := .hostV

/-- The pattern-arc symbol. -/
abbrev tdPatArc : Language.twoDags.Relations 2 := .patArc

/-- The host-arc symbol. -/
abbrev tdHostArc : Language.twoDags.Relations 2 := .hostArc

/-- The pattern's topological-order symbol. -/
abbrev tdPatLt : Language.twoDags.Relations 2 := .patLt

/-- The host's topological-order symbol. -/
abbrev tdHostLt : Language.twoDags.Relations 2 := .hostLt

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The acyclicity witness -/

section Topo

variable {A : Type}

/-- `Lt` is a topological order for the arcs `Arc` on the marked set `V`: a
strict partial order (on `V`) containing the arcs. Its existence is exactly the
acyclicity of the arcs (`DescriptiveComplexity.acyclicOn_iff_exists_topoOn`),
and it is first-order checkable, which acyclicity itself is not. -/
def TopoOn (V : A → Prop) (Lt Arc : A → A → Prop) : Prop :=
  (∀ x, V x → ¬Lt x x) ∧
    (∀ x y z, V x → V y → V z → Lt x y → Lt y z → Lt x z) ∧
    ∀ x y, V x → V y → Arc x y → Lt x y

variable {B : Type}

/-- `TopoOn` transports along an equivalence commuting with the three
predicates. -/
theorem TopoOn.of_equiv (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b'))
    (h : TopoOn VB LtB ArcB) : TopoOn VA LtA ArcA := by
  obtain ⟨hirr, htrans, hmono⟩ := h
  refine ⟨fun x hx hlt => ?_, fun x y z hx hy hz h₁ h₂ => ?_, fun x y hx hy harc => ?_⟩
  · exact hirr (u.symm x) ((hV _).mpr (by simpa using hx)) ((hLt _ _).mpr (by simpa using hlt))
  · have := htrans (u.symm x) (u.symm y) (u.symm z) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hV _).mpr (by simpa using hz))
      ((hLt _ _).mpr (by simpa using h₁)) ((hLt _ _).mpr (by simpa using h₂))
    simpa using (hLt (u.symm x) (u.symm z)).mp this
  · have := hmono (u.symm x) (u.symm y) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hArc _ _).mpr (by simpa using harc))
    simpa using (hLt (u.symm x) (u.symm y)).mp this

/-- `TopoOn` transports along an equivalence, iff version. -/
theorem TopoOn.equiv_iff (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b')) :
    TopoOn VB LtB ArcB ↔ TopoOn VA LtA ArcA :=
  ⟨TopoOn.of_equiv u hV hLt hArc,
    TopoOn.of_equiv u.symm (fun a => by rw [hV]; simp) (fun a a' => by rw [hLt]; simp)
      fun a a' => by rw [hArc]; simp⟩

/-- **The well-formed instances are exactly the DAGs**: the arcs of a marked
set admit a topological order precisely when they are acyclic on it. Left to
right a cycle would give `Lt x x`; right to left the transitive closure is the
order (`DescriptiveComplexity.acyclicRel_iff_exists_order`, on the subtype of
marked elements).

This is why carrying the witness costs no generality: every DAG is a
yes-instance-shaped instance, and no other structure is. -/
theorem acyclicOn_iff_exists_topoOn (V : A → Prop) (Arc : A → A → Prop) :
    AcyclicRel (fun x y : {x : A // V x} => Arc x.1 y.1) ↔
      ∃ Lt : A → A → Prop, TopoOn V Lt Arc := by
  constructor
  · intro hac
    obtain ⟨Lt, htrans, hirr, hmono⟩ := (acyclicRel_iff_exists_order _).mp hac
    exact ⟨fun x y => ∃ (hx : V x) (hy : V y), Lt ⟨x, hx⟩ ⟨y, hy⟩,
      fun x _ ⟨hx₁, _, hlt⟩ => hirr ⟨x, hx₁⟩ hlt,
      fun x _ z hx _ hz ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => ⟨hx, hz, htrans _ _ _ h₁ h₂⟩,
      fun x y hx hy harc => ⟨hx, hy, hmono ⟨x, hx⟩ ⟨y, hy⟩ harc⟩⟩
  · rintro ⟨Lt, hirr, htrans, hmono⟩
    refine (acyclicRel_iff_exists_order _).mpr
      ⟨fun x y => Lt x.1 y.1, fun x y z h₁ h₂ => htrans _ _ _ x.2 y.2 z.2 h₁ h₂,
        fun x => hirr x.1 x.2, fun a b h => hmono _ _ a.2 b.2 h⟩

end Topo

/-! ### The problem -/

section Shorthands

variable {A : Type} [Language.twoDags.Structure A]

/-- Being a vertex of the pattern DAG. -/
def TDPatV (a : A) : Prop := RelMap tdPatV ![a]

/-- Being a vertex of the host DAG. -/
def TDHostV (a : A) : Prop := RelMap tdHostV ![a]

/-- An arc of the pattern DAG. -/
def TDPatArc (a b : A) : Prop := RelMap tdPatArc ![a, b]

/-- An arc of the host DAG. -/
def TDHostArc (a b : A) : Prop := RelMap tdHostArc ![a, b]

/-- The pattern's topological order. -/
def TDPatLt (a b : A) : Prop := RelMap tdPatLt ![a, b]

/-- The host's topological order. -/
def TDHostLt (a b : A) : Prop := RelMap tdHostLt ![a, b]

end Shorthands

section Problem

variable (A : Type) [Language.twoDags.Structure A]

/-- Both sides are well-formed – each order relation is a topological order of
its arcs, so both marked arc relations are acyclic – and the two DAGs are
isomorphic. The isomorphism relates the arcs only: the two orders are the
instance's acyclicity witnesses, not part of the structure being matched. -/
def HasDagIso : Prop :=
  Finite A ∧ TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
    TopoOn (TDHostV (A := A)) TDHostLt TDHostArc ∧
    GraphIsoOn (TDPatV (A := A)) TDHostV TDPatArc TDHostArc

end Problem

section Iso

variable {A B : Type} [Language.twoDags.Structure A] [Language.twoDags.Structure B]

/-- The DAG-isomorphism property is isomorphism-invariant. -/
theorem hasDagIso_iso (e : A ≃[Language.twoDags] B) :
    HasDagIso A ↔ HasDagIso B :=
  and_congr e.toEquiv.finite_iff
    (and_congr
      (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdPatV a)
        (fun a b => relMap_equiv₂ e tdPatLt a b) fun a b => relMap_equiv₂ e tdPatArc a b)
      (and_congr
        (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdHostV a)
          (fun a b => relMap_equiv₂ e tdHostLt a b) fun a b => relMap_equiv₂ e tdHostArc a b)
        (GraphIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdPatV a)
          (fun a => relMap_equiv₁ e tdHostV a) (fun a b => relMap_equiv₂ e tdPatArc a b)
          fun a b => relMap_equiv₂ e tdHostArc a b)))

end Iso

/-- DAG ISOMORPHISM, as a problem on two-DAG structures: are the two marked
DAGs isomorphic? Well-formedness – each side's order relation being a
topological order of its arcs – is part of the yes-condition, and is
first-order, unlike acyclicity itself. -/
def DagIso : DecisionProblem Language.twoDags where
  Holds := fun A inst => @HasDagIso A inst
  iso_invariant := fun e => hasDagIso_iso e

end DescriptiveComplexity
