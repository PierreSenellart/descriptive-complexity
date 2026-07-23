/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel
import DescriptiveComplexity.Interpretation

/-!
# Hamilton circuits: definitions

DIRECTED HAMILTON CIRCUIT and (undirected) HAMILTON CIRCUIT
([Karp 1972][karp1972reducibility]): does a graph have a circuit visiting
every vertex exactly once? Both live on the same vocabulary
`FirstOrder.Language.digraph`, a single binary relation `arc`; the undirected
problem reads that relation *symmetrically*
(`DescriptiveComplexity.DGEdge`), which is the honest reading of an undirected
graph presented by a possibly asymmetric edge relation.

## A circuit is a linear order

A Hamilton circuit is a cyclic enumeration of the universe, and cutting it
anywhere turns it into a **linear order whose consecutive elements are
adjacent and whose last element is adjacent to its first**
(`DescriptiveComplexity.TourOn`). That reading is what makes the problem `Σ₁`: a
relation is what an existential second-order block can guess, and “being a
linear order”, “being the immediate successor” and the two adjacency demands
are first-order. It is the same device the job-sequencing certificate uses for
its schedule, one dimension down: there the order is a *sequence* of the
universe, here it is a *cycle* of it.

On the empty universe every condition is vacuous, so the empty graph counts as
a yes-instance; on a one-element universe the wrap-around demand becomes a
self-loop, which is the usual convention.
-/

/- The language of digraphs lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of digraphs. -/
inductive digraphRel : ℕ → Type
  /-- `arc a b`: there is an arc from `a` to `b`. -/
  | arc : digraphRel 2
  deriving DecidableEq

/-- The relational language of digraphs: one binary relation. The undirected
problem reads it symmetrically rather than on a vocabulary of its own. -/
protected def digraph : Language :=
  ⟨fun _ => Empty, digraphRel⟩
  deriving IsRelational

/-- The arc symbol of digraphs. -/
abbrev dgArc : Language.digraph.Relations 2 := .arc

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Tours of a relation -/

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

variable {B : Type}

/-- Being the immediate successor transports along an equivalence. -/
theorem succOf_equiv (u : A ≃ B) {Le : A → A → Prop} {x y : A} :
    SuccOf (fun b b' => Le (u.symm b) (u.symm b')) (u x) (u y) ↔ SuccOf Le x y := by
  simp only [SuccOf, Equiv.symm_apply_apply]
  refine and_congr Iff.rfl (and_congr ⟨fun h he => h (congrArg u he), fun h he => h ?_⟩ ?_)
  · simpa using congrArg u.symm he
  · constructor
    · intro h z h₁ h₂
      have := h (u z) (by simpa using h₁) (by simpa using h₂)
      simpa using this.imp (congrArg u.symm) (congrArg u.symm)
    · intro h z h₁ h₂
      have := h (u.symm z) h₁ h₂
      exact this.imp (fun hz => by simpa using congrArg u hz) fun hz => by simpa using congrArg u hz

/-- Having a tour transports along an equivalence commuting with the two
relations. -/
theorem tourOn_of_equiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) (h : TourOn RA) : TourOn RB := by
  obtain ⟨Le, hlin, hsucc, hwrap⟩ := h
  refine ⟨fun b b' => Le (u.symm b) (u.symm b'), IsLinOrd.of_equiv u (fun a a' => by simp) hlin,
    fun b b' hb => ?_, fun b b' hb hb' => ?_⟩
  · have h' : SuccOf Le (u.symm b) (u.symm b') := by
      rw [← succOf_equiv u]
      simpa using hb
    simpa using (hR _ _).mp (hsucc _ _ h')
  · have h₁ : ∀ z : A, Le (u.symm b) z := fun z => by simpa using hb (u z)
    have h₂ : ∀ z : A, Le z (u.symm b') := fun z => by simpa using hb' (u z)
    simpa using (hR _ _).mp (hwrap _ _ h₁ h₂)

end Tour

/-! ### The two problems -/

section Problems

variable {A : Type} [Language.digraph.Structure A]

/-- There is an arc from `a` to `b`. -/
def DGArc (a b : A) : Prop := RelMap dgArc ![a, b]

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

section Iso

variable {A B : Type} [Language.digraph.Structure A] [Language.digraph.Structure B]

private theorem dgArc_equiv (e : A ≃[Language.digraph] B) (a a' : A) :
    DGArc a a' ↔ DGArc (e a) (e a') :=
  relMap_equiv₂ e dgArc a a'

private theorem hasDirHamCircuit_of_iso (e : A ≃[Language.digraph] B)
    (h : HasDirHamCircuit A) : HasDirHamCircuit B :=
  ⟨e.toEquiv.finite_iff.mp h.1, tourOn_of_equiv e.toEquiv (dgArc_equiv e) h.2⟩

private theorem hasHamCircuit_of_iso (e : A ≃[Language.digraph] B)
    (h : HasHamCircuit A) : HasHamCircuit B :=
  ⟨e.toEquiv.finite_iff.mp h.1,
    tourOn_of_equiv e.toEquiv (fun a a' => or_congr (dgArc_equiv e a a') (dgArc_equiv e a' a)) h.2⟩

/-- Having a directed Hamilton circuit is isomorphism-invariant. -/
theorem hasDirHamCircuit_iso (e : A ≃[Language.digraph] B) :
    HasDirHamCircuit A ↔ HasDirHamCircuit B :=
  ⟨hasDirHamCircuit_of_iso e, hasDirHamCircuit_of_iso e.symm⟩

/-- Having a Hamilton circuit is isomorphism-invariant. -/
theorem hasHamCircuit_iso (e : A ≃[Language.digraph] B) :
    HasHamCircuit A ↔ HasHamCircuit B :=
  ⟨hasHamCircuit_of_iso e, hasHamCircuit_of_iso e.symm⟩

end Iso

/-- DIRECTED HAMILTON CIRCUIT, as a problem on digraphs: is there a circuit
following the arcs and visiting every vertex exactly once? -/
def DirHamCircuit : DecisionProblem Language.digraph where
  Holds := fun A inst => @HasDirHamCircuit A inst
  iso_invariant := fun e => hasDirHamCircuit_iso e

/-- HAMILTON CIRCUIT, as a problem on digraphs read symmetrically: is there a
circuit following the edges and visiting every vertex exactly once? -/
def HamCircuit : DecisionProblem Language.digraph where
  Holds := fun A inst => @HasHamCircuit A inst
  iso_invariant := fun e => hasHamCircuit_iso e

end DescriptiveComplexity
