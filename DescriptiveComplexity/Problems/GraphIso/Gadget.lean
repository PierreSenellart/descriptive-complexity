/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.GadgetDouble

/-!
# The digraph-to-graph gadget

The construction turning a directed graph into a *simple* one with the same
isomorphisms. It is written on a single structure – the doubling that runs it
on both sides of an instance is `DescriptiveComplexity.GadgetDouble` – so
everything below speaks about one graph.

Each vertex `u` gets

* a vertex node `V u`, and
* a **lollipop**: `M₁ u` adjacent to `V u`, with `M₁ u`, `M₂ u`, `M₃ u` a
  triangle.

Each arc `u ⟶ v` gets a path of three subdivision nodes,

```text
  V u — A u v — B u v — C u v — V v
```

together with a **pendant** `P u v` hanging off `A u v`.

Two design points, both forced:

* **Three subdivision nodes, not two.** The source is an arbitrary binary
  relation, so a self-loop `u ⟶ u` is a legal instance; with two subdivisions
  it would close a triangle and wreck the triangle test below, with three it
  closes a 4-cycle.
* **The lollipop.** Without it, a vertex incident to exactly one arc has degree
  one, and is interchangeable with the pendant of that arc – the swap is an
  automorphism, and vertices could not be recovered. With it, every vertex node
  is adjacent to a triangle and no other node is.

The levels are then recovered from adjacency alone, with no counting beyond
"has exactly one neighbour": the triangle nodes are those lying on a triangle,
the vertices those adjacent to one without lying on one, `A` the nodes with a
leaf neighbour, and so on. Points of the tagged power that no clause makes
adjacent to anything – an arc node for a pair that is not an arc – are isolated,
hence harmless: an isomorphism matches them by degree.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace GraphGadget

/-! ### The nodes -/

/-- The eight kinds of node: a vertex, its three lollipop nodes, the three
subdivision nodes of an arc, and the pendant marking the arc's tail. -/
inductive GTag
  /-- The copy of a vertex. -/
  | vtx : GTag
  /-- The lollipop node attached to a vertex. -/
  | m₁ : GTag
  /-- One corner of the lollipop triangle. -/
  | m₂ : GTag
  /-- The other corner of the lollipop triangle. -/
  | m₃ : GTag
  /-- The subdivision node next to an arc's tail. -/
  | a : GTag
  /-- The middle subdivision node of an arc. -/
  | b : GTag
  /-- The subdivision node next to an arc's head. -/
  | c : GTag
  /-- The pendant marking an arc's tail. -/
  | p : GTag
  deriving DecidableEq

instance : Fintype GTag :=
  ⟨{.vtx, .m₁, .m₂, .m₃, .a, .b, .c, .p}, by intro x; cases x <;> simp⟩

instance : Nonempty GTag := ⟨.vtx⟩

/-! ### The defining formula -/

section Formulas

variable {α : Type}

/-- The two coordinates are equal: the point is a vertex-side node, which is
indexed by the diagonal. -/
private def diagF (x₀ x₁ : Language.graph.Term α) : Language.graph.Formula α :=
  Term.equal x₀ x₁

/-- The two coordinates form an arc: the point is an arc-side node. -/
private def arcF (x₀ x₁ : Language.graph.Term α) : Language.graph.Formula α :=
  Relations.formula₂ Language.adj x₀ x₁

/-- The two points carry the same vertex. -/
private def sameVtxF (x₀ y₀ : Language.graph.Term α) : Language.graph.Formula α :=
  Term.equal x₀ y₀

/-- The two points carry the same arc. -/
private def sameArcF (x₀ x₁ y₀ y₁ : Language.graph.Term α) : Language.graph.Formula α :=
  Term.equal x₀ y₀ ⊓ Term.equal x₁ y₁

/-- The edges of the gadget, tag pair by tag pair. Every clause is stated in
both directions, so the result is symmetric; no clause relates a tag to itself
on the same point, so it is irreflexive. -/
def edgeF (t s : GTag) (x₀ x₁ y₀ y₁ : Language.graph.Term α) : Language.graph.Formula α :=
  match t, s with
  -- the lollipop: vertex — m₁, and the triangle m₁ m₂ m₃
  | .vtx, .m₁ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₁, .vtx => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₁, .m₂ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₂, .m₁ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₁, .m₃ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₃, .m₁ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₂, .m₃ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .m₃, .m₂ => diagF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF x₀ y₀
  -- the arc path: tail — a — b — c — head
  | .vtx, .a => diagF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameVtxF x₀ y₀
  | .a, .vtx => arcF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ sameVtxF y₀ x₀
  | .a, .b => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | .b, .a => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | .b, .c => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | .c, .b => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | .c, .vtx => arcF x₀ x₁ ⊓ diagF y₀ y₁ ⊓ Term.equal x₁ y₀
  | .vtx, .c => diagF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ Term.equal y₁ x₀
  -- the pendant marking the tail side
  | .a, .p => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | .p, .a => arcF x₀ x₁ ⊓ arcF y₀ y₁ ⊓ sameArcF x₀ x₁ y₀ y₁
  | _, _ => ⊥

end Formulas

/-- The gadget: a directed graph becomes a simple graph with the same
isomorphisms. Eight tags, dimension two. -/
def gadget : FOInterpretation Language.graph Language.graph GTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
        edgeF (t 0) (t 1) (Term.var (0, 0)) (Term.var (0, 1))
          (Term.var (1, 0)) (Term.var (1, 1))

/-! ### The points -/

section Points

variable {G : Type}

/-- A point of the construction: a tag and two coordinates. The vertex-side
kinds are the diagonal ones. -/
def pt (t : GTag) (u v : G) : gadget.Map G := (t, ![u, v])

/-- The vertex node of a vertex. -/
def vPt (u : G) : gadget.Map G := pt .vtx u u

/-- The lollipop node attached to a vertex. -/
def m₁Pt (u : G) : gadget.Map G := pt .m₁ u u

/-- One corner of a lollipop triangle. -/
def m₂Pt (u : G) : gadget.Map G := pt .m₂ u u

/-- The other corner of a lollipop triangle. -/
def m₃Pt (u : G) : gadget.Map G := pt .m₃ u u

/-- The subdivision node next to an arc's tail. -/
def aPt (u v : G) : gadget.Map G := pt .a u v

/-- The middle subdivision node of an arc. -/
def bPt (u v : G) : gadget.Map G := pt .b u v

/-- The subdivision node next to an arc's head. -/
def cPt (u v : G) : gadget.Map G := pt .c u v

/-- The pendant marking an arc's tail. -/
def pPt (u v : G) : gadget.Map G := pt .p u v

/-- Every point is a named one: one eta lemma for all eight kinds. -/
theorem pt_eta (q : gadget.Map G) : q = pt q.1 (q.2 0) (q.2 1) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> rfl⟩

theorem pt_tag (t : GTag) (u v : G) : (pt t u v).1 = t := rfl

theorem pt_fst (t : GTag) (u v : G) : (pt t u v).2 0 = u := rfl

theorem pt_snd (t : GTag) (u v : G) : (pt t u v).2 1 = v := rfl

end Points

/-! ### Which pairs are edges -/

section Edges

variable {G : Type} [Language.graph.Structure G]

/-- Adjacency in the input digraph. -/
def GAdj (u v : G) : Prop := RelMap Language.adj ![u, v]

/-- Adjacency in the constructed graph. -/
def GEdge (p q : gadget.Map G) : Prop := RelMap Language.adj ![p, q]

@[simp]
theorem edge_vtx_m₁ (u v : G) : GEdge (vPt u) (m₁Pt v) ↔ u = v := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, vPt, m₁Pt, Formula.realize_equal]

@[simp]
theorem edge_m₁_m₂ (u v : G) : GEdge (m₁Pt u) (m₂Pt v) ↔ u = v := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, m₁Pt, m₂Pt, Formula.realize_equal]

@[simp]
theorem edge_m₁_m₃ (u v : G) : GEdge (m₁Pt u) (m₃Pt v) ↔ u = v := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, m₁Pt, m₃Pt, Formula.realize_equal]

@[simp]
theorem edge_m₂_m₃ (u v : G) : GEdge (m₂Pt u) (m₃Pt v) ↔ u = v := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, m₂Pt, m₃Pt, Formula.realize_equal]

@[simp]
theorem edge_vtx_a (w u v : G) : GEdge (vPt w) (aPt u v) ↔ GAdj u v ∧ w = u := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, sameVtxF, vPt, aPt, GAdj, Formula.realize_equal,
    Formula.realize_rel₂]

@[simp]
theorem edge_a_b (u v u' v' : G) :
    GEdge (aPt u v) (bPt u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, aPt, bPt, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_b_c (u v u' v' : G) :
    GEdge (bPt u v) (cPt u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, bPt, cPt, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_c_vtx (u v w : G) : GEdge (cPt u v) (vPt w) ↔ GAdj u v ∧ v = w := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, cPt, vPt, GAdj, Formula.realize_equal,
    Formula.realize_rel₂]

@[simp]
theorem edge_a_p (u v u' v' : G) :
    GEdge (aPt u v) (pPt u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, aPt, pPt, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

/-! ### Which tag pairs can be joined at all -/

/-- The tag pairs the gadget joins: the lollipop's four edges in both
directions, the arc path's four, and the pendant's one. -/
def TagAdj : GTag → GTag → Prop
  | .vtx, .m₁ | .m₁, .vtx | .m₁, .m₂ | .m₂, .m₁ | .m₁, .m₃ | .m₃, .m₁
  | .m₂, .m₃ | .m₃, .m₂ | .vtx, .a | .a, .vtx | .a, .b | .b, .a
  | .b, .c | .c, .b | .c, .vtx | .vtx, .c | .a, .p | .p, .a => True
  | _, _ => False

/-- **An edge joins only the tag pairs the construction lists.** The forty-six
other pairs need no argument: their defining formula is `⊥`, so the hypothesis
*is* `False`. -/
theorem edge_tagAdj {p q : gadget.Map G} (h : GEdge p q) : TagAdj p.1 q.1 := by
  obtain ⟨t, w⟩ := p
  obtain ⟨s, x⟩ := q
  cases t <;> cases s <;> first | exact h.elim | trivial

/-- Nothing joins two vertex nodes, two `m₂`s, and so on: a shorthand for
reading `DescriptiveComplexity.GraphGadget.edge_tagAdj` off a named pair. -/
theorem not_edge_of_not_tagAdj {t s : GTag} (h : ¬TagAdj t s) (u v u' v' : G) :
    ¬GEdge (pt t u v) (pt s u' v') := fun he => h (edge_tagAdj he)

end Edges

end GraphGadget

end DescriptiveComplexity
