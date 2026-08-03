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

/-! Every clause of `DescriptiveComplexity.GraphGadget.edgeF`, read on general
points. The coordinates of a neighbour are not known to be diagonal before the
clause is read, so these are the forms the case analysis needs; the diagonal
corollaries follow. -/

@[simp]
theorem edge_vtx_m₁ (u v u' v' : G) :
    GEdge (pt .vtx u v) (pt .m₁ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₁_vtx (u v u' v' : G) :
    GEdge (pt .m₁ u v) (pt .vtx u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₁_m₂ (u v u' v' : G) :
    GEdge (pt .m₁ u v) (pt .m₂ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₂_m₁ (u v u' v' : G) :
    GEdge (pt .m₂ u v) (pt .m₁ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₁_m₃ (u v u' v' : G) :
    GEdge (pt .m₁ u v) (pt .m₃ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₃_m₁ (u v u' v' : G) :
    GEdge (pt .m₃ u v) (pt .m₁ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₂_m₃ (u v u' v' : G) :
    GEdge (pt .m₂ u v) (pt .m₃ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_m₃_m₂ (u v u' v' : G) :
    GEdge (pt .m₃ u v) (pt .m₂ u' v') ↔ u = v ∧ u' = v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, sameVtxF, Formula.realize_equal, and_assoc]

@[simp]
theorem edge_vtx_a (u v u' v' : G) :
    GEdge (pt .vtx u v) (pt .a u' v') ↔ u = v ∧ GAdj u' v' ∧ u = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, sameVtxF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_a_vtx (u v u' v' : G) :
    GEdge (pt .a u v) (pt .vtx u' v') ↔ GAdj u v ∧ u' = v' ∧ u' = u := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, sameVtxF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_c_vtx (u v u' v' : G) :
    GEdge (pt .c u v) (pt .vtx u' v') ↔ GAdj u v ∧ u' = v' ∧ v = u' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_vtx_c (u v u' v' : G) :
    GEdge (pt .vtx u v) (pt .c u' v') ↔ u = v ∧ GAdj u' v' ∧ v' = u := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, diagF, arcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_a_b (u v u' v' : G) :
    GEdge (pt .a u v) (pt .b u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_b_a (u v u' v' : G) :
    GEdge (pt .b u v) (pt .a u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_b_c (u v u' v' : G) :
    GEdge (pt .b u v) (pt .c u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_c_b (u v u' v' : G) :
    GEdge (pt .c u v) (pt .b u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_a_p (u v u' v' : G) :
    GEdge (pt .a u v) (pt .p u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem edge_p_a (u v u' v' : G) :
    GEdge (pt .p u v) (pt .a u' v') ↔ GAdj u v ∧ GAdj u' v' ∧ u = u' ∧ v = v' := by
  rw [GEdge, FOInterpretation.relMap_map]
  simp [gadget, pt, edgeF, arcF, sameArcF, GAdj, Formula.realize_equal,
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

/-- No clause relates a tag to itself, so the construction has no loops. -/
theorem edge_irrefl_pt (t : GTag) (u v : G) : ¬GEdge (pt t u v) (pt t u v) := by
  rw [GEdge, FOInterpretation.relMap_map]
  cases t <;> exact fun h => h.elim

/-! ### The neighbours of each kind of node -/

section Neighbours

/-- The neighbours of a vertex node: its lollipop, the tail-side subdivision of
each arc out of it, and the head-side subdivision of each arc into it. -/
theorem nbr_of_vPt {u : G} {q : gadget.Map G} (h : GEdge (vPt u) q) :
    q = m₁Pt u ∨ (∃ v, GAdj u v ∧ q = aPt u v) ∨ ∃ w, GAdj w u ∧ q = cPt w u := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (vPt u) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (vPt u) z) hq) h
  rw [hq]
  cases s
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, hx, hu⟩ := (edge_vtx_m₁ u u (x 0) (x 1)).mp h'
    exact Or.inl (by rw [m₁Pt, ← hu, ← hx, ← hu])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, harc, hu⟩ := (edge_vtx_a u u (x 0) (x 1)).mp h'
    exact Or.inr (Or.inl ⟨x 1, by rw [← hu] at harc; exact harc, by rw [aPt, ← hu]⟩)
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, harc, hv⟩ := (edge_vtx_c u u (x 0) (x 1)).mp h'
    exact Or.inr (Or.inr ⟨x 0, by rw [hv] at harc; exact harc, by rw [cPt, ← hv]⟩)
  · exact (edge_tagAdj h).elim

theorem nbr_of_m₁Pt {u : G} {q : gadget.Map G} (h : GEdge (m₁Pt u) q) :
    q = vPt u ∨ q = m₂Pt u ∨ q = m₃Pt u := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (m₁Pt u) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (m₁Pt u) z) hq) h
  rw [hq]
  cases s
  · obtain ⟨-, hx, hu⟩ := (edge_m₁_vtx u u (x 0) (x 1)).mp h'
    exact Or.inl (by rw [vPt, ← hu, ← hx, ← hu])
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, hx, hu⟩ := (edge_m₁_m₂ u u (x 0) (x 1)).mp h'
    exact Or.inr (Or.inl (by rw [m₂Pt, ← hu, ← hx, ← hu]))
  · obtain ⟨-, hx, hu⟩ := (edge_m₁_m₃ u u (x 0) (x 1)).mp h'
    exact Or.inr (Or.inr (by rw [m₃Pt, ← hu, ← hx, ← hu]))
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim


theorem nbr_of_m₂Pt {u : G} {q : gadget.Map G} (h : GEdge (m₂Pt u) q) :
    q = m₁Pt u ∨ q = m₃Pt u := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (m₂Pt u) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (m₂Pt u) z) hq) h
  rw [hq]
  cases s
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, hx, hu⟩ := (edge_m₂_m₁ u u (x 0) (x 1)).mp h'
    exact Or.inl (by rw [m₁Pt, ← hu, ← hx, ← hu])
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, hx, hu⟩ := (edge_m₂_m₃ u u (x 0) (x 1)).mp h'
    exact Or.inr (by rw [m₃Pt, ← hu, ← hx, ← hu])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim


theorem nbr_of_m₃Pt {u : G} {q : gadget.Map G} (h : GEdge (m₃Pt u) q) :
    q = m₁Pt u ∨ q = m₂Pt u := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (m₃Pt u) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (m₃Pt u) z) hq) h
  rw [hq]
  cases s
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, hx, hu⟩ := (edge_m₃_m₁ u u (x 0) (x 1)).mp h'
    exact Or.inl (by rw [m₁Pt, ← hu, ← hx, ← hu])
  · obtain ⟨-, hx, hu⟩ := (edge_m₃_m₂ u u (x 0) (x 1)).mp h'
    exact Or.inr (by rw [m₂Pt, ← hu, ← hx, ← hu])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim


theorem nbr_of_aPt {u v : G} {q : gadget.Map G} (h : GEdge (aPt u v) q) :
    q = vPt u ∨ q = bPt u v ∨ q = pPt u v := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (aPt u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (aPt u v) z) hq) h
  rw [hq]
  cases s
  · obtain ⟨-, hx, hu⟩ := (edge_a_vtx u v (x 0) (x 1)).mp h'
    exact Or.inl (by rw [vPt, hu, ← hx, hu])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_a_b u v (x 0) (x 1)).mp h'
    exact Or.inr (Or.inl (by rw [bPt, h0, h1]))
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_a_p u v (x 0) (x 1)).mp h'
    exact Or.inr (Or.inr (by rw [pPt, h0, h1]))


theorem nbr_of_bPt {u v : G} {q : gadget.Map G} (h : GEdge (bPt u v) q) :
    q = aPt u v ∨ q = cPt u v := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (bPt u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (bPt u v) z) hq) h
  rw [hq]
  cases s
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_b_a u v (x 0) (x 1)).mp h'
    exact Or.inl (by rw [aPt, h0, h1])
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_b_c u v (x 0) (x 1)).mp h'
    exact Or.inr (by rw [cPt, h0, h1])
  · exact (edge_tagAdj h).elim


theorem nbr_of_cPt {u v : G} {q : gadget.Map G} (h : GEdge (cPt u v) q) :
    q = bPt u v ∨ q = vPt v := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (cPt u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (cPt u v) z) hq) h
  rw [hq]
  cases s
  · obtain ⟨-, hx, hv⟩ := (edge_c_vtx u v (x 0) (x 1)).mp h'
    exact Or.inr (by rw [vPt, ← hv, ← hx, ← hv])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_c_b u v (x 0) (x 1)).mp h'
    exact Or.inl (by rw [bPt, h0, h1])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim


theorem nbr_of_pPt {u v : G} {q : gadget.Map G} (h : GEdge (pPt u v) q) :
    q = aPt u v := by
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have h' : GEdge (pPt u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pPt u v) z) hq) h
  rw [hq]
  cases s
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · obtain ⟨-, -, h0, h1⟩ := (edge_p_a u v (x 0) (x 1)).mp h'
    exact (by rw [aPt, h0, h1])
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim
  · exact (edge_tagAdj h).elim

end Neighbours

/-! ### The structural predicates that recover the levels -/

section Levels

/-- Lying on a triangle. -/
def OnTri (p : gadget.Map G) : Prop := ∃ q r, GEdge p q ∧ GEdge q r ∧ GEdge r p

/-- Being adjacent to a node that lies on a triangle. -/
def AdjTri (p : gadget.Map G) : Prop := ∃ q, GEdge p q ∧ OnTri q

/-- Having exactly one neighbour. -/
def Leaf (p : gadget.Map G) : Prop := ∃ q, GEdge p q ∧ ∀ r, GEdge p r → r = q

/-- Having a neighbour with exactly one neighbour. -/
def HasLeafNbr (p : gadget.Map G) : Prop := ∃ q, GEdge p q ∧ Leaf q

/-- The lollipop triangle is a triangle. -/
theorem onTri_m₁Pt (u : G) : OnTri (m₁Pt u) :=
  ⟨m₂Pt u, m₃Pt u, (edge_m₁_m₂ u u u u).mpr ⟨rfl, rfl, rfl⟩,
    (edge_m₂_m₃ u u u u).mpr ⟨rfl, rfl, rfl⟩, (edge_m₃_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩⟩

/-- A vertex node lies on no triangle: no two of its neighbours are joined. -/
theorem not_onTri_vPt (u : G) : ¬OnTri (vPt u) := by
  rintro ⟨q, r, hpq, hqr, hrp⟩
  rcases nbr_of_vPt hpq with rfl | ⟨v, -, rfl⟩ | ⟨w, -, rfl⟩
  · rcases nbr_of_m₁Pt hqr with rfl | rfl | rfl
    · exact edge_irrefl_pt _ _ _ hrp
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim
  · rcases nbr_of_aPt hqr with rfl | rfl | rfl
    · exact edge_irrefl_pt _ _ _ hrp
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim
  · rcases nbr_of_cPt hqr with rfl | rfl
    · exact (edge_tagAdj hrp).elim
    · exact edge_irrefl_pt _ _ _ hrp

/-- A tail-side subdivision node lies on no triangle. -/
theorem not_onTri_aPt (u v : G) : ¬OnTri (aPt u v) := by
  rintro ⟨q, r, hpq, hqr, hrp⟩
  rcases nbr_of_aPt hpq with rfl | rfl | rfl
  · rcases nbr_of_vPt hqr with rfl | ⟨v', -, rfl⟩ | ⟨w, -, rfl⟩
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim
  · rcases nbr_of_bPt hqr with rfl | rfl
    · exact edge_irrefl_pt _ _ _ hrp
    · exact (edge_tagAdj hrp).elim
  · rcases nbr_of_pPt hqr with rfl
    · exact edge_irrefl_pt _ _ _ hrp

/-- A middle subdivision node lies on no triangle. -/
theorem not_onTri_bPt (u v : G) : ¬OnTri (bPt u v) := by
  rintro ⟨q, r, hpq, hqr, hrp⟩
  rcases nbr_of_bPt hpq with rfl | rfl
  · rcases nbr_of_aPt hqr with rfl | rfl | rfl
    · exact (edge_tagAdj hrp).elim
    · exact edge_irrefl_pt _ _ _ hrp
    · exact (edge_tagAdj hrp).elim
  · rcases nbr_of_cPt hqr with rfl | rfl
    · exact edge_irrefl_pt _ _ _ hrp
    · exact (edge_tagAdj hrp).elim

/-- A head-side subdivision node lies on no triangle. -/
theorem not_onTri_cPt (u v : G) : ¬OnTri (cPt u v) := by
  rintro ⟨q, r, hpq, hqr, hrp⟩
  rcases nbr_of_cPt hpq with rfl | rfl
  · rcases nbr_of_bPt hqr with rfl | rfl
    · exact (edge_tagAdj hrp).elim
    · exact edge_irrefl_pt _ _ _ hrp
  · rcases nbr_of_vPt hqr with rfl | ⟨v', -, rfl⟩ | ⟨w, -, rfl⟩
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim
    · exact (edge_tagAdj hrp).elim

/-- A pendant lies on no triangle. -/
theorem not_onTri_pPt (u v : G) : ¬OnTri (pPt u v) := by
  rintro ⟨q, r, hpq, hqr, hrp⟩
  rcases nbr_of_pPt hpq with rfl
  rcases nbr_of_aPt hqr with rfl | rfl | rfl
  · exact (edge_tagAdj hrp).elim
  · exact (edge_tagAdj hrp).elim
  · exact edge_irrefl_pt _ _ _ hrp

/-! ### Junk points are isolated

A point whose coordinates do not fit its tag – a lollipop node off the
diagonal, a subdivision node on a pair that is not an arc – is joined to
nothing, so an isomorphism can only match it with another such point. This is
what lets the recovery below case over *all* points rather than only the
well-formed ones. -/

/-- A `vtx` node off the diagonal is isolated. -/
theorem isolated_vtx {u v : G} (h : ¬u = v) (q : gadget.Map G) :
    ¬GEdge (pt .vtx u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .vtx u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .vtx u v) z) hq) he
  cases s
  · exact (edge_tagAdj he).elim
  · exact h ((edge_vtx_m₁ u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact h ((edge_vtx_a u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact h ((edge_vtx_c u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim

/-- A `m₁` node off the diagonal is isolated. -/
theorem isolated_m₁ {u v : G} (h : ¬u = v) (q : gadget.Map G) :
    ¬GEdge (pt .m₁ u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .m₁ u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .m₁ u v) z) hq) he
  cases s
  · exact h ((edge_m₁_vtx u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact h ((edge_m₁_m₂ u v (x 0) (x 1)).mp he').1
  · exact h ((edge_m₁_m₃ u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim

/-- A `m₂` node off the diagonal is isolated. -/
theorem isolated_m₂ {u v : G} (h : ¬u = v) (q : gadget.Map G) :
    ¬GEdge (pt .m₂ u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .m₂ u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .m₂ u v) z) hq) he
  cases s
  · exact (edge_tagAdj he).elim
  · exact h ((edge_m₂_m₁ u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact h ((edge_m₂_m₃ u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim

/-- A `m₃` node off the diagonal is isolated. -/
theorem isolated_m₃ {u v : G} (h : ¬u = v) (q : gadget.Map G) :
    ¬GEdge (pt .m₃ u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .m₃ u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .m₃ u v) z) hq) he
  cases s
  · exact (edge_tagAdj he).elim
  · exact h ((edge_m₃_m₁ u v (x 0) (x 1)).mp he').1
  · exact h ((edge_m₃_m₂ u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim

/-- An `a` node on a pair that is not an arc is isolated. -/
theorem isolated_a {u v : G} (h : ¬GAdj u v) (q : gadget.Map G) :
    ¬GEdge (pt .a u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .a u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .a u v) z) hq) he
  cases s
  · exact h ((edge_a_vtx u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact h ((edge_a_b u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact h ((edge_a_p u v (x 0) (x 1)).mp he').1

/-- An `b` node on a pair that is not an arc is isolated. -/
theorem isolated_b {u v : G} (h : ¬GAdj u v) (q : gadget.Map G) :
    ¬GEdge (pt .b u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .b u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .b u v) z) hq) he
  cases s
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact h ((edge_b_a u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact h ((edge_b_c u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim

/-- An `c` node on a pair that is not an arc is isolated. -/
theorem isolated_c {u v : G} (h : ¬GAdj u v) (q : gadget.Map G) :
    ¬GEdge (pt .c u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .c u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .c u v) z) hq) he
  cases s
  · exact h ((edge_c_vtx u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact h ((edge_c_b u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim

/-- An `p` node on a pair that is not an arc is isolated. -/
theorem isolated_p {u v : G} (h : ¬GAdj u v) (q : gadget.Map G) :
    ¬GEdge (pt .p u v) q := by
  intro he
  obtain ⟨s, x⟩ := q
  have hq : ((s, x) : gadget.Map G) = pt s (x 0) (x 1) := pt_eta _
  have he' : GEdge (pt .p u v) (pt s (x 0) (x 1)) :=
    Eq.mp (congrArg (fun z => GEdge (pt .p u v) z) hq) he
  cases s
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact h ((edge_p_a u v (x 0) (x 1)).mp he').1
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim
  · exact (edge_tagAdj he).elim

/-! ### Adjacency to a triangle: the vertices -/

/-- A vertex node is adjacent to its lollipop. -/
theorem adjTri_vPt (u : G) : AdjTri (vPt u) :=
  ⟨m₁Pt u, (edge_vtx_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩, onTri_m₁Pt u⟩

/-- No subdivision node is adjacent to a triangle. -/
theorem not_adjTri_aPt (u v : G) : ¬AdjTri (aPt u v) := by
  rintro ⟨q, hq, htri⟩
  rcases nbr_of_aPt hq with rfl | rfl | rfl
  · exact not_onTri_vPt u htri
  · exact not_onTri_bPt u v htri
  · exact not_onTri_pPt u v htri

@[inherit_doc not_adjTri_aPt]
theorem not_adjTri_bPt (u v : G) : ¬AdjTri (bPt u v) := by
  rintro ⟨q, hq, htri⟩
  rcases nbr_of_bPt hq with rfl | rfl
  · exact not_onTri_aPt u v htri
  · exact not_onTri_cPt u v htri

@[inherit_doc not_adjTri_aPt]
theorem not_adjTri_cPt (u v : G) : ¬AdjTri (cPt u v) := by
  rintro ⟨q, hq, htri⟩
  rcases nbr_of_cPt hq with rfl | rfl
  · exact not_onTri_bPt u v htri
  · exact not_onTri_vPt v htri

@[inherit_doc not_adjTri_aPt]
theorem not_adjTri_pPt (u v : G) : ¬AdjTri (pPt u v) := by
  rintro ⟨q, hq, htri⟩
  rcases nbr_of_pPt hq with rfl
  exact not_onTri_aPt u v htri

/-- The other two corners of a lollipop lie on its triangle too. -/
theorem onTri_m₂Pt (u : G) : OnTri (m₂Pt u) :=
  ⟨m₃Pt u, m₁Pt u, (edge_m₂_m₃ u u u u).mpr ⟨rfl, rfl, rfl⟩,
    (edge_m₃_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩, (edge_m₁_m₂ u u u u).mpr ⟨rfl, rfl, rfl⟩⟩

@[inherit_doc onTri_m₂Pt]
theorem onTri_m₃Pt (u : G) : OnTri (m₃Pt u) :=
  ⟨m₁Pt u, m₂Pt u, (edge_m₃_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩,
    (edge_m₁_m₂ u u u u).mpr ⟨rfl, rfl, rfl⟩, (edge_m₂_m₃ u u u u).mpr ⟨rfl, rfl, rfl⟩⟩

/-- **The vertices are recoverable from adjacency alone**: they are the nodes
adjacent to a triangle without lying on one. Junk points fail the test by being
isolated, lollipop nodes by lying on their triangle, and subdivision nodes and
pendants by touching no triangle. -/
theorem vertex_iff (p : gadget.Map G) : (¬OnTri p ∧ AdjTri p) ↔ ∃ u, p = vPt u := by
  constructor
  · rintro ⟨hnt, q, hq, htri⟩
    obtain ⟨t, x⟩ := p
    have hp : ((t, x) : gadget.Map G) = pt t (x 0) (x 1) := pt_eta _
    have hq' : GEdge (pt t (x 0) (x 1)) q := Eq.mp (congrArg (fun z => GEdge z q) hp) hq
    have hnt' : ¬OnTri (pt t (x 0) (x 1)) := fun h =>
      hnt (Eq.mp (congrArg OnTri hp.symm) h)
    rw [hp]
    cases t
    · by_cases hd : x 0 = x 1
      · exact ⟨x 0, by rw [vPt, ← hd]⟩
      · exact absurd hq' (isolated_vtx hd q)
    · by_cases hd : x 0 = x 1
      · refine absurd (Eq.mp (congrArg OnTri ?_) (onTri_m₁Pt (x 0))) hnt'
        rw [m₁Pt, hd]
      · exact absurd hq' (isolated_m₁ hd q)
    · by_cases hd : x 0 = x 1
      · refine absurd (Eq.mp (congrArg OnTri ?_) (onTri_m₂Pt (x 0))) hnt'
        rw [m₂Pt, hd]
      · exact absurd hq' (isolated_m₂ hd q)
    · by_cases hd : x 0 = x 1
      · refine absurd (Eq.mp (congrArg OnTri ?_) (onTri_m₃Pt (x 0))) hnt'
        rw [m₃Pt, hd]
      · exact absurd hq' (isolated_m₃ hd q)
    · by_cases hd : GAdj (x 0) (x 1)
      · exact absurd ⟨q, hq', htri⟩ (not_adjTri_aPt (x 0) (x 1))
      · exact absurd hq' (isolated_a hd q)
    · by_cases hd : GAdj (x 0) (x 1)
      · exact absurd ⟨q, hq', htri⟩ (not_adjTri_bPt (x 0) (x 1))
      · exact absurd hq' (isolated_b hd q)
    · by_cases hd : GAdj (x 0) (x 1)
      · exact absurd ⟨q, hq', htri⟩ (not_adjTri_cPt (x 0) (x 1))
      · exact absurd hq' (isolated_c hd q)
    · by_cases hd : GAdj (x 0) (x 1)
      · exact absurd ⟨q, hq', htri⟩ (not_adjTri_pPt (x 0) (x 1))
      · exact absurd hq' (isolated_p hd q)
  · rintro ⟨u, rfl⟩
    exact ⟨not_onTri_vPt u, adjTri_vPt u⟩

/-! ### Leaves: the pendant marks the tail -/

/-- The pendant of an arc is a leaf. -/
theorem leaf_pPt {u v : G} (h : GAdj u v) : Leaf (pPt u v) :=
  ⟨aPt u v, (edge_p_a u v u v).mpr ⟨h, h, rfl, rfl⟩, fun _ hr => nbr_of_pPt hr⟩

/-- A middle subdivision node is not a leaf: it has both an `a` and a `c`
neighbour, and those have different tags. -/
theorem not_leaf_bPt {u v : G} (h : GAdj u v) : ¬Leaf (bPt u v) := by
  rintro ⟨q, -, huniq⟩
  have h₁ := huniq (aPt u v) ((edge_b_a u v u v).mpr ⟨h, h, rfl, rfl⟩)
  have h₂ := huniq (cPt u v) ((edge_b_c u v u v).mpr ⟨h, h, rfl, rfl⟩)
  have : (aPt u v).1 = (cPt u v).1 := by rw [h₁, h₂]
  exact absurd this (by simp [aPt, cPt, pt])

/-- A vertex node incident to an arc is not a leaf: it has its lollipop and the
arc's subdivision node. -/
theorem not_leaf_vPt_of_out {u v : G} (h : GAdj u v) : ¬Leaf (vPt u) := by
  rintro ⟨q, -, huniq⟩
  have h₁ := huniq (m₁Pt u) ((edge_vtx_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩)
  have h₂ := huniq (aPt u v) ((edge_vtx_a u u u v).mpr ⟨rfl, h, rfl⟩)
  have : (m₁Pt u).1 = (aPt u v).1 := by rw [h₁, h₂]
  exact absurd this (by simp [m₁Pt, aPt, pt])

@[inherit_doc not_leaf_vPt_of_out]
theorem not_leaf_vPt_of_in {w u : G} (h : GAdj w u) : ¬Leaf (vPt u) := by
  rintro ⟨q, -, huniq⟩
  have h₁ := huniq (m₁Pt u) ((edge_vtx_m₁ u u u u).mpr ⟨rfl, rfl, rfl⟩)
  have h₂ := huniq (cPt w u) ((edge_vtx_c u u w u).mpr ⟨rfl, h, rfl⟩)
  have : (m₁Pt u).1 = (cPt w u).1 := by rw [h₁, h₂]
  exact absurd this (by simp [m₁Pt, cPt, pt])

/-! ### Which nodes have a leaf neighbour: the tail side -/

/-- The tail-side subdivision node has the pendant as a neighbour. -/
theorem hasLeafNbr_aPt {u v : G} (h : GAdj u v) : HasLeafNbr (aPt u v) :=
  ⟨pPt u v, (edge_a_p u v u v).mpr ⟨h, h, rfl, rfl⟩, leaf_pPt h⟩

/-- The head-side subdivision node has none: its neighbours are the middle node
and the head, and the head is incident to this very arc. -/
theorem not_hasLeafNbr_cPt {u v : G} (h : GAdj u v) : ¬HasLeafNbr (cPt u v) := by
  rintro ⟨q, hq, hleaf⟩
  rcases nbr_of_cPt hq with rfl | rfl
  · exact not_leaf_bPt h hleaf
  · exact not_leaf_vPt_of_in h hleaf

/-! ### The arcs are recoverable -/

/-- **An arc of the input is a guarded path of length four between the two
vertex nodes.** Each guard rules out a concrete impostor: without `¬OnTri` the
lollipop of an isolated vertex closes the chain, without `¬AdjTri` it turns
back through the vertex node, without `¬Leaf` it goes out to the pendant and
back, and without `¬HasLeafNbr` it returns along the tail-side node – each of
which would claim an arc from a vertex to itself. The direction of the arc is
carried by `HasLeafNbr`: only the tail side has a pendant. -/
theorem arc_iff (u v : G) :
    GAdj u v ↔ ∃ p q r, GEdge (vPt u) p ∧ ¬OnTri p ∧ ¬AdjTri p ∧ HasLeafNbr p ∧
      GEdge p q ∧ ¬OnTri q ∧ ¬AdjTri q ∧ ¬Leaf q ∧
      GEdge q r ∧ ¬OnTri r ∧ ¬HasLeafNbr r ∧ GEdge r (vPt v) := by
  constructor
  · intro h
    exact ⟨aPt u v, bPt u v, cPt u v,
      (edge_vtx_a u u u v).mpr ⟨rfl, h, rfl⟩,
      not_onTri_aPt u v, not_adjTri_aPt u v, hasLeafNbr_aPt h,
      (edge_a_b u v u v).mpr ⟨h, h, rfl, rfl⟩,
      not_onTri_bPt u v, not_adjTri_bPt u v, not_leaf_bPt h,
      (edge_b_c u v u v).mpr ⟨h, h, rfl, rfl⟩,
      not_onTri_cPt u v, not_hasLeafNbr_cPt h,
      (edge_c_vtx u v v v).mpr ⟨h, rfl, rfl⟩⟩
  · rintro ⟨p, q, r, hvp, hntp, hnap, hlp, hpq, hntq, hnaq, hnlq, hqr, hntr, hnlr, hrv⟩
    -- the first step leaves the tail-side subdivision node as the only option
    rcases nbr_of_vPt hvp with rfl | ⟨v', harc, rfl⟩ | ⟨w, harc, rfl⟩
    · exact absurd (onTri_m₁Pt u) hntp
    · -- the second step: neither back to the vertex nor out to the pendant
      rcases nbr_of_aPt hpq with rfl | rfl | rfl
      · exact absurd (adjTri_vPt u) hnaq
      · -- the third step: not back along the tail-side node
        rcases nbr_of_bPt hqr with rfl | rfl
        · exact absurd (hasLeafNbr_aPt harc) hnlr
        · -- the head of the arc is where the chain lands
          obtain ⟨-, -, hv⟩ := (edge_c_vtx u v' v v).mp hrv
          rw [hv] at harc
          exact harc
      · exact absurd (leaf_pPt harc) hnlq
    · exact absurd (not_hasLeafNbr_cPt harc) (fun hn => hn hlp)

end Levels

end Edges

/-! ### An isomorphism of the constructions is one of the inputs -/

section Reflect

variable {G H : Type} [Language.graph.Structure G] [Language.graph.Structure H]
variable (φ : gadget.Map G ≃[Language.graph] gadget.Map H)

/-- An isomorphism preserves and reflects the constructed adjacency. -/
theorem edge_map (p q : gadget.Map G) : GEdge (φ p) (φ q) ↔ GEdge p q := by
  have h := φ.map_rel' Language.adj ![p, q]
  rw [show (φ.toFun ∘ ![p, q]) = ![φ p, φ q] by funext i; fin_cases i <;> rfl] at h
  exact h

theorem edge_map_symm (p q : gadget.Map H) : GEdge (φ.symm p) (φ.symm q) ↔ GEdge p q := by
  have h := edge_map φ (φ.symm p) (φ.symm q)
  rw [φ.apply_symm_apply, φ.apply_symm_apply] at h
  exact h.symm

/-- Lying on a triangle is preserved. -/
theorem onTri_map (p : gadget.Map G) : OnTri (φ p) ↔ OnTri p := by
  constructor
  · rintro ⟨q, r, h₁, h₂, h₃⟩
    refine ⟨φ.symm q, φ.symm r, ?_, ?_, ?_⟩
    · rw [← edge_map_symm φ, φ.symm_apply_apply] at h₁; exact h₁
    · rw [← edge_map_symm φ] at h₂; exact h₂
    · rw [← edge_map_symm φ, φ.symm_apply_apply] at h₃; exact h₃
  · rintro ⟨q, r, h₁, h₂, h₃⟩
    exact ⟨φ q, φ r, (edge_map φ _ _).mpr h₁, (edge_map φ _ _).mpr h₂, (edge_map φ _ _).mpr h₃⟩

/-- Adjacency to a triangle is preserved. -/
theorem adjTri_map (p : gadget.Map G) : AdjTri (φ p) ↔ AdjTri p := by
  constructor
  · rintro ⟨q, h₁, h₂⟩
    refine ⟨φ.symm q, ?_, ?_⟩
    · rw [← edge_map_symm φ, φ.symm_apply_apply] at h₁; exact h₁
    · rw [← onTri_map φ, φ.apply_symm_apply]; exact h₂
  · rintro ⟨q, h₁, h₂⟩
    exact ⟨φ q, (edge_map φ _ _).mpr h₁, (onTri_map φ q).mpr h₂⟩

/-- Being a leaf is preserved: the uniqueness clause transfers because every
neighbour of the image is the image of a neighbour. -/
theorem leaf_map (p : gadget.Map G) : Leaf (φ p) ↔ Leaf p := by
  constructor
  · rintro ⟨q, h₁, h₂⟩
    refine ⟨φ.symm q, ?_, fun r hr => ?_⟩
    · rw [← edge_map_symm φ, φ.symm_apply_apply] at h₁; exact h₁
    · have := h₂ (φ r) ((edge_map φ p r).mpr hr)
      rw [← this, φ.symm_apply_apply]
  · rintro ⟨q, h₁, h₂⟩
    refine ⟨φ q, (edge_map φ _ _).mpr h₁, fun r hr => ?_⟩
    have hr' : GEdge p (φ.symm r) := by
      rw [← edge_map_symm φ, φ.symm_apply_apply] at hr; exact hr
    rw [← h₂ (φ.symm r) hr', φ.apply_symm_apply]

/-- Having a leaf neighbour is preserved. -/
theorem hasLeafNbr_map (p : gadget.Map G) : HasLeafNbr (φ p) ↔ HasLeafNbr p := by
  constructor
  · rintro ⟨q, h₁, h₂⟩
    refine ⟨φ.symm q, ?_, ?_⟩
    · rw [← edge_map_symm φ, φ.symm_apply_apply] at h₁; exact h₁
    · rw [← leaf_map φ, φ.apply_symm_apply]; exact h₂
  · rintro ⟨q, h₁, h₂⟩
    exact ⟨φ q, (edge_map φ _ _).mpr h₁, (leaf_map φ q).mpr h₂⟩

omit [Language.graph.Structure G] in
theorem vPt_injective : Function.Injective (vPt (G := G)) := fun _ _ h =>
  congrArg (fun z : gadget.Map G => z.2 0) h

/-- **The gadget reflects isomorphism**: an isomorphism of the constructed
graphs restricts to the vertex nodes, and the arcs are read off it by
`DescriptiveComplexity.GraphGadget.arc_iff`. Together with functoriality – free
for an interpretation – this says the construction is faithful. -/
theorem gadget_isoReflecting : IsoReflecting gadget := by
  intro G H _ _ _ _ hiso
  obtain ⟨φ⟩ := hiso
  classical
  have hvtx : ∀ u : G, ∃ w : H, φ (vPt u) = vPt w := fun u =>
    (vertex_iff (φ (vPt u))).mp
      ⟨by rw [onTri_map φ]; exact not_onTri_vPt u, by rw [adjTri_map φ]; exact adjTri_vPt u⟩
  choose g hg using hvtx
  have hvtx' : ∀ w : H, ∃ u : G, φ.symm (vPt w) = vPt u := fun w =>
    (vertex_iff (φ.symm (vPt w))).mp
      ⟨by rw [← onTri_map φ, φ.apply_symm_apply]; exact not_onTri_vPt w,
        by rw [← adjTri_map φ, φ.apply_symm_apply]; exact adjTri_vPt w⟩
  choose g' hg' using hvtx'
  have hsymm : ∀ u : G, φ.symm (vPt (g u)) = vPt u := fun u => by
    rw [← hg u, φ.symm_apply_apply]
  have hginj : Function.Injective g := fun u v huv => by
    have : φ (vPt u) = φ (vPt v) := by rw [hg u, hg v, huv]
    exact vPt_injective (φ.injective this)
  have hgsurj : Function.Surjective g := fun w => by
    refine ⟨g' w, vPt_injective ?_⟩
    have : φ (vPt (g' w)) = vPt w := by rw [← hg' w, φ.apply_symm_apply]
    rw [← hg (g' w), this]
  -- the arcs, through the guarded chain on both sides
  have hadj : ∀ u v : G, GAdj u v ↔ GAdj (g u) (g v) := by
    intro u v
    rw [arc_iff, arc_iff]
    constructor
    · rintro ⟨p, q, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨φ p, φ q, φ r, ?_, ?_, ?_, ?_, (edge_map φ _ _).mpr h5, ?_, ?_, ?_,
        (edge_map φ _ _).mpr h9, ?_, ?_, ?_⟩
      · rw [← hg u]; exact (edge_map φ _ _).mpr h1
      · rw [onTri_map φ]; exact h2
      · rw [adjTri_map φ]; exact h3
      · rw [hasLeafNbr_map φ]; exact h4
      · rw [onTri_map φ]; exact h6
      · rw [adjTri_map φ]; exact h7
      · rw [leaf_map φ]; exact h8
      · rw [onTri_map φ]; exact h10
      · rw [hasLeafNbr_map φ]; exact h11
      · rw [← hg v]; exact (edge_map φ _ _).mpr h12
    · rintro ⟨p, q, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨φ.symm p, φ.symm q, φ.symm r, ?_, ?_, ?_, ?_,
        (edge_map_symm φ _ _).mpr h5, ?_, ?_, ?_, (edge_map_symm φ _ _).mpr h9, ?_, ?_, ?_⟩
      · rw [← hsymm u]; exact (edge_map_symm φ _ _).mpr h1
      · rw [← onTri_map φ, φ.apply_symm_apply]; exact h2
      · rw [← adjTri_map φ, φ.apply_symm_apply]; exact h3
      · rw [← hasLeafNbr_map φ, φ.apply_symm_apply]; exact h4
      · rw [← onTri_map φ, φ.apply_symm_apply]; exact h6
      · rw [← adjTri_map φ, φ.apply_symm_apply]; exact h7
      · rw [← leaf_map φ, φ.apply_symm_apply]; exact h8
      · rw [← onTri_map φ, φ.apply_symm_apply]; exact h10
      · rw [← hasLeafNbr_map φ, φ.apply_symm_apply]; exact h11
      · rw [← hsymm v]; exact (edge_map_symm φ _ _).mpr h12
  refine ⟨{ toEquiv := Equiv.ofBijective g ⟨hginj, hgsurj⟩
            map_fun' := fun f => isEmptyElim f
            map_rel' := ?_ }⟩
  intro n r x
  cases r
  rw [show x = ![x 0, x 1] by funext i; fin_cases i <;> rfl]
  rw [show ((Equiv.ofBijective g ⟨hginj, hgsurj⟩).toFun ∘ ![x 0, x 1])
      = ![g (x 0), g (x 1)] by funext i; fin_cases i <;> rfl]
  exact (hadj (x 0) (x 1)).symm

end Reflect

end GraphGadget

end DescriptiveComplexity
