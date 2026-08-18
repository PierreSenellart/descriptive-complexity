/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DagIso.Defs

/-!
# Digraph Isomorphism reduces to DAG Isomorphism

The substantial half of GI-completeness: an arbitrary directed graph is turned
into a DAG whose isomorphisms are exactly the isomorphisms of the graph. Every
arc is subdivided **twice**,

```text
  u  ⟶  a(u,v)  ⟶  b(u,v)  ⟵  v
```

so that the arc `u ⟶ v` becomes a three-level pattern: the tail `u` points at
the middle node `a(u,v)`, which points at the end node `b(u,v)`, which the head
`v` also points at. Subdividing once would not do – with a single node per arc
the two endpoints would be interchangeable and the direction of the arc lost;
here the tail is the vertex pointing at a middle node and the head the vertex
pointing at an end node.

The construction is acyclic by inspection: every arc goes from level 0
(vertices) to level 1 (middle nodes) or level 2 (end nodes), or from level 1 to
level 2. That is also the topological order the instance must carry, and it
needs no formula at all – it is read off the tags
(`DescriptiveComplexity.DagIso.ltF`), which is why the reduction stays
**order-free**: `FirstOrder.Language.twoGraphs` carries its own vertex marks, so
the same gadget runs on the pattern side and on the host side inside a single
interpretation, junk staying unmarked.

The three levels are recovered from the arcs alone, without any counting:
a vertex node is one with no incoming arc, an end node one with an incoming but
no outgoing arc, and a middle node has both
(`DescriptiveComplexity.DagIso.patV_no_in_iff` and its siblings). An
isomorphism of the two DAGs therefore preserves the levels, and reading it on
level 0 gives the isomorphism of the graphs.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DagIso

/-! ### The tags: the three levels of the construction -/

/-- The three kinds of node of the gadget: a vertex, the middle node of an arc,
the end node of an arc. -/
inductive NodeTag
  /-- A copy of a vertex of the input graph (level 0). -/
  | vtx : NodeTag
  /-- The middle node `a(u,v)` of an arc `u ⟶ v` (level 1). -/
  | arcMid : NodeTag
  /-- The end node `b(u,v)` of an arc `u ⟶ v` (level 2). -/
  | arcEnd : NodeTag
  deriving DecidableEq

instance : Fintype NodeTag :=
  ⟨{.vtx, .arcMid, .arcEnd}, by intro x; cases x <;> simp⟩

instance : Nonempty NodeTag := ⟨.vtx⟩

/-! ### The defining formulas -/

section Formulas

variable {α : Type}

/-- Being a node of the gadget, for one side of the instance: a vertex node is
a diagonal pair whose entry is a marked vertex, and an arc node is a pair that
is an arc between two marked vertices. -/
def nodeF (mark : Language.twoGraphs.Relations 1) (adj : Language.twoGraphs.Relations 2)
    (t : NodeTag) (x y : Language.twoGraphs.Term α) : Language.twoGraphs.Formula α :=
  match t with
  | .vtx => Term.equal x y ⊓ Relations.formula₁ mark x
  | .arcMid | .arcEnd =>
      Relations.formula₁ mark x ⊓ Relations.formula₁ mark y ⊓ Relations.formula₂ adj x y

/-- The arcs of the gadget: `u ⟶ a(u,v)`, `a(u,v) ⟶ b(u,v)` and
`v ⟶ b(u,v)`, and nothing else. -/
def arcF (mark : Language.twoGraphs.Relations 1) (adj : Language.twoGraphs.Relations 2)
    (t s : NodeTag) (x₀ x₁ y₀ y₁ : Language.twoGraphs.Term α) :
    Language.twoGraphs.Formula α :=
  match t, s with
  | .vtx, .arcMid =>
      nodeF mark adj .vtx x₀ x₁ ⊓ nodeF mark adj .arcMid y₀ y₁ ⊓ Term.equal x₀ y₀
  | .vtx, .arcEnd =>
      nodeF mark adj .vtx x₀ x₁ ⊓ nodeF mark adj .arcEnd y₀ y₁ ⊓ Term.equal x₀ y₁
  | .arcMid, .arcEnd =>
      nodeF mark adj .arcMid x₀ x₁ ⊓ nodeF mark adj .arcEnd y₀ y₁ ⊓
        (Term.equal x₀ y₀ ⊓ Term.equal x₁ y₁)
  | _, _ => ⊥

/-- The topological order of the gadget: the level of the tag strictly
increases. It mentions no variable at all – the whole point of the three-level
layout. -/
def ltF (t s : NodeTag) : Language.twoGraphs.Formula α :=
  match t, s with
  | .vtx, .arcMid | .vtx, .arcEnd | .arcMid, .arcEnd => ⊤
  | _, _ => ⊥

end Formulas

/-- The interpretation of Digraph Isomorphism into DAG Isomorphism: two
dimensions (an arc is a pair), three tags (the three levels), the same gadget
run on the pattern side and on the host side. -/
def incInterp : FOInterpretation Language.twoGraphs Language.twoDags NodeTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .patV => fun t => nodeF tgPatV tgPatE (t 0) (Term.var (0, 0)) (Term.var (0, 1))
    | _, .hostV => fun t => nodeF tgHostV tgHostE (t 0) (Term.var (0, 0)) (Term.var (0, 1))
    | _, .patArc => fun t =>
        arcF tgPatV tgPatE (t 0) (t 1) (Term.var (0, 0)) (Term.var (0, 1))
          (Term.var (1, 0)) (Term.var (1, 1))
    | _, .hostArc => fun t =>
        arcF tgHostV tgHostE (t 0) (t 1) (Term.var (0, 0)) (Term.var (0, 1))
          (Term.var (1, 0)) (Term.var (1, 1))
    | _, .patLt => fun t => ltF (t 0) (t 1)
    | _, .hostLt => fun t => ltF (t 0) (t 1)

/-! ### The points of the gadget -/

section Points

variable {A : Type}

/-- A point at the vertex level; it is a node only when its two coordinates
agree (`DescriptiveComplexity.DagIso.pat_vPt2`). -/
def vPt2 (u v : A) : incInterp.Map A := (.vtx, ![u, v])

/-- The vertex node of a vertex. -/
def vPt (v : A) : incInterp.Map A := vPt2 v v

/-- The middle node of an arc. -/
def midPt (u v : A) : incInterp.Map A := (.arcMid, ![u, v])

/-- The end node of an arc. -/
def endPt (u v : A) : incInterp.Map A := (.arcEnd, ![u, v])

theorem two_eta (w : Fin 2 → A) : w = ![w 0, w 1] := by
  funext i; fin_cases i <;> rfl

/-- A point of the vertex level, in named form. -/
theorem vtx_eta (w : Fin 2 → A) : ((NodeTag.vtx, w) : incInterp.Map A) = vPt2 (w 0) (w 1) :=
  Prod.ext_iff.mpr ⟨rfl, two_eta w⟩

/-- A point of the middle level, in named form. -/
theorem mid_eta (w : Fin 2 → A) : ((NodeTag.arcMid, w) : incInterp.Map A) = midPt (w 0) (w 1) :=
  Prod.ext_iff.mpr ⟨rfl, two_eta w⟩

/-- A point of the end level, in named form. -/
theorem end_eta (w : Fin 2 → A) : ((NodeTag.arcEnd, w) : incInterp.Map A) = endPt (w 0) (w 1) :=
  Prod.ext_iff.mpr ⟨rfl, two_eta w⟩

theorem vPt_injective : Function.Injective (vPt (A := A)) := fun _ _ h =>
  congrArg (fun p : incInterp.Map A => p.2 0) h

theorem midPt_inj {u v u' v' : A} (h : midPt u v = midPt u' v') : u = u' ∧ v = v' :=
  ⟨congrArg (fun p : incInterp.Map A => p.2 0) h, congrArg (fun p : incInterp.Map A => p.2 1) h⟩

end Points

/-! ### What the gadget builds, on the pattern side -/

section PatternChar

variable {A : Type} [Language.twoGraphs.Structure A]

@[simp]
theorem pat_vPt2 (u v : A) : TDPatV (vPt2 u v) ↔ u = v ∧ TGPatV u := by
  rw [TDPatV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, vPt2, TGPatV, Formula.realize_rel₁, Formula.realize_equal]

@[simp]
theorem pat_vPt (v : A) : TDPatV (vPt v) ↔ TGPatV v := by
  rw [vPt, pat_vPt2]
  simp

@[simp]
theorem pat_midPt (u v : A) :
    TDPatV (midPt u v) ↔ TGPatV u ∧ TGPatV v ∧ TGPatE u v := by
  rw [TDPatV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, midPt, TGPatV, TGPatE, Formula.realize_rel₁, Formula.realize_rel₂,
    and_assoc]

@[simp]
theorem pat_endPt (u v : A) :
    TDPatV (endPt u v) ↔ TGPatV u ∧ TGPatV v ∧ TGPatE u v := by
  rw [TDPatV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, endPt, TGPatV, TGPatE, Formula.realize_rel₁, Formula.realize_rel₂,
    and_assoc]

/-- A pattern node is a vertex node, a middle node or an end node. The
hypothesis is unfolded by `rcases` rather than by `rw`: the defining formula's
realization is definitionally a conjunction, and a pair literal at
`FOInterpretation.Map` type does not match at rewriting transparency. -/
theorem patV_cases {p : incInterp.Map A} (h : TDPatV p) :
    (∃ v, TGPatV v ∧ p = vPt v) ∨
      (∃ u v, (TGPatV u ∧ TGPatV v ∧ TGPatE u v) ∧ p = midPt u v) ∨
      ∃ u v, (TGPatV u ∧ TGPatV v ∧ TGPatE u v) ∧ p = endPt u v := by
  obtain ⟨t, w⟩ := p
  cases t
  · obtain ⟨heq, hmark⟩ := (pat_vPt2 (w 0) (w 1)).mp (Eq.mp (congrArg TDPatV (vtx_eta w)) h)
    exact Or.inl ⟨w 0, hmark, (vtx_eta w).trans (by rw [vPt, heq])⟩
  · exact Or.inr (Or.inl ⟨w 0, w 1,
      (pat_midPt (w 0) (w 1)).mp (Eq.mp (congrArg TDPatV (mid_eta w)) h), mid_eta w⟩)
  · exact Or.inr (Or.inr ⟨w 0, w 1,
      (pat_endPt (w 0) (w 1)).mp (Eq.mp (congrArg TDPatV (end_eta w)) h), end_eta w⟩)

/-- The only arcs are the three of the gadget: the tags of an arc's endpoints
climb the three levels. The six forbidden tag combinations need no argument –
their defining formula is `⊥`, so the hypothesis *is* `False`. -/
theorem pat_arc_tag {p q : incInterp.Map A} (h : TDPatArc p q) :
    (p.1 = .vtx ∧ q.1 = .arcMid) ∨ (p.1 = .vtx ∧ q.1 = .arcEnd) ∨
      (p.1 = .arcMid ∧ q.1 = .arcEnd) := by
  obtain ⟨t, w⟩ := p
  obtain ⟨s, x⟩ := q
  cases t <;> cases s <;>
    first
      | exact h.elim
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Nothing points at a vertex node: level 0 is the bottom. -/
theorem pat_no_in_vPt (q : incInterp.Map A) (v : A) : ¬TDPatArc q (vPt v) := fun h => by
  rcases pat_arc_tag h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> exact absurd h' (by simp [vPt, vPt2])

/-- An end node points at nothing: level 2 is the top. -/
theorem pat_no_out_endPt (u v : A) (q : incInterp.Map A) : ¬TDPatArc (endPt u v) q := fun h => by
  rcases pat_arc_tag h with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> exact absurd h' (by simp [endPt])

/-- Two middle nodes are never joined: they sit at the same level. -/
theorem pat_no_arc_mid_mid (u v u' v' : A) : ¬TDPatArc (midPt u v) (midPt u' v') := fun h => by
  rcases pat_arc_tag h with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩ <;> exact absurd h' (by simp [midPt])

@[simp]
theorem pat_arc_v_mid (x u v : A) :
    TDPatArc (vPt x) (midPt u v) ↔ TGPatV x ∧ (TGPatV u ∧ TGPatV v ∧ TGPatE u v) ∧ x = u := by
  rw [TDPatArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, vPt, vPt2, midPt, TGPatV, TGPatE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

@[simp]
theorem pat_arc_v_end (x u v : A) :
    TDPatArc (vPt x) (endPt u v) ↔ TGPatV x ∧ (TGPatV u ∧ TGPatV v ∧ TGPatE u v) ∧ x = v := by
  rw [TDPatArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, vPt, vPt2, endPt, TGPatV, TGPatE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

@[simp]
theorem pat_arc_mid_end (u v u' v' : A) :
    TDPatArc (midPt u v) (endPt u' v') ↔
      (TGPatV u ∧ TGPatV v ∧ TGPatE u v) ∧ (TGPatV u' ∧ TGPatV v' ∧ TGPatE u' v') ∧
        u = u' ∧ v = v' := by
  rw [TDPatArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, midPt, endPt, TGPatV, TGPatE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

end PatternChar

/-! ### What the gadget builds, on the host side -/

section HostChar

variable {A : Type} [Language.twoGraphs.Structure A]

@[simp]
theorem host_vPt2 (u v : A) : TDHostV (vPt2 u v) ↔ u = v ∧ TGHostV u := by
  rw [TDHostV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, vPt2, TGHostV, Formula.realize_rel₁, Formula.realize_equal]

@[simp]
theorem host_vPt (v : A) : TDHostV (vPt v) ↔ TGHostV v := by
  rw [vPt, host_vPt2]
  simp

@[simp]
theorem host_midPt (u v : A) :
    TDHostV (midPt u v) ↔ TGHostV u ∧ TGHostV v ∧ TGHostE u v := by
  rw [TDHostV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, midPt, TGHostV, TGHostE, Formula.realize_rel₁, Formula.realize_rel₂,
    and_assoc]

@[simp]
theorem host_endPt (u v : A) :
    TDHostV (endPt u v) ↔ TGHostV u ∧ TGHostV v ∧ TGHostE u v := by
  rw [TDHostV, FOInterpretation.relMap_map]
  simp [incInterp, nodeF, endPt, TGHostV, TGHostE, Formula.realize_rel₁, Formula.realize_rel₂,
    and_assoc]

/-- A host node is a vertex node, a middle node or an end node. The
hypothesis is unfolded by `rcases` rather than by `rw`: the defining formula's
realization is definitionally a conjunction, and a pair literal at
`FOInterpretation.Map` type does not match at rewriting transparency. -/
theorem hostV_cases {p : incInterp.Map A} (h : TDHostV p) :
    (∃ v, TGHostV v ∧ p = vPt v) ∨
      (∃ u v, (TGHostV u ∧ TGHostV v ∧ TGHostE u v) ∧ p = midPt u v) ∨
      ∃ u v, (TGHostV u ∧ TGHostV v ∧ TGHostE u v) ∧ p = endPt u v := by
  obtain ⟨t, w⟩ := p
  cases t
  · obtain ⟨heq, hmark⟩ := (host_vPt2 (w 0) (w 1)).mp (Eq.mp (congrArg TDHostV (vtx_eta w)) h)
    exact Or.inl ⟨w 0, hmark, (vtx_eta w).trans (by rw [vPt, heq])⟩
  · exact Or.inr (Or.inl ⟨w 0, w 1,
      (host_midPt (w 0) (w 1)).mp (Eq.mp (congrArg TDHostV (mid_eta w)) h), mid_eta w⟩)
  · exact Or.inr (Or.inr ⟨w 0, w 1,
      (host_endPt (w 0) (w 1)).mp (Eq.mp (congrArg TDHostV (end_eta w)) h), end_eta w⟩)

/-- The only arcs are the three of the gadget: the tags of an arc's endpoints
climb the three levels. The six forbidden tag combinations need no argument –
their defining formula is `⊥`, so the hypothesis *is* `False`. -/
theorem host_arc_tag {p q : incInterp.Map A} (h : TDHostArc p q) :
    (p.1 = .vtx ∧ q.1 = .arcMid) ∨ (p.1 = .vtx ∧ q.1 = .arcEnd) ∨
      (p.1 = .arcMid ∧ q.1 = .arcEnd) := by
  obtain ⟨t, w⟩ := p
  obtain ⟨s, x⟩ := q
  cases t <;> cases s <;>
    first
      | exact h.elim
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Nothing points at a vertex node: level 0 is the bottom. -/
theorem host_no_in_vPt (q : incInterp.Map A) (v : A) : ¬TDHostArc q (vPt v) := fun h => by
  rcases host_arc_tag h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> exact absurd h' (by simp [vPt, vPt2])

/-- An end node points at nothing: level 2 is the top. -/
theorem host_no_out_endPt (u v : A) (q : incInterp.Map A) : ¬TDHostArc (endPt u v) q := fun h => by
  rcases host_arc_tag h with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> exact absurd h' (by simp [endPt])

/-- Two middle nodes are never joined: they sit at the same level. -/
theorem host_no_arc_mid_mid (u v u' v' : A) : ¬TDHostArc (midPt u v) (midPt u' v') := fun h => by
  rcases host_arc_tag h with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩ <;> exact absurd h' (by simp [midPt])

@[simp]
theorem host_arc_v_mid (x u v : A) :
    TDHostArc (vPt x) (midPt u v) ↔ TGHostV x ∧ (TGHostV u ∧ TGHostV v ∧ TGHostE u v) ∧ x = u := by
  rw [TDHostArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, vPt, vPt2, midPt, TGHostV, TGHostE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

@[simp]
theorem host_arc_v_end (x u v : A) :
    TDHostArc (vPt x) (endPt u v) ↔ TGHostV x ∧ (TGHostV u ∧ TGHostV v ∧ TGHostE u v) ∧ x = v := by
  rw [TDHostArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, vPt, vPt2, endPt, TGHostV, TGHostE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

@[simp]
theorem host_arc_mid_end (u v u' v' : A) :
    TDHostArc (midPt u v) (endPt u' v') ↔
      (TGHostV u ∧ TGHostV v ∧ TGHostE u v) ∧ (TGHostV u' ∧ TGHostV v' ∧ TGHostE u' v') ∧
        u = u' ∧ v = v' := by
  rw [TDHostArc, FOInterpretation.relMap_map]
  simp [incInterp, arcF, nodeF, midPt, endPt, TGHostV, TGHostE, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, and_assoc]

end HostChar

/-! ### The gadget is acyclic: the levels -/

section Levels

variable {A : Type} [Language.twoGraphs.Structure A]

/-- The level of a node: vertices at 0, middle nodes at 1, end nodes at 2. The
carried topological order is exactly the comparison of levels. -/
def level : NodeTag → ℕ
  | .vtx => 0
  | .arcMid => 1
  | .arcEnd => 2

@[simp]
theorem patLt_iff (p q : incInterp.Map A) : TDPatLt p q ↔ level p.1 < level q.1 := by
  obtain ⟨t, w⟩ := p
  obtain ⟨s, x⟩ := q
  cases t <;> cases s <;>
    first
      | exact ⟨fun h => h.elim, fun h => absurd h (by simp [level])⟩
      | exact ⟨fun _ => by simp [level], fun _ => id⟩

@[simp]
theorem hostLt_iff (p q : incInterp.Map A) : TDHostLt p q ↔ level p.1 < level q.1 := by
  obtain ⟨t, w⟩ := p
  obtain ⟨s, x⟩ := q
  cases t <;> cases s <;>
    first
      | exact ⟨fun h => h.elim, fun h => absurd h (by simp [level])⟩
      | exact ⟨fun _ => by simp [level], fun _ => id⟩

/-- Arcs climb the levels, on the pattern side. -/
theorem patLt_of_patArc {p q : incInterp.Map A} (h : TDPatArc p q) : TDPatLt p q := by
  rcases pat_arc_tag h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    exact (patLt_iff p q).mpr (by rw [h₁, h₂]; decide)

/-- Arcs climb the levels, on the host side. -/
theorem hostLt_of_hostArc {p q : incInterp.Map A} (h : TDHostArc p q) : TDHostLt p q := by
  rcases host_arc_tag h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    exact (hostLt_iff p q).mpr (by rw [h₁, h₂]; decide)

/-- **The pattern side of the image is a DAG**, with the carried order as
witness: the order is the level comparison, so irreflexivity and transitivity
are those of `<` on `ℕ`, and every arc climbs a level. -/
theorem topoOn_pat : TopoOn (TDPatV (A := incInterp.Map A)) TDPatLt TDPatArc :=
  ⟨fun p _ h => absurd ((patLt_iff p p).mp h) (lt_irrefl _),
    fun p q r _ _ _ h₁ h₂ =>
      (patLt_iff p r).mpr (((patLt_iff p q).mp h₁).trans ((patLt_iff q r).mp h₂)),
    fun _ _ _ _ h => patLt_of_patArc h⟩

/-- **The host side of the image is a DAG**, likewise. -/
theorem topoOn_host : TopoOn (TDHostV (A := incInterp.Map A)) TDHostLt TDHostArc :=
  ⟨fun p _ h => absurd ((hostLt_iff p p).mp h) (lt_irrefl _),
    fun p q r _ _ _ h₁ h₂ =>
      (hostLt_iff p r).mpr (((hostLt_iff p q).mp h₁).trans ((hostLt_iff q r).mp h₂)),
    fun _ _ _ _ h => hostLt_of_hostArc h⟩

end Levels

/-! ### From an isomorphism of the graphs to one of the DAGs -/

section Lift

variable {A : Type}

/-- A map of the universe, lifted to the nodes of the gadget: it keeps the
level and acts on both coordinates. -/
def liftMap (g : A → A) (p : incInterp.Map A) : incInterp.Map A := (p.1, fun i => g (p.2 i))

@[simp]
theorem liftMap_vPt (g : A → A) (v : A) : liftMap g (vPt v) = vPt (g v) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> rfl⟩

@[simp]
theorem liftMap_midPt (g : A → A) (u v : A) : liftMap g (midPt u v) = midPt (g u) (g v) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> rfl⟩

@[simp]
theorem liftMap_endPt (g : A → A) (u v : A) : liftMap g (endPt u v) = endPt (g u) (g v) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => by fin_cases i <;> rfl⟩

theorem liftMap_tag (g : A → A) (p : incInterp.Map A) : (liftMap g p).1 = p.1 := rfl

end Lift

section Forward

variable {A : Type} [Language.twoGraphs.Structure A]

/-- Both coordinates of a pattern node are marked vertices. -/
theorem patV_coords {p : incInterp.Map A} (h : TDPatV p) : TGPatV (p.2 0) ∧ TGPatV (p.2 1) := by
  rcases patV_cases h with ⟨v, hv, rfl⟩ | ⟨u, v, ⟨hu, hv, -⟩, rfl⟩ | ⟨u, v, ⟨hu, hv, -⟩, rfl⟩
  · exact ⟨hv, hv⟩
  · exact ⟨hu, hv⟩
  · exact ⟨hu, hv⟩

/-- **The gadget is functorial and faithful**: an isomorphism of the two marked
graphs lifts, level by level, to an isomorphism of the two DAGs. The six
combinations of levels that carry no arc are dispatched by the level lemmas,
the three that do by the corresponding characterizations. -/
theorem relIsoOn_map (g : A → A)
    (hmaps : ∀ x, TGPatV x → TGHostV (g x))
    (hinj : ∀ x y, TGPatV x → TGPatV y → g x = g y → x = y)
    (hsurj : ∀ y, TGHostV y → ∃ x, TGPatV x ∧ g x = y)
    (hedge : ∀ x y, TGPatV x → TGPatV y → (TGPatE x y ↔ TGHostE (g x) (g y))) :
    RelIsoOn (TDPatV (A := incInterp.Map A)) TDHostV TDPatArc TDHostArc := by
  refine ⟨liftMap g, ?_, ?_, ?_, ?_⟩
  · rintro p hp
    rcases patV_cases hp with ⟨v, hv, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩
    · rw [liftMap_vPt]
      exact (host_vPt (g v)).mpr (hmaps v hv)
    · rw [liftMap_midPt]
      exact (host_midPt (g u) (g v)).mpr ⟨hmaps u hu, hmaps v hv, (hedge u v hu hv).mp he⟩
    · rw [liftMap_endPt]
      exact (host_endPt (g u) (g v)).mpr ⟨hmaps u hu, hmaps v hv, (hedge u v hu hv).mp he⟩
  · intro p q hp hq hpq
    obtain ⟨hp0, hp1⟩ := patV_coords hp
    obtain ⟨hq0, hq1⟩ := patV_coords hq
    have htag : p.1 = q.1 := by rw [← liftMap_tag g p, ← liftMap_tag g q, hpq]
    have hco : ∀ i, g (p.2 i) = g (q.2 i) := fun i => congrFun (congrArg Prod.snd hpq) i
    refine Prod.ext_iff.mpr ⟨htag, funext fun i => ?_⟩
    fin_cases i
    · exact hinj _ _ hp0 hq0 (hco 0)
    · exact hinj _ _ hp1 hq1 (hco 1)
  · intro q hq
    rcases hostV_cases hq with ⟨w, hw, rfl⟩ | ⟨x, y, ⟨hx, hy, he⟩, rfl⟩ | ⟨x, y, ⟨hx, hy, he⟩, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := hsurj w hw
      exact ⟨vPt u, (pat_vPt u).mpr hu, liftMap_vPt g u⟩
    · obtain ⟨u, hu, rfl⟩ := hsurj x hx
      obtain ⟨v, hv, rfl⟩ := hsurj y hy
      exact ⟨midPt u v, (pat_midPt u v).mpr ⟨hu, hv, (hedge u v hu hv).mpr he⟩,
        liftMap_midPt g u v⟩
    · obtain ⟨u, hu, rfl⟩ := hsurj x hx
      obtain ⟨v, hv, rfl⟩ := hsurj y hy
      exact ⟨endPt u v, (pat_endPt u v).mpr ⟨hu, hv, (hedge u v hu hv).mpr he⟩,
        liftMap_endPt g u v⟩
  · intro p q hp hq
    rcases patV_cases hp with ⟨a, ha, rfl⟩ | ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ |
      ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ <;>
      rcases patV_cases hq with ⟨c, hc, rfl⟩ | ⟨c, d, ⟨hc, hd, hcd⟩, rfl⟩ |
        ⟨c, d, ⟨hc, hd, hcd⟩, rfl⟩ <;>
      simp only [liftMap_vPt, liftMap_midPt, liftMap_endPt]
    · exact iff_of_false (pat_no_in_vPt _ _) (host_no_in_vPt _ _)
    · rw [pat_arc_v_mid, host_arc_v_mid]
      exact ⟨fun ⟨_, _, h₃⟩ => ⟨hmaps _ ha, ⟨hmaps _ hc, hmaps _ hd,
          (hedge _ _ hc hd).mp hcd⟩, by rw [h₃]⟩,
        fun ⟨_, _, h₃⟩ => ⟨ha, ⟨hc, hd, hcd⟩, hinj _ _ ha hc h₃⟩⟩
    · rw [pat_arc_v_end, host_arc_v_end]
      exact ⟨fun ⟨_, _, h₃⟩ => ⟨hmaps _ ha, ⟨hmaps _ hc, hmaps _ hd,
          (hedge _ _ hc hd).mp hcd⟩, by rw [h₃]⟩,
        fun ⟨_, _, h₃⟩ => ⟨ha, ⟨hc, hd, hcd⟩, hinj _ _ ha hd h₃⟩⟩
    · exact iff_of_false (pat_no_in_vPt _ _) (host_no_in_vPt _ _)
    · exact iff_of_false (pat_no_arc_mid_mid _ _ _ _) (host_no_arc_mid_mid _ _ _ _)
    · rw [pat_arc_mid_end, host_arc_mid_end]
      exact ⟨fun ⟨_, _, h₃, h₄⟩ => ⟨⟨hmaps _ ha, hmaps _ hb, (hedge _ _ ha hb).mp hab⟩,
          ⟨hmaps _ hc, hmaps _ hd, (hedge _ _ hc hd).mp hcd⟩, by rw [h₃], by rw [h₄]⟩,
        fun ⟨_, _, h₃, h₄⟩ => ⟨⟨ha, hb, hab⟩, ⟨hc, hd, hcd⟩,
          hinj _ _ ha hc h₃, hinj _ _ hb hd h₄⟩⟩
    · exact iff_of_false (pat_no_out_endPt _ _ _) (host_no_out_endPt _ _ _)
    · exact iff_of_false (pat_no_out_endPt _ _ _) (host_no_out_endPt _ _ _)
    · exact iff_of_false (pat_no_out_endPt _ _ _) (host_no_out_endPt _ _ _)

end Forward

/-! ### From an isomorphism of the DAGs back to one of the graphs -/

section Backward

variable {A : Type} [Language.twoGraphs.Structure A] (F : incInterp.Map A → incInterp.Map A)
  (hmaps : ∀ p, TDPatV p → TDHostV (F p))
  (hsurj : ∀ q, TDHostV q → ∃ p, TDPatV p ∧ F p = q)
  (hedge : ∀ p q, TDPatV p → TDPatV q → (TDPatArc p q ↔ TDHostArc (F p) (F q)))

include hmaps hsurj hedge

/-- An isomorphism of the DAGs sends vertex nodes to vertex nodes: they are the
nodes nothing points at, and that is preserved because every host node is the
image of a pattern node. -/
theorem image_vPt {v : A} (hv : TGPatV v) : ∃ w, TGHostV w ∧ F (vPt v) = vPt w := by
  have hpv : TDPatV (vPt v) := (pat_vPt v).mpr hv
  have hnoin : ∀ q, TDHostV q → ¬TDHostArc q (F (vPt v)) := by
    intro q hq harc
    obtain ⟨p, hp, rfl⟩ := hsurj q hq
    exact pat_no_in_vPt p v ((hedge p (vPt v) hp hpv).mpr harc)
  rcases hostV_cases (hmaps _ hpv) with ⟨w, hw, hFw⟩ | ⟨x, y, ⟨hx, hy, he⟩, hFw⟩ |
    ⟨x, y, ⟨hx, hy, he⟩, hFw⟩
  · exact ⟨w, hw, hFw⟩
  · exact absurd (hFw ▸ (host_arc_v_mid x x y).mpr ⟨hx, ⟨hx, hy, he⟩, rfl⟩)
      (hnoin (vPt x) ((host_vPt x).mpr hx))
  · exact absurd (hFw ▸ (host_arc_v_end y x y).mpr ⟨hy, ⟨hx, hy, he⟩, rfl⟩)
      (hnoin (vPt y) ((host_vPt y).mpr hy))

omit hmaps in
/-- Nothing follows the image of an end node: end nodes are the nodes with no
outgoing arc, and that too is preserved. -/
theorem image_endPt_no_out {x y : A} (he : TDPatV (endPt x y)) (q : incInterp.Map A)
    (hq : TDHostV q) : ¬TDHostArc (F (endPt x y)) q := by
  intro harc
  obtain ⟨p, hp, rfl⟩ := hsurj q hq
  exact pat_no_out_endPt x y p ((hedge (endPt x y) p he hp).mpr harc)

omit hsurj in
/-- The image of a middle node is a middle node: it has both an incoming and an
outgoing arc, which no other level has. -/
theorem image_midPt_shape {x y : A} (hx : TGPatV x) (hy : TGPatV y) (hxy : TGPatE x y) :
    ∃ x' y', (TGHostV x' ∧ TGHostV y' ∧ TGHostE x' y') ∧ F (midPt x y) = midPt x' y' := by
  have hmid : TDPatV (midPt x y) := (pat_midPt x y).mpr ⟨hx, hy, hxy⟩
  have hend : TDPatV (endPt x y) := (pat_endPt x y).mpr ⟨hx, hy, hxy⟩
  have hin : TDHostArc (F (vPt x)) (F (midPt x y)) :=
    (hedge _ _ ((pat_vPt x).mpr hx) hmid).mp ((pat_arc_v_mid x x y).mpr ⟨hx, ⟨hx, hy, hxy⟩, rfl⟩)
  have hout : TDHostArc (F (midPt x y)) (F (endPt x y)) :=
    (hedge _ _ hmid hend).mp
      ((pat_arc_mid_end x y x y).mpr ⟨⟨hx, hy, hxy⟩, ⟨hx, hy, hxy⟩, rfl, rfl⟩)
  rcases hostV_cases (hmaps _ hmid) with ⟨w, hw, hFw⟩ | ⟨x', y', hnode, hFw⟩ | ⟨x', y', hnode, hFw⟩
  · exact absurd (hFw ▸ hin) (host_no_in_vPt _ w)
  · exact ⟨x', y', hnode, hFw⟩
  · exact absurd (hFw ▸ hout) (host_no_out_endPt x' y' _)

/-- The image of an end node is an end node. -/
theorem image_endPt_shape {x y : A} (hx : TGPatV x) (hy : TGPatV y) (hxy : TGPatE x y) :
    ∃ x' y', (TGHostV x' ∧ TGHostV y' ∧ TGHostE x' y') ∧ F (endPt x y) = endPt x' y' := by
  have hmid : TDPatV (midPt x y) := (pat_midPt x y).mpr ⟨hx, hy, hxy⟩
  have hend : TDPatV (endPt x y) := (pat_endPt x y).mpr ⟨hx, hy, hxy⟩
  have hin : TDHostArc (F (midPt x y)) (F (endPt x y)) :=
    (hedge _ _ hmid hend).mp
      ((pat_arc_mid_end x y x y).mpr ⟨⟨hx, hy, hxy⟩, ⟨hx, hy, hxy⟩, rfl, rfl⟩)
  rcases hostV_cases (hmaps _ hend) with ⟨w, hw, hFw⟩ | ⟨x', y', hnode, hFw⟩ | ⟨x', y', hnode, hFw⟩
  · exact absurd (hFw ▸ hin) (host_no_in_vPt _ w)
  · exact absurd (hFw ▸ (host_arc_mid_end x' y' x' y').mpr ⟨hnode, hnode, rfl, rfl⟩)
      (image_endPt_no_out F hsurj hedge hend _ ((host_endPt x' y').mpr hnode))
  · exact ⟨x', y', hnode, hFw⟩

variable (g : A → A) (hg : ∀ v, TGPatV v → TGHostV (g v) ∧ F (vPt v) = vPt (g v))

include hg

/-- The image of the middle node of an arc is the middle node of the image
arc: the tail is pinned by the arc from the tail's vertex node, the head by the
arc from the head's vertex node through the end node. -/
theorem image_midPt_eq {x y : A} (hx : TGPatV x) (hy : TGPatV y) (hxy : TGPatE x y) :
    F (midPt x y) = midPt (g x) (g y) ∧ F (endPt x y) = endPt (g x) (g y) := by
  obtain ⟨x', y', hnode', hmid'⟩ := image_midPt_shape F hmaps hedge hx hy hxy
  obtain ⟨x'', y'', hnode'', hend'⟩ := image_endPt_shape F hmaps hsurj hedge hx hy hxy
  have hmid : TDPatV (midPt x y) := (pat_midPt x y).mpr ⟨hx, hy, hxy⟩
  have hend : TDPatV (endPt x y) := (pat_endPt x y).mpr ⟨hx, hy, hxy⟩
  -- the tail: the arc from the tail's vertex node
  have htail : g x = x' := by
    have := (hedge _ _ ((pat_vPt x).mpr hx) hmid).mp
      ((pat_arc_v_mid x x y).mpr ⟨hx, ⟨hx, hy, hxy⟩, rfl⟩)
    rw [(hg x hx).2, hmid'] at this
    exact ((host_arc_v_mid _ x' y').mp this).2.2
  -- the two arc nodes carry the same pair
  have hpair : x' = x'' ∧ y' = y'' := by
    have := (hedge _ _ hmid hend).mp
      ((pat_arc_mid_end x y x y).mpr ⟨⟨hx, hy, hxy⟩, ⟨hx, hy, hxy⟩, rfl, rfl⟩)
    rw [hmid', hend'] at this
    exact ((host_arc_mid_end x' y' x'' y'').mp this).2.2
  -- the head: the arc from the head's vertex node into the end node
  have hhead : g y = y' := by
    have := (hedge _ _ ((pat_vPt y).mpr hy) hend).mp
      ((pat_arc_v_end y x y).mpr ⟨hy, ⟨hx, hy, hxy⟩, rfl⟩)
    rw [(hg y hy).2, hend'] at this
    rw [hpair.2]
    exact ((host_arc_v_end _ x'' y'').mp this).2.2
  exact ⟨by rw [hmid', htail, hhead], by rw [hend', htail, hhead, hpair.1, hpair.2]⟩

end Backward

/-! ### Correctness of the reduction -/

section Correctness

variable {A : Type} [Language.twoGraphs.Structure A]

/-- **Reading an isomorphism of the DAGs on level 0**: it maps vertex nodes to
vertex nodes, so it restricts to a bijection of the marked vertices, and the
arcs of the graphs are recovered from the arcs of the gadget through the middle
and end nodes. -/
theorem relIsoOn_of_dagIso
    (h : RelIsoOn (TDPatV (A := incInterp.Map A)) TDHostV TDPatArc TDHostArc) :
    RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE := by
  classical
  obtain ⟨F, hmaps, hinj, hsurj, hedge⟩ := h
  have hstep : ∀ v : {v : A // TGPatV v}, ∃ w, TGHostV w ∧ F (vPt v.1) = vPt w :=
    fun v => image_vPt F hmaps hsurj hedge v.2
  choose gg hgg1 hgg2 using hstep
  set g : A → A := fun v => if h : TGPatV v then gg ⟨v, h⟩ else v with hgdef
  have hg : ∀ v, TGPatV v → TGHostV (g v) ∧ F (vPt v) = vPt (g v) := by
    intro v hv
    have hgv : g v = gg ⟨v, hv⟩ := by rw [hgdef]; exact dif_pos hv
    rw [hgv]
    exact ⟨hgg1 ⟨v, hv⟩, hgg2 ⟨v, hv⟩⟩
  have hginj : ∀ x y, TGPatV x → TGPatV y → g x = g y → x = y := by
    intro x y hx hy hxy
    have : F (vPt x) = F (vPt y) := by rw [(hg x hx).2, (hg y hy).2, hxy]
    exact vPt_injective (hinj _ _ ((pat_vPt x).mpr hx) ((pat_vPt y).mpr hy) this)
  refine ⟨g, fun x hx => (hg x hx).1, hginj, ?_, ?_⟩
  · -- every marked vertex of the host is hit, because every host vertex node is
    intro w hw
    obtain ⟨p, hp, hFp⟩ := hsurj (vPt w) ((host_vPt w).mpr hw)
    rcases patV_cases hp with ⟨u, hu, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩
    · refine ⟨u, hu, vPt_injective ?_⟩
      rw [← (hg u hu).2, hFp]
    · exact absurd (hFp ▸ (hedge _ _ ((pat_vPt u).mpr hu) ((pat_midPt u v).mpr ⟨hu, hv, he⟩)).mp
        ((pat_arc_v_mid u u v).mpr ⟨hu, ⟨hu, hv, he⟩, rfl⟩)) (host_no_in_vPt _ w)
    · exact absurd (hFp ▸ (hedge _ _ ((pat_midPt u v).mpr ⟨hu, hv, he⟩)
        ((pat_endPt u v).mpr ⟨hu, hv, he⟩)).mp
        ((pat_arc_mid_end u v u v).mpr ⟨⟨hu, hv, he⟩, ⟨hu, hv, he⟩, rfl, rfl⟩))
        (host_no_in_vPt _ w)
  · -- arcs, both ways, through the middle node of the arc
    intro x y hx hy
    constructor
    · intro hxy
      have himg := (image_midPt_eq F hmaps hsurj hedge g hg hx hy hxy).1
      have := hmaps _ ((pat_midPt x y).mpr ⟨hx, hy, hxy⟩)
      rw [himg] at this
      exact ((host_midPt (g x) (g y)).mp this).2.2
    · intro hxy
      obtain ⟨p, hp, hFp⟩ := hsurj (midPt (g x) (g y))
        ((host_midPt (g x) (g y)).mpr ⟨(hg x hx).1, (hg y hy).1, hxy⟩)
      rcases patV_cases hp with ⟨u, hu, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩ | ⟨u, v, ⟨hu, hv, he⟩, rfl⟩
      · rw [(hg u hu).2] at hFp
        exact absurd (congrArg Prod.fst hFp) (by simp [vPt, vPt2, midPt])
      · rw [(image_midPt_eq F hmaps hsurj hedge g hg hu hv he).1] at hFp
        obtain ⟨h₁, h₂⟩ := midPt_inj hFp
        rw [← hginj u x hu hx h₁, ← hginj v y hv hy h₂]
        exact he
      · rw [(image_midPt_eq F hmaps hsurj hedge g hg hu hv he).2] at hFp
        exact absurd (congrArg Prod.fst hFp) (by simp [endPt, midPt])

/-- **Correctness of the reduction**: the two graphs are isomorphic exactly
when the two DAGs built from them are. -/
theorem hasDigraphIso_iff_hasDagIso_map (A : Type) [Language.twoGraphs.Structure A] [Finite A] :
    HasDigraphIso A ↔ HasDagIso (incInterp.Map A) := by
  constructor
  · rintro ⟨-, g, hmaps, hinj, hsurj, hedge⟩
    exact ⟨incInterp.map_finite A, topoOn_pat, topoOn_host,
      relIsoOn_map g hmaps hinj hsurj hedge⟩
  · rintro ⟨-, -, -, hiso⟩
    exact ⟨‹Finite A›, relIsoOn_of_dagIso hiso⟩

end Correctness

end DagIso

/-- **Digraph Isomorphism FO-reduces to DAG Isomorphism**: subdivide every arc
twice, and carry the level comparison as the topological order. Two dimensions,
three tags, and no order on the input – the reduction is order-free, as every
reduction between isomorphism problems must be. -/
def digraphIso_fo_reduction_dagIso : DigraphIso ≤ᶠᵒ DagIso where
  Tag := DagIso.NodeTag
  dim := 2
  toInterpretation := DagIso.incInterp
  correct A _ _ _ := DagIso.hasDigraphIso_iff_hasDagIso_map A

end DescriptiveComplexity
