/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Cycle
import DescriptiveComplexity.Problems.Hamilton.Gadget
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Lattice

/-!
# A Hamilton circuit presented as a cyclic list

The forward direction of the Vertex Cover → Hamilton Circuit reduction builds
its circuit as an explicit sequence of vertices – selectors interleaved with the
chains of the cover vertices – so it is convenient to introduce a tour from a
**list**: a duplicate-free list containing every vertex, along which
consecutive elements are adjacent and whose last element is adjacent to its
first, is a tour (`DescriptiveComplexity.tourOn_of_cycleList`).
-/

namespace DescriptiveComplexity

open FirstOrder

section CycleList

variable {H : Type} {R : H → H → Prop}

/-- Consecutive elements of an `IsChain` list are related, indexed form. -/
private theorem isChain_rel_get {l : List H} (h : l.IsChain R) (i : ℕ)
    (hi : i + 1 < l.length) :
    R (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, hi⟩) := by
  have hdec : l = l.take i ++ l[i] :: l[i + 1] :: l.drop (i + 2) := by
    conv_lhs => rw [← List.take_append_drop i l,
      List.drop_eq_getElem_cons (show i < l.length by omega),
      List.drop_eq_getElem_cons (show i + 1 < l.length from hi)]
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp h hdec

/-- **A cyclic list is a tour.** A duplicate-free list containing every element,
along which consecutive elements are `R`-related and whose last element is
`R`-related to its first, presents a tour of `R`. -/
theorem tourOn_of_cycleList [Finite H] (l : List H) (hne : l ≠ [])
    (nd : l.Nodup) (hcov : ∀ x, x ∈ l) (hchain : l.IsChain R)
    (hwrap : R (l.getLast hne) (l.head hne)) : TourOn R := by
  classical
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
  refine tourOn_of_enum (List.Nodup.getEquivOfForallMemList l nd hcov) fun i => ?_
  simp only [List.Nodup.getEquivOfForallMemList_apply]
  by_cases hi : (i : ℕ) + 1 < l.length
  · have hnext : (nextIdx i : ℕ) = (i : ℕ) + 1 := nextIdx_of_lt hi
    have := isChain_rel_get hchain i hi
    have he : l.get (nextIdx i) = l.get ⟨(i : ℕ) + 1, hi⟩ := by
      apply congrArg; exact Fin.ext hnext
    rw [he]; simpa using this
  · -- `i` is the last index: it wraps to the head
    have hlast : (i : ℕ) + 1 = l.length := by have := i.isLt; omega
    have hnext : (nextIdx i : ℕ) = 0 := nextIdx_of_last hlast
    have hbound : l.length - 1 < l.length := by omega
    have hival : (i : ℕ) = l.length - 1 := by omega
    have hget_last : l.get i = l.getLast hne := by
      rw [show i = ⟨l.length - 1, hbound⟩ from Fin.ext hival]
      exact List.get_length_sub_one _
    have hget_head : l.get (nextIdx i) = l.head hne := by
      rw [show nextIdx i = ⟨0, hlen⟩ from Fin.ext hnext, List.get_eq_getElem,
        List.head_eq_getElem_zero]
    rw [hget_last, hget_head]; exact hwrap

/-- **A cycle of blocks is a tour.** A list of nonempty blocks whose flattening
is duplicate-free and covers everything, where each block is a chain,
consecutive blocks connect (last of one to head of the next), and the whole
wraps (last of the flattening to its head), presents a tour. This packages the
`isChain_flatten` step for the forward construction, whose blocks are a selector
followed by a cover vertex's chain. -/
theorem tourOn_of_blocks [Finite H] (bs : List (List H)) (hbne : [] ∉ bs)
    (hflat : bs.flatten ≠ []) (nd : bs.flatten.Nodup) (hcov : ∀ x, x ∈ bs.flatten)
    (hchain : ∀ l ∈ bs, l.IsChain R)
    (hconn : bs.IsChain (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y))
    (hwrap : ∀ x ∈ bs.flatten.getLast?, ∀ y ∈ bs.flatten.head?, R x y) : TourOn R := by
  refine tourOn_of_cycleList bs.flatten hflat nd hcov ?_ ?_
  · rw [List.isChain_flatten hbne]; exact ⟨hchain, hconn⟩
  · exact hwrap _ (List.getLast?_eq_getLast_of_ne_nil hflat ▸ rfl)
      _ (List.head?_eq_some_head hflat ▸ rfl)

end CycleList

/-! ### The traversal of a single gadget (the snake) -/

section Snake

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

/-- The gadget vertex of index `i` over the ordered edge `(a, b)` (owner `a`). -/
abbrev gv (i : HTag) (hi : i ≠ .sel ∧ i ≠ .hub) {a b : A} (h : HEdge a b) :
    hamInterp.MapRel A := gPt i hi h

/-- Adjacency between two gadget vertices reduces to the intended adjacency of
their (tag, tuple) pairs. -/
theorem gv_adj {a b a' b' : A} (i j : HTag) (hi hj) (h : HEdge a b) (h' : HEdge a' b') :
    DGEdge (gPt i hi h) (gPt j hj h') ↔ IAdjRaw (i, ![a, b]) (j, ![a', b']) :=
  dgEdge_iff _ _

/-- Gadget vertex `0` (a side's entrance). -/
abbrev gv0 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g0 ⟨by decide, by decide⟩ h
/-- Gadget vertex `1`. -/
abbrev gv1 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g1 ⟨by decide, by decide⟩ h
/-- Gadget vertex `2`. -/
abbrev gv2 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g2 ⟨by decide, by decide⟩ h
/-- Gadget vertex `3`. -/
abbrev gv3 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g3 ⟨by decide, by decide⟩ h
/-- Gadget vertex `4`. -/
abbrev gv4 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g4 ⟨by decide, by decide⟩ h
/-- Gadget vertex `5` (a side's exit). -/
abbrev gv5 {a b : A} (h : HEdge a b) : hamInterp.MapRel A := gPt .g5 ⟨by decide, by decide⟩ h

/-- The traversal of gadget `{a, b}` when `b` is **also** in the cover: only the
`a`-side is walked, a straight horizontal path `0-1-2-3-4-5`. -/
def snakeBoth {a b : A} (h : HEdge a b) : List (hamInterp.MapRel A) :=
  [gv0 h, gv1 h, gv2 h, gv3 h, gv4 h, gv5 h]

/-- The traversal of gadget `{a, b}` when `b` is **not** in the cover: the
`a`-through path visiting all twelve vertices, dipping into the `b`-side. -/
def snakeThrough {a b : A} (h : HEdge a b) : List (hamInterp.MapRel A) :=
  [gv0 h, gv1 h, gv2 h,
   gv0 (hEdge_symm h), gv1 (hEdge_symm h), gv2 (hEdge_symm h),
   gv3 (hEdge_symm h), gv4 (hEdge_symm h), gv5 (hEdge_symm h),
   gv3 h, gv4 h, gv5 h]

theorem snakeBoth_isChain {a b : A} (h : HEdge a b) : (snakeBoth h).IsChain DGEdge := by
  simp only [snakeBoth, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (gv_adj _ _ _ _ _ _).mpr (by simp [IAdjRaw])

theorem snakeThrough_isChain {a b : A} (h : HEdge a b) : (snakeThrough h).IsChain DGEdge := by
  simp only [snakeThrough, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (gv_adj _ _ _ _ _ _).mpr (by simp [IAdjRaw])

@[simp] theorem snakeBoth_head? {a b : A} (h : HEdge a b) :
    (snakeBoth h).head? = some (gv0 h) := rfl
@[simp] theorem snakeThrough_head? {a b : A} (h : HEdge a b) :
    (snakeThrough h).head? = some (gv0 h) := rfl
@[simp] theorem snakeBoth_getLast? {a b : A} (h : HEdge a b) :
    (snakeBoth h).getLast? = some (gv5 h) := rfl
@[simp] theorem snakeThrough_getLast? {a b : A} (h : HEdge a b) :
    (snakeThrough h).getLast? = some (gv5 h) := rfl

theorem snakeBoth_ne_nil {a b : A} (h : HEdge a b) : snakeBoth h ≠ [] := by simp [snakeBoth]
theorem snakeThrough_ne_nil {a b : A} (h : HEdge a b) : snakeThrough h ≠ [] := by
  simp [snakeThrough]

/-! #### Distinctness of gadget vertices -/

theorem snakeBoth_nodup {a b : A} (h : HEdge a b) : (snakeBoth h).Nodup := by
  apply List.Nodup.of_map (fun p => p.1.1)
  simp only [snakeBoth, List.map_cons, List.map_nil, gPt_tag]
  decide

theorem snakeThrough_nodup {a b : A} (h : HEdge a b) : (snakeThrough h).Nodup := by
  apply List.Nodup.of_map (fun p => (p.1.1, p.1.2 0))
  have hab : a ≠ b := h.2
  simp only [snakeThrough, List.map_cons, List.map_nil, gPt_tag, gPt_fst]
  simp [List.nodup_cons, hab, hab.symm, Prod.ext_iff]

/-! #### Which vertices a snake contains (for covering) -/

/-- Every `a`-side gadget vertex is in the both-sides snake. -/
theorem mem_snakeBoth_owner {a b : A} (h : HEdge a b) (i : HTag) (hi : i ≠ .sel ∧ i ≠ .hub) :
    gPt i hi h ∈ snakeBoth h := by
  cases i <;>
    first
      | exact absurd rfl hi.1
      | exact absurd rfl hi.2
      | (simp only [snakeBoth, List.mem_cons]; tauto)

/-- Every `a`-side gadget vertex is in the through snake. -/
theorem mem_snakeThrough_near {a b : A} (h : HEdge a b) (i : HTag) (hi : i ≠ .sel ∧ i ≠ .hub) :
    gPt i hi h ∈ snakeThrough h := by
  cases i <;>
    first
      | exact absurd rfl hi.1
      | exact absurd rfl hi.2
      | (simp only [snakeThrough, List.mem_cons]; tauto)

/-- Every `b`-side gadget vertex – a gadget vertex owned by the far endpoint – is
in the through snake. This is why an uncovered endpoint's vertices are visited by
the covered endpoint's chain. -/
theorem mem_snakeThrough_far {a b : A} (hba : HEdge b a) (i : HTag) (hi : i ≠ .sel ∧ i ≠ .hub)
    (hab : HEdge a b) : gPt i hi hab ∈ snakeThrough hba := by
  cases i <;>
    first
      | exact absurd rfl hi.1
      | exact absurd rfl hi.2
      | (simp only [snakeThrough, List.mem_cons]; tauto)

end Snake

/-! ### The sorted neighbor list of a vertex -/

section Neighbors

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A]

open Classical in
/-- The neighbors of `a` in the input, listed in increasing order. -/
noncomputable def nbrList (a : A) : List A :=
  (Finset.univ.filter (fun b => HEdge a b)).sort (· ≤ ·)

theorem mem_nbrList {a b : A} : b ∈ nbrList a ↔ HEdge a b := by
  classical
  simp only [nbrList, Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The neighbor list is strictly increasing. -/
theorem nbrList_sortedLT (a : A) : (nbrList a).SortedLT := by
  simp only [nbrList]; exact Finset.sortedLT_sort _

theorem nbrList_nodup (a : A) : (nbrList a).Nodup := by
  simp only [nbrList]; exact Finset.sort_nodup _ _

omit [Fintype A] in
/-- **The gadget chain edge**: the exit `⟨g5,(a,b)⟩` of one gadget is adjacent to
the entrance `⟨g0,(a,c)⟩` of the next, given the neighbor-successor conditions
(`DescriptiveComplexity.IAdjRaw`, the `.g5,.g0` case). This is what glues consecutive
snakes into a vertex's chain. -/
theorem chain_edge {a : A} {b c : A} (hb : HEdge a b) (hc : HEdge a c)
    (hbc : b < c) (hbtw : ∀ d, HEdge a d → d ≤ b ∨ c ≤ d) :
    DGEdge (gv5 hb) (gv0 hc) := by
  rw [gv_adj]
  simp only [IAdjRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨trivial, hc, hbc, hbtw⟩

/-- **The neighbor list is a connection-chain**: consecutive neighbors `b`, `c`
of `a` satisfy the gadget chain edge, so the per-neighbor snakes concatenate
into `a`'s chain. -/
theorem nbrList_isChain (a : A) :
    (nbrList a).IsChain
      (fun b c => ∀ (hb : HEdge a b) (hc : HEdge a c), DGEdge (gv5 hb) (gv0 hc)) := by
  have hp : (nbrList a).Pairwise (· < ·) :=
    List.pairwise_iff_getElem.mpr fun i j h1 h2 hij => nbrList_sortedLT a (by simpa using hij)
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro b c l₁ l₂ heq hb hc
  rw [heq, List.pairwise_append, List.pairwise_cons, List.pairwise_cons] at hp
  obtain ⟨-, ⟨hbrest, hcrest, -⟩, hl1⟩ := hp
  have hbc : b < c := hbrest c (by simp)
  have hl2 : ∀ x ∈ l₂, c < x := fun x hx => hcrest x hx
  refine chain_edge hb hc hbc fun d hd => ?_
  have hdmem : d ∈ nbrList a := mem_nbrList.mpr hd
  rw [heq, List.mem_append, List.mem_cons, List.mem_cons] at hdmem
  rcases hdmem with hd1 | rfl | rfl | hd2
  · exact Or.inl (hl1 d hd1 b (by simp)).le
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inr (hl2 d hd2).le

end Neighbors

/-! ### A cover vertex's chain -/

section Chain

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A]

open Classical in
/-- The snake of gadget `{a, b}` in a chain of `a`: the `a`-side-only path if `b`
is in the cover `C`, the through-path otherwise (empty if `a, b` is not an edge,
which never happens on the neighbor list). -/
noncomputable def snakeOf (C : A → Prop) (a b : A) : List (hamInterp.MapRel A) :=
  if h : HEdge a b then (if C b then snakeBoth h else snakeThrough h) else []

open Classical in
omit [Fintype A] in
theorem snakeOf_eq {C : A → Prop} {a b : A} (h : HEdge a b) :
    snakeOf C a b = if C b then snakeBoth h else snakeThrough h := by
  rw [snakeOf, dif_pos h]

open Classical in
omit [Fintype A] in
theorem snakeOf_ne_nil {C : A → Prop} {a b : A} (h : HEdge a b) : snakeOf C a b ≠ [] := by
  rw [snakeOf_eq h]; split
  · exact snakeBoth_ne_nil h
  · exact snakeThrough_ne_nil h

open Classical in
omit [Fintype A] in
theorem snakeOf_isChain {C : A → Prop} {a b : A} (h : HEdge a b) :
    (snakeOf C a b).IsChain DGEdge := by
  rw [snakeOf_eq h]; split
  · exact snakeBoth_isChain h
  · exact snakeThrough_isChain h

open Classical in
omit [Fintype A] in
theorem snakeOf_head? {C : A → Prop} {a b : A} (h : HEdge a b) :
    (snakeOf C a b).head? = some (gv0 h) := by
  rw [snakeOf_eq h]; split <;> simp

open Classical in
omit [Fintype A] in
theorem snakeOf_getLast? {C : A → Prop} {a b : A} (h : HEdge a b) :
    (snakeOf C a b).getLast? = some (gv5 h) := by
  rw [snakeOf_eq h]; split <;> simp

open Classical in
/-- The chain of the cover vertex `a`: its gadgets' snakes, concatenated in
neighbor order. -/
noncomputable def chain (C : A → Prop) (a : A) : List (hamInterp.MapRel A) :=
  (nbrList a).flatMap (snakeOf C a)

/-- **A chain is a `DGEdge`-chain**: the snakes are chains and consecutive ones
connect via `DescriptiveComplexity.chain_edge`. -/
theorem chain_isChain (C : A → Prop) (a : A) : (chain C a).IsChain DGEdge := by
  have hne : [] ∉ (nbrList a).map (snakeOf C a) := by
    rw [List.mem_map]; rintro ⟨b, hb, hnil⟩
    exact snakeOf_ne_nil (mem_nbrList.mp hb) hnil
  rw [chain, List.flatMap_def, List.isChain_flatten hne]
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [List.mem_map] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    exact snakeOf_isChain (mem_nbrList.mp hb)
  · rw [List.isChain_map]
    refine (nbrList_isChain a).imp_of_mem_imp (fun b c hb hc hR => ?_)
    intro x hx y hy
    rw [snakeOf_getLast? (mem_nbrList.mp hb)] at hx
    rw [snakeOf_head? (mem_nbrList.mp hc)] at hy
    simp only [Option.mem_some_iff] at hx hy
    subst hx; subst hy
    exact hR (mem_nbrList.mp hb) (mem_nbrList.mp hc)

/-! #### Minima and maxima of the neighbor list -/

/-- The head of the neighbor list is the least neighbor. -/
theorem head_nbrList_le {a : A} (hne : nbrList a ≠ []) {d : A} (hd : HEdge a d) :
    (nbrList a).head hne ≤ d := by
  have hmono : StrictMono (nbrList a).get := nbrList_sortedLT a
  have h0 : 0 < (nbrList a).length := List.length_pos_of_ne_nil hne
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (mem_nbrList.mpr hd)
  have hhead : (nbrList a).head hne = (nbrList a).get ⟨0, h0⟩ := by
    rw [List.head_eq_getElem_zero, List.get_eq_getElem]
  rw [hhead]
  exact hmono.le_iff_le.mpr (by simp only [Fin.le_def]; omega)

/-- The last of the neighbor list is the greatest neighbor. -/
theorem le_getLast_nbrList {a : A} (hne : nbrList a ≠ []) {d : A} (hd : HEdge a d) :
    d ≤ (nbrList a).getLast hne := by
  have hmono : StrictMono (nbrList a).get := nbrList_sortedLT a
  have h0 : (nbrList a).length - 1 < (nbrList a).length := by
    have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (mem_nbrList.mpr hd)
  rw [(List.get_length_sub_one h0).symm]
  exact hmono.le_iff_le.mpr (by simp only [Fin.le_def]; have := j.isLt; omega)

/-! #### Selector edges -/

omit [Fintype A] in
/-- A selector is adjacent to a chain entrance `⟨g0,(a,b)⟩` when `b` is the least
neighbor of `a`. -/
theorem sel_entrance_edge {m a b : A} (hm : MGMarked m) (h : HEdge a b)
    (hmin : ∀ d, HEdge a d → b ≤ d) : DGEdge (selPt hm) (gv0 h) := by
  rw [dgEdge_iff]
  simp only [IAdjRaw, selPt_tag, gPt_tag, gPt_fst]
  exact hmin

omit [Fintype A] in
/-- A selector is adjacent to a chain exit `⟨g5,(a,b)⟩` when `b` is the greatest
neighbor of `a`. -/
theorem exit_sel_edge {m a b : A} (hm : MGMarked m) (h : HEdge a b)
    (hmax : ∀ d, HEdge a d → d ≤ b) : DGEdge (gv5 h) (selPt hm) := by
  rw [dgEdge_iff]
  simp only [IAdjRaw, selPt_tag, gPt_tag, gPt_fst]
  exact hmax

omit [Fintype A] in
/-- Selectors are mutually adjacent (a self-looped clique). -/
theorem sel_sel_edge {m m' : A} (hm : MGMarked m) (hm' : MGMarked m') :
    DGEdge (selPt hm) (selPt hm') := by
  rw [dgEdge_iff]; trivial

/-! #### Which vertices a chain contains (for covering) -/

open Classical in
omit [Fintype A] in
/-- Every `a`-side gadget vertex is in `a`'s snake for `b`, whichever snake it is. -/
theorem mem_snakeOf_owner {C : A → Prop} {a b : A} (h : HEdge a b) (i : HTag)
    (hi : i ≠ .sel ∧ i ≠ .hub) : gPt i hi h ∈ snakeOf C a b := by
  rw [snakeOf_eq h]; split
  · exact mem_snakeBoth_owner h i hi
  · exact mem_snakeThrough_near h i hi

/-- **A gadget vertex is in its owner's chain**: `⟨i,(a,b)⟩` is visited by `a`'s
chain (for any cover `C`). -/
theorem gadget_mem_chain {C : A → Prop} {a b : A} (h : HEdge a b) (i : HTag)
    (hi : i ≠ .sel ∧ i ≠ .hub) : gPt i hi h ∈ chain C a := by
  rw [chain, List.mem_flatMap]
  exact ⟨b, mem_nbrList.mpr h, mem_snakeOf_owner h i hi⟩

/-- **A gadget vertex is in the far endpoint's chain when its owner is uncovered**:
if `a ∉ C`, the vertex `⟨i,(a,b)⟩` is visited by `b`'s through-traversal. -/
theorem gadget_mem_chain_far {C : A → Prop} {a b : A} (hab : HEdge a b) (i : HTag)
    (hi : i ≠ .sel ∧ i ≠ .hub) (hnc : ¬C a) : gPt i hi hab ∈ chain C b := by
  rw [chain, List.mem_flatMap]
  refine ⟨a, mem_nbrList.mpr (hEdge_symm hab), ?_⟩
  rw [snakeOf_eq (hEdge_symm hab), if_neg hnc]
  exact mem_snakeThrough_far (hEdge_symm hab) i hi hab

/-! #### The endpoints of a chain -/

/-- **A chain's first vertex is the entrance `⟨g0,(a,b)⟩` of the least-neighbor
gadget** – which a selector is adjacent to. -/
theorem chain_head? (C : A → Prop) (a : A) (hne : nbrList a ≠ []) :
    ∃ (b : A) (h : HEdge a b), (∀ d, HEdge a d → b ≤ d) ∧ (chain C a).head? = some (gv0 h) := by
  obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hne
  have hb : HEdge a b := mem_nbrList.mp (by rw [hbt]; exact List.mem_cons_self)
  have hhead : (nbrList a).head hne = b :=
    Option.some.inj ((List.head?_eq_some_head hne).symm.trans (by rw [hbt]; rfl))
  refine ⟨b, hb, fun d hd => hhead ▸ head_nbrList_le hne hd, ?_⟩
  rw [chain, hbt, List.flatMap_cons,
    List.head?_append_of_ne_nil _ (snakeOf_ne_nil hb), snakeOf_head? hb]

/-- **A chain's last vertex is the exit `⟨g5,(a,b)⟩` of the greatest-neighbor
gadget** – which a selector is adjacent to. -/
theorem chain_getLast? (C : A → Prop) (a : A) (hne : nbrList a ≠ []) :
    ∃ (b : A) (h : HEdge a b), (∀ d, HEdge a d → d ≤ b) ∧ (chain C a).getLast? = some (gv5 h) := by
  set z := (nbrList a).getLast hne with hz
  have hzmem : z ∈ nbrList a := List.getLast_mem hne
  have hb : HEdge a z := mem_nbrList.mp hzmem
  refine ⟨z, hb, fun d hd => le_getLast_nbrList hne hd, ?_⟩
  have hsplit : nbrList a = (nbrList a).dropLast ++ [z] := (List.dropLast_append_getLast hne).symm
  rw [chain]
  conv_lhs => rw [hsplit]
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.getLast?_append_of_ne_nil _ (snakeOf_ne_nil hb), snakeOf_getLast? hb]

/-! #### Chains of distinct cover vertices are disjoint -/

omit [Fintype A] in
theorem snakeBoth_tuple {a b : A} (h : HEdge a b) {p : hamInterp.MapRel A}
    (hp : p ∈ snakeBoth h) : p.1.2 0 = a ∧ p.1.2 1 = b := by
  simp only [snakeBoth, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

omit [Fintype A] in
theorem snakeThrough_tuple {a b : A} (h : HEdge a b) {p : hamInterp.MapRel A}
    (hp : p ∈ snakeThrough h) : (p.1.2 0 = a ∧ p.1.2 1 = b) ∨ (p.1.2 0 = b ∧ p.1.2 1 = a) := by
  simp only [snakeThrough, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-- **The owner invariant of a chain**: a vertex of `w`'s chain is either owned
by `w` (`w`-side) or owned by an *uncovered* neighbor of `w` (the far side of a
through-traversal). -/
theorem chain_tuple {C : A → Prop} {w : A} {p : hamInterp.MapRel A} (hp : p ∈ chain C w) :
    p.1.2 0 = w ∨ (p.1.2 1 = w ∧ ¬C (p.1.2 0)) := by
  rw [chain, List.mem_flatMap] at hp
  obtain ⟨b, hbmem, hp⟩ := hp
  have hwb : HEdge w b := mem_nbrList.mp hbmem
  rw [snakeOf_eq hwb] at hp
  by_cases hCb : C b
  · rw [if_pos hCb] at hp
    exact Or.inl (snakeBoth_tuple hwb hp).1
  · rw [if_neg hCb] at hp
    rcases snakeThrough_tuple hwb hp with ⟨h0, -⟩ | ⟨h0, h1⟩
    · exact Or.inl h0
    · exact Or.inr ⟨h1, by rw [h0]; exact hCb⟩

/-- **Chains of distinct cover vertices are disjoint.** Their only possible
overlap is a far-side vertex, which requires an *uncovered* owner – but both
cover vertices are covered. -/
theorem chain_disjoint {C : A → Prop} {w w' : A} (hw : C w) (hw' : C w') (hne : w ≠ w') :
    (chain C w).Disjoint (chain C w') := by
  intro p hpw hpw'
  rcases chain_tuple hpw with h1 | ⟨h1, h1c⟩ <;> rcases chain_tuple hpw' with h2 | ⟨h2, h2c⟩
  · exact hne (h1.symm.trans h2)
  · exact h2c (by rw [h1]; exact hw)
  · exact h1c (by rw [h2]; exact hw')
  · exact hne (h1.symm.trans h2)

omit [Fintype A] in
theorem snakeOf_tuple {C : A → Prop} {w b : A} (hwb : HEdge w b) {p : hamInterp.MapRel A}
    (hp : p ∈ snakeOf C w b) : (p.1.2 0 = w ∧ p.1.2 1 = b) ∨ (p.1.2 0 = b ∧ p.1.2 1 = w) := by
  rw [snakeOf_eq hwb] at hp
  by_cases hCb : C b
  · rw [if_pos hCb] at hp; exact Or.inl (snakeBoth_tuple hwb hp)
  · rw [if_neg hCb] at hp; exact snakeThrough_tuple hwb hp

omit [Fintype A] in
/-- Snakes of distinct neighbors of `w` are disjoint. -/
theorem snakeOf_disjoint {C : A → Prop} {w b b' : A} (hwb : HEdge w b) (hwb' : HEdge w b')
    (hbb : b ≠ b') : (snakeOf C w b).Disjoint (snakeOf C w b') := by
  intro p hp hp'
  rcases snakeOf_tuple hwb hp with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
    rcases snakeOf_tuple hwb' hp' with ⟨f0, f1⟩ | ⟨f0, f1⟩
  · exact hbb (e1.symm.trans f1)
  · exact hwb'.2 (e0.symm.trans f0)
  · exact hwb.2 (f0.symm.trans e0)
  · exact hbb (e0.symm.trans f0)

open Classical in
/-- **A single chain is duplicate-free**: its snakes are internally nodup and
pairwise disjoint (distinct neighbors ⇒ distinct gadgets). -/
theorem chain_nodup (C : A → Prop) (w : A) : (chain C w).Nodup := by
  rw [chain, List.nodup_flatMap]
  refine ⟨fun b hb => ?_,
    (nbrList_nodup w).pairwise_of_forall_ne fun b hb b' hb' hbb => ?_⟩
  · rw [snakeOf_eq (mem_nbrList.mp hb)]; split
    · exact snakeBoth_nodup _
    · exact snakeThrough_nodup _
  · exact snakeOf_disjoint (mem_nbrList.mp hb) (mem_nbrList.mp hb') hbb

/-- Chain vertices are gadget vertices, never selectors. -/
theorem chain_tag {C : A → Prop} {w : A} {p : hamInterp.MapRel A} (hp : p ∈ chain C w) :
    p.1.1 ≠ HTag.sel := by
  rw [chain, List.mem_flatMap] at hp
  obtain ⟨b, hb, hp⟩ := hp
  rw [snakeOf_eq (mem_nbrList.mp hb)] at hp
  split at hp <;>
    · simp only [snakeBoth, snakeThrough, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A selector is never a chain vertex. -/
theorem selPt_not_mem_chain {C : A → Prop} {w m : A} (hm : MGMarked m) :
    selPt hm ∉ chain C w := fun hmem => chain_tag hmem rfl

end Chain

/-! ### The blocks of the cycle -/

section Blocks

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A] {C : A → Prop}

/-- A chain over a nonempty neighbor list is nonempty. -/
theorem chain_ne_nil {w : A} (hne : nbrList w ≠ []) : chain C w ≠ [] := by
  obtain ⟨b, _, _, hhead⟩ := chain_head? C w hne
  intro h; rw [h] at hhead; simp at hhead

/-- A block of the cycle: a selector, optionally followed by a cover vertex's
chain. The `cp` is that chain when the selector is paired with a cover vertex,
and `[]` for a leftover selector. -/
def block {m : A} (hm : MGMarked m) (cp : List (hamInterp.MapRel A)) : List (hamInterp.MapRel A) :=
  selPt hm :: cp

omit [Fintype A] in
theorem block_ne_nil {m : A} (hm : MGMarked m) (cp) : block hm cp ≠ [] := by simp [block]

omit [Fintype A] in
theorem block_head? {m : A} (hm : MGMarked m) (cp) : (block hm cp).head? = some (selPt hm) := rfl

/-- Every paired block is a `DGEdge`-chain: the selector connects to the chain's
entrance and the chain is a chain. -/
theorem block_isChain_paired {m w : A} (hm : MGMarked m) (hne : nbrList w ≠ []) :
    (block hm (chain C w)).IsChain DGEdge := by
  rw [block, List.isChain_cons]
  refine ⟨fun y hy => ?_, chain_isChain C w⟩
  obtain ⟨b, hb, hmin, hhead⟩ := chain_head? C w hne
  rw [hhead] at hy
  simp only [Option.mem_some_iff] at hy
  subst hy
  exact sel_entrance_edge hm hb hmin

omit [Fintype A] in
theorem block_isChain_extra {m : A} (hm : MGMarked m) :
    (block hm ([] : List (hamInterp.MapRel A))).IsChain DGEdge := by
  rw [block]; exact List.isChain_singleton _

/-- The last vertex of a paired block (a chain exit) is adjacent to any
selector. -/
theorem block_getLast_paired_adj {m m' w : A} (hm : MGMarked m) (hm' : MGMarked m')
    (hne : nbrList w ≠ []) {x : hamInterp.MapRel A}
    (hx : x ∈ (block hm (chain C w)).getLast?) : DGEdge x (selPt hm') := by
  rw [block, List.getLast?_cons_of_ne_nil (chain_ne_nil hne)] at hx
  obtain ⟨b, hb, hmax, hlast⟩ := chain_getLast? C w hne
  rw [hlast] at hx
  simp only [Option.mem_some_iff] at hx
  subst hx
  exact exit_sel_edge hm' hb hmax

omit [Fintype A] in
/-- The last vertex of an extra block (its selector) is adjacent to any
selector. -/
theorem block_getLast_extra_adj {m m' : A} (hm : MGMarked m) (hm' : MGMarked m')
    {x : hamInterp.MapRel A} (hx : x ∈ (block hm ([] : List (hamInterp.MapRel A))).getLast?) :
    DGEdge x (selPt hm') := by
  rw [block] at hx
  simp only [List.getLast?_singleton, Option.mem_some_iff] at hx
  subst hx
  exact sel_sel_edge hm hm'

end Blocks

/-! ### The marked and cover lists -/

section Lists

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A] (C : A → Prop)

open Classical in
/-- The marked vertices of the input: the selectors. -/
noncomputable def markedList : List A := (Finset.univ.filter fun m : A => MGMarked m).toList

open Classical in
/-- The non-isolated cover vertices: those whose chain is nonempty. -/
noncomputable def coverList : List A :=
  (Finset.univ.filter fun w : A => C w ∧ nbrList w ≠ []).toList

variable {C}

omit [LinearOrder A] in
theorem mem_markedList {m : A} : m ∈ markedList ↔ MGMarked m := by
  simp [markedList]

theorem mem_coverList {w : A} : w ∈ coverList C ↔ C w ∧ nbrList w ≠ [] := by
  simp [coverList]

omit [LinearOrder A] in
theorem markedList_nodup : (markedList (A := A)).Nodup := Finset.nodup_toList _

theorem coverList_nodup : (coverList C).Nodup := Finset.nodup_toList _

/-- There are at most as many cover vertices as selectors, from the vertex-cover
threshold. -/
theorem coverList_length_le (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard) :
    (coverList C).length ≤ (markedList (A := A)).length := by
  classical
  rw [markedList, coverList, Finset.length_toList, Finset.length_toList]
  have hsub : (Finset.univ.filter fun w : A => C w ∧ nbrList w ≠ []) ⊆
      (Finset.univ.filter fun w : A => C w) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.filter fun w : A => C w).card = {x : A | C x}.ncard := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp
  have h3 : (Finset.univ.filter fun m : A => MGMarked m).card = {x : A | MGMarked x}.ncard := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp
  omega

end Lists

/-! ### The cycle and its correctness -/

section Cycle

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A] {C : A → Prop}

open Classical in
/-- The blocks of the cycle: the first `|coverList|` selectors each followed by
their paired cover vertex's chain, then the leftover selectors alone. -/
noncomputable def blockList (C : A → Prop) : List (List (hamInterp.MapRel A)) :=
  ((coverList C).attach.zip ((markedList (A := A)).attach.take (coverList C).length)).map
      (fun p => block (mem_markedList.mp p.2.2) (chain C p.1.1)) ++
    ((markedList (A := A)).attach.drop (coverList C).length).map
      (fun s => block (mem_markedList.mp s.2) [])

/-- Every block of the list is a selector followed by a chain, or a lone
selector – both nonempty and starting with a selector. -/
theorem block_of_mem_blockList {bl : List (hamInterp.MapRel A)} (hbl : bl ∈ blockList C) :
    (∃ (m w : A) (hm : MGMarked m), C w ∧ nbrList w ≠ [] ∧ bl = block hm (chain C w)) ∨
      (∃ (m : A) (hm : MGMarked m), bl = block hm []) := by
  rw [blockList, List.mem_append] at hbl
  rcases hbl with hbl | hbl
  · rw [List.mem_map] at hbl
    obtain ⟨p, -, rfl⟩ := hbl
    obtain ⟨hc, hne⟩ := mem_coverList.mp p.1.2
    exact Or.inl ⟨p.2.1, p.1.1, mem_markedList.mp p.2.2, hc, hne, rfl⟩
  · rw [List.mem_map] at hbl
    obtain ⟨s, -, rfl⟩ := hbl
    exact Or.inr ⟨s.1, mem_markedList.mp s.2, rfl⟩

/-- No block is empty. -/
theorem blockList_ne_nil_mem : [] ∉ blockList C := by
  intro h
  rcases block_of_mem_blockList h with ⟨m, w, hm, -, -, he⟩ | ⟨m, hm, he⟩ <;>
    exact block_ne_nil hm _ he.symm

/-- Every block is a `DGEdge`-chain. -/
theorem blockList_isChain_mem {bl : List (hamInterp.MapRel A)} (hbl : bl ∈ blockList C) :
    bl.IsChain DGEdge := by
  rcases block_of_mem_blockList hbl with ⟨m, w, hm, -, hne, rfl⟩ | ⟨m, hm, rfl⟩
  · exact block_isChain_paired hm hne
  · exact block_isChain_extra hm

/-- **Consecutive blocks connect** – in fact every pair does, since every block
starts with a selector and every block's last vertex is adjacent to every
selector. -/
theorem blockList_isChain_conn :
    (blockList C).IsChain
      (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, DGEdge x y) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro b1 b2 L1 L2 heq x hx y hy
  have hb1 : b1 ∈ blockList C := by rw [heq]; simp
  have hb2 : b2 ∈ blockList C := by rw [heq]; simp
  rcases block_of_mem_blockList hb2 with ⟨m2, w2, hm2, -, -, rfl⟩ | ⟨m2, hm2, rfl⟩ <;>
    · rw [block_head?] at hy
      simp only [Option.mem_some_iff] at hy
      subst hy
      rcases block_of_mem_blockList hb1 with ⟨m1, w1, hm1, -, hne1, rfl⟩ | ⟨m1, hm1, rfl⟩
      · exact block_getLast_paired_adj hm1 hm2 hne1 hx
      · exact block_getLast_extra_adj hm1 hm2 hx

omit [Fintype A] in
/-- Two blocks with distinct selectors and appropriately disjoint chain parts are
disjoint. -/
theorem block_disjoint {m1 m2 : A} (hm1 : MGMarked m1) (hm2 : MGMarked m2)
    {cp1 cp2 : List (hamInterp.MapRel A)} (hmm : m1 ≠ m2) (hcp : cp1.Disjoint cp2)
    (h1 : selPt hm1 ∉ cp2) (h2 : selPt hm2 ∉ cp1) :
    (block hm1 cp1).Disjoint (block hm2 cp2) := by
  rw [block, block]
  intro x hx hx'
  rw [List.mem_cons] at hx hx'
  rcases hx with rfl | hx <;> rcases hx' with hx' | hx'
  · exact hmm (congrArg (fun p : hamInterp.MapRel A => p.1.2 0) hx')
  · exact h1 hx'
  · exact h2 (hx' ▸ hx)
  · exact hcp hx hx'

end Cycle

section ZipHelpers

variable {α β : Type}

/-- Every element of the first list is paired by `zip` when it is no longer than
the second. -/
theorem mem_zip_left {l₁ : List α} {l₂ : List β} (hlen : l₁.length ≤ l₂.length) {x : α}
    (hx : x ∈ l₁) : ∃ y, (x, y) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  have hiz : i < (l₁.zip l₂).length := by rw [List.length_zip]; omega
  refine ⟨l₂[i]'(by omega), ?_⟩
  have hm := List.getElem_mem hiz
  rwa [List.getElem_zip, hix] at hm

/-- Every element of the second list is paired by `zip` when it is no longer than
the first. -/
theorem mem_zip_right {l₁ : List α} {l₂ : List β} (hlen : l₂.length ≤ l₁.length) {y : β}
    (hy : y ∈ l₂) : ∃ x, (x, y) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  have hiz : i < (l₁.zip l₂).length := by rw [List.length_zip]; omega
  refine ⟨l₁[i]'(by omega), ?_⟩
  have hm := List.getElem_mem hiz
  rwa [List.getElem_zip, hiy] at hm

/-- Zipping two duplicate-free lists gives a list whose pairs differ in **both**
components. -/
theorem zip_pairwise_both {l₁ : List α} {l₂ : List β} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    (l₁.zip l₂).Pairwise (fun p q => p.1 ≠ q.1 ∧ p.2 ≠ q.2) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_zip] at hi hj
  rw [List.getElem_zip, List.getElem_zip]
  exact ⟨fun he => absurd (h₁.getElem_inj_iff.mp he) (Nat.ne_of_lt hij),
    fun he => absurd (h₂.getElem_inj_iff.mp he) (Nat.ne_of_lt hij)⟩

end ZipHelpers

section Covering

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] [Fintype A] {C : A → Prop}

/-- **Every cover vertex's chain is in the cycle**: a cover vertex is paired with
a selector, so its chain sits in a paired block. -/
theorem chain_sub_flatten (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard)
    {w : A} (hw : w ∈ coverList C) : chain C w ⊆ (blockList C).flatten := by
  have hle : (coverList C).attach.length ≤
      ((markedList (A := A)).attach.take (coverList C).length).length := by
    rw [List.length_attach, List.length_take, List.length_attach]
    have := coverList_length_le hcard; omega
  obtain ⟨s, hs⟩ := mem_zip_left hle (List.mem_attach _ ⟨w, hw⟩)
  intro x hx
  rw [List.mem_flatten]
  refine ⟨block (mem_markedList.mp s.2) (chain C w), ?_, ?_⟩
  · rw [blockList, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨(⟨w, hw⟩, s), hs, rfl⟩)
  · rw [block]; exact List.mem_cons_of_mem _ hx

/-- **Every selector is in the cycle**: it heads either a paired block (if among
the first `|coverList|` selectors) or a leftover block. -/
theorem selPt_mem_flatten (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard)
    {m : A} (hm : MGMarked m) : selPt hm ∈ (blockList C).flatten := by
  have hmm : m ∈ markedList := mem_markedList.mpr hm
  rw [← List.take_append_drop (coverList C).length (markedList (A := A)), List.mem_append] at hmm
  rw [List.mem_flatten]
  rcases hmm with hmt | hmd
  · have hmap : m ∈ ((markedList (A := A)).attach.take (coverList C).length).map Subtype.val := by
      rw [List.map_take, List.attach_map_subtype_val]; exact hmt
    rw [List.mem_map] at hmap
    obtain ⟨s, hs1, rfl⟩ := hmap
    have hle : ((markedList (A := A)).attach.take (coverList C).length).length ≤
        (coverList C).attach.length := by
      rw [List.length_take, List.length_attach, List.length_attach]
      have := coverList_length_le hcard; omega
    obtain ⟨c, hc⟩ := mem_zip_right hle hs1
    refine ⟨block (mem_markedList.mp s.2) (chain C c.1), ?_,
      by rw [block]; exact List.mem_cons_self⟩
    rw [blockList, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨(c, s), hc, rfl⟩)
  · have hmap : m ∈ ((markedList (A := A)).attach.drop (coverList C).length).map Subtype.val := by
      rw [List.map_drop, List.attach_map_subtype_val]; exact hmd
    rw [List.mem_map] at hmap
    obtain ⟨s, hs1, rfl⟩ := hmap
    refine ⟨block (mem_markedList.mp s.2) [], ?_, by rw [block]; exact List.mem_cons_self⟩
    rw [blockList, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨s, hs1, rfl⟩)

/-- **Covering**: every vertex of the interpreted graph is in the cycle. A
selector heads a block; a gadget vertex sits in a covered endpoint's chain (its
owner's if covered, the neighbor's otherwise); the hub cannot occur, since
there is a selector. -/
theorem blockList_covers (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard)
    (hcover : ∀ a b : A, HEdge a b → C a ∨ C b) (hmarks : ∃ m : A, MGMarked m)
    (v : hamInterp.MapRel A) : v ∈ (blockList C).flatten := by
  rcases point_cases v with ⟨t, ht, h, hv⟩ | ⟨hmk, -, hv⟩ | hhub
  · rw [hv]
    by_cases hca : C (v.1.2 0)
    · exact chain_sub_flatten hcard
        (mem_coverList.mpr ⟨hca, List.ne_nil_of_mem (mem_nbrList.mpr h)⟩)
        (gadget_mem_chain h t ht)
    · exact chain_sub_flatten hcard
        (mem_coverList.mpr ⟨(hcover _ _ h).resolve_left hca,
          List.ne_nil_of_mem (mem_nbrList.mpr (hEdge_symm h))⟩)
        (gadget_mem_chain_far h t ht hca)
  · rw [hv]; exact selPt_mem_flatten hcard hmk
  · obtain ⟨_, _, hnm, -⟩ := (dom_hub v.1.2).mp (hhub ▸ v.2)
    obtain ⟨m, hmm⟩ := hmarks
    exact absurd hmm (hnm m)

/-- The cycle is nonempty when there is a selector. -/
theorem blockList_flatten_ne_nil (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard)
    (hmarks : ∃ m : A, MGMarked m) : (blockList C).flatten ≠ [] := by
  obtain ⟨m, hm⟩ := hmarks
  exact List.ne_nil_of_mem (selPt_mem_flatten hcard hm)

/-- Each block is duplicate-free. -/
theorem blockList_block_nodup {bl : List (hamInterp.MapRel A)} (hbl : bl ∈ blockList C) :
    bl.Nodup := by
  rcases block_of_mem_blockList hbl with ⟨m, w, hm, -, -, rfl⟩ | ⟨m, hm, rfl⟩
  · exact List.nodup_cons.mpr ⟨selPt_not_mem_chain hm, chain_nodup C w⟩
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

/-- The blocks are pairwise disjoint: distinct selectors, and distinct cover
vertices give disjoint chains. -/
theorem blockList_pairwise_disjoint : (blockList C).Pairwise List.Disjoint := by
  have hmn : (markedList (A := A)).attach.Nodup := List.nodup_attach.mpr markedList_nodup
  have hcn : (coverList C).attach.Nodup := List.nodup_attach.mpr coverList_nodup
  have htd : ∀ a ∈ (markedList (A := A)).attach.take (coverList C).length,
      ∀ b ∈ (markedList (A := A)).attach.drop (coverList C).length, a ≠ b :=
    (List.nodup_append.mp (by rw [List.take_append_drop]; exact hmn)).2.2
  rw [blockList, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (zip_pairwise_both hcn hmn.take).imp ?_
    rintro ⟨c1, s1⟩ ⟨c2, s2⟩ ⟨hc, hs⟩
    obtain ⟨hcp1, -⟩ := mem_coverList.mp c1.2
    obtain ⟨hcp2, -⟩ := mem_coverList.mp c2.2
    exact block_disjoint _ _ (fun h => hs (Subtype.ext h))
      (chain_disjoint hcp1 hcp2 (fun h => hc (Subtype.ext h)))
      (selPt_not_mem_chain _) (selPt_not_mem_chain _)
  · rw [List.pairwise_map]
    refine hmn.drop.imp ?_
    rintro s s' hss
    exact block_disjoint _ _ (fun h => hss (Subtype.ext h)) (List.disjoint_nil_left _)
      List.not_mem_nil List.not_mem_nil
  · rintro pb hpb eb heb
    rw [List.mem_map] at hpb heb
    obtain ⟨⟨c, s⟩, hcs, rfl⟩ := hpb
    obtain ⟨s', hs', rfl⟩ := heb
    exact block_disjoint _ _ (fun h => htd s (List.of_mem_zip hcs).2 s' hs' (Subtype.ext h))
      (List.disjoint_nil_right _) List.not_mem_nil (selPt_not_mem_chain _)

/-- **The cycle is duplicate-free.** -/
theorem blockList_flatten_nodup : (blockList C).flatten.Nodup :=
  List.nodup_flatten.mpr ⟨fun _ => blockList_block_nodup, blockList_pairwise_disjoint⟩

/-- **The wrap edge**: the last vertex of the cycle is adjacent to the first (a
selector), since every block's last vertex is adjacent to every selector. -/
theorem blockList_wrap : ∀ x ∈ (blockList C).flatten.getLast?,
    ∀ y ∈ (blockList C).flatten.head?, DGEdge x y := by
  intro x hx y hy
  have hfl : (blockList C).flatten ≠ [] := by rintro h; rw [h] at hx; simp at hx
  have hbl : blockList C ≠ [] := by rintro h; rw [h] at hfl; simp at hfl
  have hb0 : (blockList C).head hbl ≠ [] := fun h => blockList_ne_nil_mem (h ▸ List.head_mem hbl)
  have hbL : (blockList C).getLast hbl ≠ [] :=
    fun h => blockList_ne_nil_mem (h ▸ List.getLast_mem hbl)
  have hh : (blockList C).flatten.head? = ((blockList C).head hbl).head? := by
    rw [List.head?_eq_some_head hfl, List.head?_eq_some_head hb0]
    exact congrArg some (List.head_flatten_eq_head_head hfl hb0)
  have hg : (blockList C).flatten.getLast? = ((blockList C).getLast hbl).getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hfl, List.getLast?_eq_getLast_of_ne_nil hbL]
    exact congrArg some (List.getLast_flatten_eq_getLast_getLast hfl hbL)
  rw [hh] at hy
  rw [hg] at hx
  obtain ⟨m, hm, hysel⟩ : ∃ (m : A) (hm : MGMarked m), y = selPt hm := by
    rcases block_of_mem_blockList (List.head_mem hbl) with ⟨m, w, hm, -, -, he0⟩ | ⟨m, hm, he0⟩ <;>
      · rw [he0, block_head?, Option.mem_some_iff] at hy
        exact ⟨m, hm, hy.symm⟩
  subst hysel
  rcases block_of_mem_blockList (List.getLast_mem hbl) with
    ⟨m', w', hm', -, hne', heL⟩ | ⟨m', hm', heL⟩
  · rw [heL] at hx; exact block_getLast_paired_adj hm' hm hne' hx
  · rw [heL] at hx; exact block_getLast_extra_adj hm' hm hx

omit [Fintype A] in
/-- **The non-degenerate forward direction**: given a cover with at most as many
vertices as the marked set, at least one marked vertex, and covering every edge,
the gadget graph has a Hamilton circuit – the cycle of selectors and chains. -/
theorem blockCycle_tourOn [Finite A] (hcard : {x : A | C x}.ncard ≤ {x : A | MGMarked x}.ncard)
    (hcover : ∀ a b : A, HEdge a b → C a ∨ C b) (hmarks : ∃ m : A, MGMarked m) :
    TourOn (DGEdge (A := hamInterp.MapRel A)) := by
  have := Fintype.ofFinite A
  have : Finite (hamInterp.MapRel A) := hamInterp.mapRel_finite A
  exact tourOn_of_blocks (blockList C) blockList_ne_nil_mem
    (blockList_flatten_ne_nil hcard hmarks) blockList_flatten_nodup
    (blockList_covers hcard hcover hmarks) (fun _ hl => blockList_isChain_mem hl)
    blockList_isChain_conn blockList_wrap

omit [Fintype A] in
/-- **The degenerate forward direction**: with no marked vertices and no edges,
the interpreted graph is the single self-looped hub, a one-element Hamilton
circuit. -/
theorem degenerate_tourOn [Finite A] [Nonempty A] (hnm : ∀ y : A, ¬MGMarked y)
    (hne : ∀ y z : A, ¬HEdge y z) : TourOn (DGEdge (A := hamInterp.MapRel A)) := by
  have := Fintype.ofFinite A
  have : Finite (hamInterp.MapRel A) := hamInterp.mapRel_finite A
  obtain ⟨m, hmin⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  refine tourOn_of_cycleList [hubPt hmin hnm hne] (by simp) (by simp) ?_
    (List.isChain_singleton _) ((dgEdge_iff _ _).mpr trivial)
  intro v
  rw [List.mem_singleton]
  rcases point_cases v with ⟨t, ht, h, -⟩ | ⟨hmk, -, -⟩ | hhub
  · exact absurd h (hne _ _)
  · exact absurd hmk (hnm _)
  · obtain ⟨heq, hvmin, -, -⟩ := (dom_hub v.1.2).mp (hhub ▸ v.2)
    have hmeq : v.1.2 0 = m := le_antisymm (hvmin m) (hmin (v.1.2 0))
    apply Subtype.ext
    refine Prod.ext hhub ?_
    funext i
    fin_cases i
    · change v.1.2 0 = m; exact hmeq
    · change v.1.2 1 = m; exact heq.symm.trans hmeq

end Covering

end DescriptiveComplexity
