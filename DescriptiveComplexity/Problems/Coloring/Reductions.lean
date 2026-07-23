/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Coloring.Defs
import DescriptiveComplexity.Problems.CliqueFamily.Reductions
import DescriptiveComplexity.OrderWalk

/-!
# Reductions of the coloring family

Three reductions, one per problem of the family:

* `DescriptiveComplexity.threeCol_fo_reduction_kCol`: **3-colorability reduces to
  `k`-colorability** for every `k = 3 + m`, by padding the graph with `m`
  universal vertices. An interpretation cannot add constantly many elements to
  a universe, so the new vertices become *tags*, hence blown-up independent
  classes (`DescriptiveComplexity.padColorInterp`, tag type `Option (Fin m)`); this is
  harmless, because a proper coloring gives the classes pairwise disjoint sets
  of colors, all disjoint from the colors of the original part, leaving
  exactly three for it.

* `DescriptiveComplexity.threeCol_ordered_fo_reduction_chromaticNumber`:
  **3-colorability reduces to Chromatic Number**, an *ordered* reduction
  (`DescriptiveComplexity.chromInterp`, tag `Fin 4`, dimension 1). The graph is kept on
  the copy of tag `0`; the marked set must have exactly three elements, which
  no order-free interpretation can produce, so it is `{0, 1, 2} × {minimum}`,
  definable with `DescriptiveComplexity.minF`. The three spare copies are not only
  scaffolding for the threshold: the target problem ignores self-loops while
  3-colorability does not, so a self-looped vertex is turned into the `K₄`
  formed by its four copies, which no 3-coloring survives.

* `DescriptiveComplexity.chromaticNumber_fo_reduction_cliqueCover` and
  `DescriptiveComplexity.cliqueCover_fo_reduction_chromaticNumber`: the two threshold
  problems are **interreducible by edge complementation**, reusing
  `DescriptiveComplexity.complEdgeInterp` of the clique family unchanged: covering by
  cliques is coloring the complement, and complementing off the diagonal
  exchanges the two conflict relations while keeping the marked set.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### The padding interpretation

Tags are `Option (Fin m)`: the tag `none` carries the original graph, and
each tag `some i` carries one blown-up universal vertex. -/

/-- The padding interpretation adding `m` universal (blown-up) vertices to a
graph: the `none`-copy keeps the original adjacency, each `some i`-copy is an
independent set, and any two elements with different tags are adjacent. -/
def padColorInterp (m : ℕ) :
    FOInterpretation Language.graph Language.graph (Option (Fin m)) 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
      match t 0, t 1 with
      | none, none => adj.formula₂ (Term.var (0, 0)) (Term.var (1, 0))
      | none, some _ => ⊤
      | some _, none => ⊤
      | some i, some j => if i = j then ⊥ else ⊤

/-- The padding interpretation is quantifier-free. -/
theorem padColorInterp_isQuantifierFree (m : ℕ) :
    (padColorInterp m).IsQuantifierFree := by
  intro n R t
  cases R
  rcases h0 : t 0 with _ | i <;> rcases h1 : t 1 with _ | j <;>
    simp only [padColorInterp, h0, h1]
  · exact (IsAtomic.rel _ _).isQF
  · exact isQF_bot.imp isQF_bot
  · exact isQF_bot.imp isQF_bot
  · by_cases hij : i = j <;> simp only [hij, if_true, if_false]
    · exact isQF_bot
    · exact isQF_bot.imp isQF_bot

section Characterizations

variable {m : ℕ} {A : Type} [Language.graph.Structure A]

@[simp]
theorem padColor_adj_orig (w₁ w₂ : Fin 1 → A) :
    RelMap (M := (padColorInterp m).Map A) adj ![(none, w₁), (none, w₂)] ↔
      RelMap adj ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [padColorInterp, Formula.realize_rel₂]

@[simp]
theorem padColor_adj_left (i : Fin m) (w₁ w₂ : Fin 1 → A) :
    RelMap (M := (padColorInterp m).Map A) adj ![(some i, w₁), (none, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [padColorInterp]

@[simp]
theorem padColor_adj_right (i : Fin m) (w₁ w₂ : Fin 1 → A) :
    RelMap (M := (padColorInterp m).Map A) adj ![(none, w₁), (some i, w₂)] := by
  rw [FOInterpretation.relMap_map]
  simp [padColorInterp]

@[simp]
theorem padColor_adj_pad (i j : Fin m) (w₁ w₂ : Fin 1 → A) :
    RelMap (M := (padColorInterp m).Map A) adj ![(some i, w₁), (some j, w₂)] ↔ i ≠ j := by
  rw [FOInterpretation.relMap_map]
  by_cases hij : i = j <;> simp [padColorInterp, hij]

end Characterizations

/-! ### The two colors of the padded palette -/

section Palette

variable {m : ℕ}

/-- One of the first three colors of a palette of `3 + m`. -/
private def origColor (i : Fin 3) : Fin (3 + m) := ⟨i.1, by have := i.isLt; omega⟩

/-- One of the last `m` colors of a palette of `3 + m`. -/
private def padColor (j : Fin m) : Fin (3 + m) := ⟨3 + j.1, by have := j.isLt; omega⟩

private theorem origColor_injective : Function.Injective (origColor (m := m)) := by
  intro i j h
  have hv : (origColor i : Fin (3 + m)).1 = (origColor j).1 := congrArg Fin.val h
  simp only [origColor] at hv
  exact Fin.ext hv

private theorem origColor_ne_padColor (i : Fin 3) (j : Fin m) :
    origColor i ≠ padColor j := by
  intro h
  have := i.isLt
  have : (origColor i : Fin (3 + m)).1 = (padColor j).1 := congrArg Fin.val h
  simp only [origColor, padColor] at this
  omega

private theorem padColor_injective : Function.Injective (padColor (m := m)) := by
  intro i j h
  have : (padColor i : Fin (3 + m)).1 = (padColor j).1 := congrArg Fin.val h
  simp only [padColor] at this
  exact Fin.ext (by omega)

end Palette

/-! ### Correctness of the padding -/

section Correctness

variable {m : ℕ} {A : Type} [Language.graph.Structure A]

/-- The `k`-coloring of the padded graph built from a 3-coloring of the
input: the original copy keeps its three colors, and the `i`-th blown-up
universal vertex takes the `i`-th spare color. -/
private def paddedColoring (c : A → Fin 3) :
    Option (Fin m) × (Fin 1 → A) → Fin (3 + m) :=
  fun p => p.1.elim (origColor (c (p.2 0))) padColor

/-- A 3-coloring of a graph yields a `(3 + m)`-coloring of the padded
graph. -/
theorem kColorable_map_of_threeColorable (h : ThreeColorable A) :
    KColorable (3 + m) ((padColorInterp m).Map A) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨paddedColoring c, ?_⟩
  rintro ⟨(_ | i), w₁⟩ ⟨(_ | j), w₂⟩ hadj
  · exact fun h => hc (w₁ 0) (w₂ 0) ((padColor_adj_orig w₁ w₂).mp hadj)
      (origColor_injective h)
  · exact origColor_ne_padColor _ _
  · exact fun h => origColor_ne_padColor _ _ h.symm
  · exact fun h => (padColor_adj_pad i j w₁ w₂).mp hadj (padColor_injective h)

/-- A `(3 + m)`-coloring of the padded graph yields a 3-coloring of the
input: each of the `m` blown-up universal vertices consumes a color of its
own, all distinct from the colors of the original copy, which is therefore
left with at most three of them. (The input structure must be nonempty: an
empty class would consume no color.) -/
theorem threeColorable_of_kColorable_map [Nonempty A]
    (h : KColorable (3 + m) ((padColorInterp m).Map A)) : ThreeColorable A := by
  classical
  obtain ⟨c, hc⟩ := h
  obtain ⟨a₀⟩ := ‹Nonempty A›
  -- the color of the `i`-th blown-up universal vertex, read at `a₀`
  set d : Fin m → Fin (3 + m) := fun i => c (some i, fun _ => a₀) with hd
  have hdinj : Function.Injective d := by
    intro i j hij
    by_contra hne
    exact hc _ _ ((padColor_adj_pad i j (fun _ => a₀) fun _ => a₀).mpr hne) hij
  -- the colors of the original copy avoid all of them
  have horig : ∀ (x : A) (i : Fin m), c (none, fun _ => x) ≠ d i := fun x i =>
    hc _ _ (padColor_adj_right i (fun _ => x) fun _ => a₀)
  -- so they live in a set of exactly three colors
  set S : Finset (Fin (3 + m)) := Finset.univ \ Finset.image d Finset.univ with hS
  have hcard : S.card = 3 := by
    have himg : (Finset.image d Finset.univ).card = m := by
      rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin]
    rw [hS, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, himg]
    omega
  have hmem : ∀ x : A, c (none, fun _ => x) ∈ S := by
    intro x
    rw [hS, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact horig x i hi.symm
  let e : S ≃ Fin 3 := Finset.equivFinOfCardEq hcard
  refine ⟨fun x => e ⟨c (none, fun _ => x), hmem x⟩, fun x y hxy hcol => ?_⟩
  have hne : c (none, fun _ => x) ≠ c (none, fun _ => y) :=
    hc _ _ ((padColor_adj_orig (fun _ => x) fun _ => y).mpr (by simpa using hxy))
  exact hne (congrArg Subtype.val (e.injective hcol))

/-- Correctness of the padding interpretation. -/
theorem threeColorable_iff_kColorable_map [Nonempty A] :
    ThreeColorable A ↔ KColorable (3 + m) ((padColorInterp m).Map A) :=
  ⟨kColorable_map_of_threeColorable, threeColorable_of_kColorable_map⟩

end Correctness

/-- **3-colorability FO-reduces to `(3 + m)`-colorability**, by padding the
graph with `m` blown-up universal vertices. -/
def threeCol_fo_reduction_kCol (m : ℕ) : ThreeCol ≤ᶠᵒ KCol (3 + m) where
  Tag := Option (Fin m)
  dim := 1
  toInterpretation := padColorInterp m
  correct _ _ _ := threeColorable_iff_kColorable_map


/-! ### Chromatic Number and Clique Cover are complements of each other -/

section Complement

variable (A : Type) [Language.markedGraph.Structure A]

omit [Language.markedGraph.Structure A] in
private theorem complEdge_ne (w w' : Fin 1 → A) :
    (((), w) : complEdgeInterp.Map A) ≠ ((), w') ↔ w 0 ≠ w' 0 := by
  constructor
  · exact fun h heq => h (Prod.ext rfl (funext fun i => by
      rw [Subsingleton.elim i 0]; exact heq))
  · exact fun h heq => h (congrArg (fun r : complEdgeInterp.Map A => r.2 0) heq)

private theorem complEdge_conflict :
    ∀ p q : complEdgeInterp.Map A,
      MGCoConflict p q ↔ MGConflict (complEdgeInterp.mapEquivSelf A p)
        (complEdgeInterp.mapEquivSelf A q) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  have hadj := complEdge_adj (A := A) w w'
  have hne := complEdge_ne A w w'
  constructor
  · rintro ⟨hp, hcfl⟩
    have hw : w 0 ≠ w' 0 := hne.mp hp
    refine ⟨hw, ?_⟩
    rcases Classical.em (MGAdj (w 0) (w' 0)) with h | h
    · exact h
    · exact absurd (hadj.mpr ⟨hw, h⟩) hcfl
  · rintro ⟨hw, hadjw⟩
    exact ⟨hne.mpr hw, fun hcfl => (hadj.mp hcfl).2 hadjw⟩

private theorem complEdge_coconflict :
    ∀ p q : complEdgeInterp.Map A,
      MGConflict p q ↔ MGCoConflict (complEdgeInterp.mapEquivSelf A p)
        (complEdgeInterp.mapEquivSelf A q) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  have hadj := complEdge_adj (A := A) w w'
  have hne := complEdge_ne A w w'
  constructor
  · rintro ⟨hp, hcfl⟩
    exact ⟨hne.mp hp, (hadj.mp hcfl).2⟩
  · rintro ⟨hw, hcfl⟩
    exact ⟨hne.mpr hw, hadj.mpr ⟨hw, hcfl⟩⟩

private theorem complEdge_ncard_marked :
    {x : complEdgeInterp.Map A | MGMarked x}.ncard = {x : A | MGMarked x}.ncard :=
  ncard_setOf_equiv (complEdgeInterp.mapEquivSelf A) (by
    rintro ⟨⟨⟩, w⟩
    exact complEdge_marked w)

/-- Correctness of the edge complementation, chromatic-number-to-clique-cover
direction. -/
theorem hasSmallChromaticNumber_iff_cliqueCover_map :
    HasSmallChromaticNumber A ↔ HasSmallCliqueCover (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [complEdge_ncard_marked A]
  exact (ColorableOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_conflict A)).symm

/-- Correctness of the edge complementation, clique-cover-to-chromatic-number
direction. -/
theorem hasSmallCliqueCover_iff_chromaticNumber_map :
    HasSmallCliqueCover A ↔ HasSmallChromaticNumber (complEdgeInterp.Map A) := by
  refine and_congr ((complEdgeInterp.mapEquivSelf A).finite_iff).symm ?_
  rw [complEdge_ncard_marked A]
  exact (ColorableOn.equiv_iff (complEdgeInterp.mapEquivSelf A) (complEdge_coconflict A)).symm

end Complement

/-- **Chromatic Number FO-reduces to Clique Cover**, by complementing the
edges: covering by cliques is coloring the complement. -/
def chromaticNumber_fo_reduction_cliqueCover : ChromaticNumber ≤ᶠᵒ CliqueCover where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ := hasSmallChromaticNumber_iff_cliqueCover_map A

/-- **Clique Cover FO-reduces to Chromatic Number**, by the same
complementation. -/
def cliqueCover_fo_reduction_chromaticNumber : CliqueCover ≤ᶠᵒ ChromaticNumber where
  Tag := Unit
  dim := 1
  toInterpretation := complEdgeInterp
  correct A _ _ := hasSmallCliqueCover_iff_chromaticNumber_map A

/-! ### 3-colorability reduces to Chromatic Number

The threshold must be a marked set of exactly three elements, which no
order-free interpretation can produce; with an order it is `{0, 1, 2}` times
the minimum. The fourth tag exists for a different reason: the target problem
reads its conflict relation off the diagonal, so a self-loop of the input –
which makes it a no-instance – has to be turned into something no 3-coloring
survives, and the `K₄` on the four copies of the looped vertex is exactly
that. -/

/-- The adjacency symbol over the ordered expansion of the graph vocabulary. -/
abbrev oGAdjSym : (Language.graph.sum Language.order).Relations 2 := Sum.inl adj

/-- The interpretation of 3-colorability into Chromatic Number: the graph on
the copy of tag `0`, a `K₄` on the four copies of each self-looped vertex, and
the marked set `{0, 1, 2} × {minimum}` carrying the threshold `3`. -/
noncomputable def chromInterp :
    FOInterpretation (Language.graph.sum Language.order) Language.markedGraph (Fin 4) 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t =>
        if t 0 = t 1 then
          (if t 0 = 0 then
            Relations.formula₂ oGAdjSym (Term.var (0, 0)) (Term.var (1, 0)) else ⊥)
        else
          Term.equal (Term.var (0, 0)) (Term.var (1, 0)) ⊓
            Relations.formula₂ oGAdjSym (Term.var (0, 0)) (Term.var (0, 0))
    | _, .marked => fun t => if t 0 = 3 then ⊥ else minF (0, 0)

section ChromCharacterizations

variable {A : Type} [Language.graph.Structure A] [LinearOrder A]

/-- The copy of a vertex carried by a tag. -/
def cnPt (i : Fin 4) (v : A) : chromInterp.Map A := (i, fun _ => v)

omit [Language.graph.Structure A] [LinearOrder A] in
theorem cnPt_eta (i : Fin 4) (w : Fin 1 → A) :
    ((i, w) : chromInterp.Map A) = cnPt i (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg w (Subsingleton.elim j 0)⟩

omit [Language.graph.Structure A] [LinearOrder A] in
theorem cnPt_injective (i : Fin 4) : Function.Injective (cnPt i (A := A)) :=
  fun _ _ h => congrArg (fun p : Fin 4 × (Fin 1 → A) => p.2 0) h

@[simp]
theorem chrom_adj_zero (v w : A) :
    MGAdj (cnPt 0 v) (cnPt 0 w) ↔ RelMap adj ![v, w] := by
  rw [MGAdj, FOInterpretation.relMap_map]
  simp [chromInterp, cnPt, Formula.realize_rel₂]

@[simp]
theorem chrom_adj_same (i : Fin 4) (hi : i ≠ 0) (v w : A) :
    ¬MGAdj (cnPt i v) (cnPt i w) := by
  rw [MGAdj, FOInterpretation.relMap_map]
  simp [chromInterp, cnPt, hi]

@[simp]
theorem chrom_adj_diff {i j : Fin 4} (hij : i ≠ j) (v w : A) :
    MGAdj (cnPt i v) (cnPt j w) ↔ v = w ∧ RelMap adj ![v, v] := by
  rw [MGAdj, FOInterpretation.relMap_map]
  simp [chromInterp, cnPt, hij, Formula.realize_rel₂]

@[simp]
theorem chrom_marked (i : Fin 4) (v : A) :
    MGMarked (cnPt i v) ↔ i ≠ 3 ∧ ∀ a : A, v ≤ a := by
  rw [MGMarked, FOInterpretation.relMap_map]
  rcases Classical.em (i = 3) with hi | hi
  · simp [chromInterp, cnPt, hi]
  · simp [chromInterp, cnPt, hi, realize_minF]

end ChromCharacterizations

section ChromCorrectness

variable (A : Type) [Language.graph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The marked set of the interpreted structure has exactly three elements:
the first three copies of the minimum. -/
theorem chrom_ncard_marked : {p : chromInterp.Map A | MGMarked p}.ncard = 3 := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  have hinj : Function.Injective fun i : Fin 3 => cnPt (A := A) i.castSucc m := by
    intro i j h
    exact Fin.castSucc_injective 3 (congrArg (fun p : Fin 4 × (Fin 1 → A) => p.1) h)
  have hset : {p : chromInterp.Map A | MGMarked p} =
      (fun i : Fin 3 => cnPt (A := A) i.castSucc m) '' Set.univ := by
    ext p
    rcases p with ⟨i, w⟩
    rw [cnPt_eta i w]
    constructor
    · intro hp
      obtain ⟨hi3, hmin⟩ := (chrom_marked i (w 0)).mp hp
      have hw : w 0 = m := le_antisymm (hmin m) (hm (w 0))
      refine ⟨⟨i.val, ?_⟩, Set.mem_univ _, ?_⟩
      · rcases Nat.lt_or_ge i.val 3 with h | h
        · exact h
        · exact absurd (Fin.ext (le_antisymm (Nat.lt_succ_iff.mp i.isLt) h)) hi3
      · rw [hw]
        rfl
    · rintro ⟨j, -, hj⟩
      rw [← hj]
      refine (chrom_marked _ m).mpr ⟨fun h => ?_, hm⟩
      have hval : (j.castSucc : ℕ) = ((3 : Fin 4) : ℕ) := congrArg Fin.val h
      have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
      have hj3 : (j : ℕ) < 3 := j.isLt
      simp only [Fin.val_castSucc] at hval
      omega
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- Correctness of the interpretation: the graph is 3-colorable iff the
interpreted marked graph has chromatic number at most the size of its marked
set, which is three. -/
theorem threeColorable_iff_chromaticNumber_map :
    ThreeColorable A ↔ HasSmallChromaticNumber (chromInterp.Map A) := by
  have hfin : Finite (chromInterp.Map A) := chromInterp.map_finite A
  rw [HasSmallChromaticNumber, chrom_ncard_marked A]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨hfin, fun p => c (p.2 0), fun p q hpq hcol => ?_⟩
    rcases p with ⟨i, w⟩
    rcases q with ⟨j, w'⟩
    rw [cnPt_eta i w, cnPt_eta j w'] at hpq
    obtain ⟨hne, hadj⟩ := hpq
    rcases Classical.em (i = j) with rfl | hij
    · rcases Classical.em (i = 0) with rfl | hi
      · exact hc (w 0) (w' 0) ((chrom_adj_zero (w 0) (w' 0)).mp hadj) hcol
      · exact chrom_adj_same i hi (w 0) (w' 0) hadj
    · obtain ⟨-, hloop⟩ := (chrom_adj_diff hij (w 0) (w' 0)).mp hadj
      exact hc (w 0) (w 0) hloop rfl
  · rintro ⟨-, c, hc⟩
    refine ⟨fun v => c (cnPt 0 v), fun x y hadj hcol => ?_⟩
    rcases Classical.em (x = y) with rfl | hxy
    · -- a self-loop: the four copies of `x` form a `K₄`, which needs four colors
      obtain ⟨i, j, hij, hcij⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin 4 => c (cnPt i x)) (by simp)
      exact hc (cnPt i x) (cnPt j x)
        ⟨fun h => hij (congrArg (fun p : Fin 4 × (Fin 1 → A) => p.1) h),
          (chrom_adj_diff hij x x).mpr ⟨rfl, hadj⟩⟩ hcij
    · exact hc (cnPt 0 x) (cnPt 0 y)
        ⟨fun h => hxy (cnPt_injective 0 h), (chrom_adj_zero x y).mpr hadj⟩ hcol

end ChromCorrectness

/-- **3-colorability ordered-FO-reduces to Chromatic Number**: keep the graph,
mark three copies of the minimum to carry the threshold, and turn each
self-looped vertex into a `K₄`. -/
noncomputable def threeCol_ordered_fo_reduction_chromaticNumber :
    ThreeCol ≤ᶠᵒ[≤] ChromaticNumber where
  Tag := Fin 4
  dim := 1
  toInterpretation := chromInterp
  correct A _ _ _ _ := threeColorable_iff_chromaticNumber_map A

end DescriptiveComplexity
