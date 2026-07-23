/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeColorability
import DescriptiveComplexity.SecondOrder

/-!
# `k`-colorability is NP-complete for every `k ≥ 3`

`DescriptiveComplexity.KColorable k` generalizes
`DescriptiveComplexity.ThreeColorable` to `k` colors, and
`DescriptiveComplexity.KCol k` is the bundled decision problem on
`FirstOrder.Language.graph`-structures; `DescriptiveComplexity.kCol_three` identifies
`KCol 3` with `DescriptiveComplexity.ThreeCol`.

The two halves of NP-completeness for `k = 3 + m`:

* membership (`DescriptiveComplexity.kCol_sigmaSODefinable`) guesses the `k` color
  classes as `k` unary relation variables, the first-order kernel checking
  that they cover the vertices and that no edge stays inside one class;
* hardness (`DescriptiveComplexity.threeCol_fo_reduction_kCol`) is the textbook
  padding reduction from 3-colorability: add `m` universal vertices, pairwise
  adjacent, so that they eat exactly `m` of the `k` colors and leave 3 for the
  original graph.

The padding is *tagged* rather than literal: an interpretation cannot add a
constant number of elements to the universe, so the `m` new vertices become
`m` new tags, each contributing a full copy of the universe
(`DescriptiveComplexity.padColorInterp`, of dimension 1 and tag type
`Option (Fin m)`). Each copy is made an *independent* set, adjacent to
everything outside itself, i.e. the new vertices are blown up into
independent classes; this changes nothing, because a proper coloring must
give the `m` classes pairwise disjoint sets of colors, all disjoint from the
colors of the original part, so the original part still sees at most `k - m =
3` colors. Recovering a 3-coloring from a `k`-coloring is exactly this
counting argument (`DescriptiveComplexity.threeColorable_of_kColorable_map`), and it is
where the reduction uses that the input structure is nonempty: an empty class
would eat no color.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### The problem -/

section Defs

variable (k : ℕ) (V : Type) [Language.graph.Structure V]

/-- A `Language.graph`-structure is `k`-colorable if the vertices can be
colored with `k` colors so that adjacent vertices get distinct colors. -/
def KColorable : Prop :=
  ∃ c : V → Fin k, ∀ x y : V, RelMap adj ![x, y] → c x ≠ c y

end Defs

private theorem kColorable_of_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) (h : KColorable k A) :
    KColorable k B := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b => c (e.symm b), fun x y hxy =>
    hc (e.symm x) (e.symm y) ((relMap_equiv₂ e.symm adj x y).mp hxy)⟩

/-- `k`-colorability is isomorphism-invariant. -/
theorem kColorable_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) :
    KColorable k A ↔ KColorable k B :=
  ⟨kColorable_of_iso e, kColorable_of_iso e.symm⟩

/-- `k`-colorability, as a problem on `Language.graph`-structures. -/
def KCol (k : ℕ) : DecisionProblem Language.graph where
  Holds := fun V inst => @KColorable k V inst
  iso_invariant := fun e => kColorable_iso e

/-- At `k = 3`, `k`-colorability *is* 3-colorability. -/
theorem kCol_three : KCol 3 = ThreeCol :=
  DecisionProblem.ext fun _ _ => Iff.rfl

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

/-! ### Membership: the color classes as guessed relations -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of `k`-colorability:
one unary relation variable per color. -/
def colorGuessBlock (k : ℕ) : SOBlock where
  ι := Fin k
  arity := fun _ => 1

/-- The symbol of the `i`-th color class. -/
def cgColorSym {k : ℕ} (i : Fin k) : (colorGuessBlock k).lang.Relations 1 := ⟨i, rfl⟩

/-- The vocabulary of the kernel: graphs together with the guessed color
classes. -/
abbrev kColSOLang (k : ℕ) : Language := Language.graph.sum (colorGuessBlock k).lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev kcAdjSym (k : ℕ) : (kColSOLang k).Relations 2 := Sum.inl adj

/-- The symbol of the `i`-th color class in the kernel's vocabulary. -/
abbrev kcColorSym {k : ℕ} (i : Fin k) : (kColSOLang k).Relations 1 := Sum.inr (cgColorSym i)

/-- The first-order kernel of the `Σ₁` definition of `k`-colorability: every
vertex belongs to some color class, and no edge has both endpoints in the
same class. -/
noncomputable def kColKernel (k : ℕ) : (kColSOLang k).Sentence :=
  (Formula.iSup fun i : Fin k =>
    Relations.formula₁ (kcColorSym i) (Term.var (Sum.inr 0))).iAlls (Fin 1) ⊓
  ((Relations.formula₂ (kcAdjSym k) (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    (Formula.iInf fun i : Fin k =>
      ∼(Relations.formula₁ (kcColorSym i) (Term.var (Sum.inr 0)) ⊓
        Relations.formula₁ (kcColorSym i) (Term.var (Sum.inr 1))))).iAlls (Fin 2)

/-- Realization of the kernel under an assignment of the color classes. -/
private theorem realize_kColKernel {k : ℕ} {V : Type} [Language.graph.Structure V]
    (ρ : (colorGuessBlock k).Assignment V) :
    (@Sentence.Realize (kColSOLang k) V
        (@sumStructure _ _ V _ ((colorGuessBlock k).structure ρ)) (kColKernel k)) ↔
      (∀ x : V, ∃ i : Fin k, ρ i ![x]) ∧
        ∀ x y : V, RelMap adj ![x, y] → ∀ i : Fin k, ¬(ρ i ![x] ∧ ρ i ![y]) := by
  letI := (colorGuessBlock k).structure ρ
  have hsub : ∀ (i : Fin k) (w : Fin 1 → V),
      RelMap (L := kColSOLang k) (M := V) (kcColorSym i) w ↔ ρ i w :=
    fun _ _ => Iff.rfl
  rw [kColKernel]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iSup, Formula.realize_iInf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x => ?_, fun h i => ?_⟩ ⟨fun h x y hxy i => ?_, fun h i hi j => ?_⟩
  · obtain ⟨i, hi⟩ := h fun _ => x
    exact ⟨i, hi⟩
  · obtain ⟨j, hj⟩ := h (i 0)
    exact ⟨j, hj⟩
  · exact h ![x, y] (by simpa using hxy) i
  · exact h (i 0) (i 1) (by simpa using hi) j

/-- **`k`-colorability is `Σ₁`-definable**: existentially guess the `k` color
classes, then check first-order that they cover the vertices and that no edge
stays inside a class. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of `k`-colorability. -/
theorem kCol_sigmaSODefinable (k : ℕ) : SigmaSODefinable 1 (KCol k) := by
  refine ⟨[colorGuessBlock k], rfl, kColKernel k, ?_⟩
  intro V _ _ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i (w : Fin 1 → V) => c (w 0) = i, (realize_kColKernel _).mpr
      ⟨fun x => ⟨c x, rfl⟩, fun x y hxy i hi => ?_⟩⟩
    exact hc x y hxy (hi.1.trans hi.2.symm)
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hcover, hproper⟩ := (realize_kColKernel ρ).mp hρ
    choose c hcolor using hcover
    exact ⟨c, fun x y hxy hcxy =>
      hproper x y hxy (c x) ⟨hcolor x, hcxy ▸ hcolor y⟩⟩

end SigmaOne

/-! ### NP-completeness -/

/-- `k`-colorability is in NP: it is `Σ₁`-definable. -/
theorem kCol_mem_NP (k : ℕ) : KCol k ∈ NP :=
  kCol_sigmaSODefinable k

/-- For `k ≥ 3`, `k`-colorability is NP-hard: 3-colorability, which is
NP-hard, reduces to it by padding. -/
theorem kCol_NP_hard {k : ℕ} (hk : 3 ≤ k) : NP.Hard (KCol k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := ⟨k - 3, by omega⟩
  exact NP.hard_of_foReduction (threeCol_fo_reduction_kCol m) threeCol_NP_hard

/-- **`k`-colorability is NP-complete for every `k ≥ 3`.** -/
theorem kCol_NP_complete {k : ℕ} (hk : 3 ≤ k) : NP.Complete (KCol k) :=
  ⟨kCol_mem_NP k, kCol_NP_hard hk⟩

end DescriptiveComplexity
