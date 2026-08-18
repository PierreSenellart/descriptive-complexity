/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Forall2
import DescriptiveComplexity.Numbers.BinRel

/-!
# Sorted enumerations, and matchings between them

The list layer under `DescriptiveComplexity.PCP ∈ RE`. A word of a Post
instance is a *partial map from a finite linear order to letters*
(`DescriptiveComplexity.Pcp.IsWordU`), so everything the semantics reads is
mediated by the strictly increasing list enumerating the positions used. This
file is that mediation, stated for arbitrary relations and lists:

* `DescriptiveComplexity.Pcp.IsEnum` – being the strictly increasing
  enumeration of a predicate, and `DescriptiveComplexity.Pcp.exists_isEnum`,
  which produces one over a finite type carrying a linear order *relation*
  (`DescriptiveComplexity.IsLinOrd`), by sorting;
* the two ways a parse of a concatenation is built out of the parses of its
  blocks: `DescriptiveComplexity.Pcp.forall₂_flatMap` for the letters and
  `List.pairwise_flatMap` for the order;
* `DescriptiveComplexity.Pcp.forall₂_of_matching`, **the** lemma of the file: a
  relation between the members of two strictly sorted lists that is total on
  both sides and reflects the order is the pairing of their entries index by
  index. This is what makes a *matching between the two parses* – a relation
  variable, hence first-order-checkable – as good as the equality of the two
  concatenations, which is not.

The converse pairing, `DescriptiveComplexity.Pcp.IdxMatch`, is the matching two
lists of the same length carry for free; it is the certificate a yes-instance
hands back.
-/

namespace DescriptiveComplexity

namespace Pcp

open List

/-! ### Strictly increasing enumerations -/

section IsEnum

variable {α : Type}

/-- **`ps` enumerates `S` in increasing order**: it is strictly sorted for `Lt`,
and its members are exactly the elements satisfying `S`. Such a list is unique
when it exists, but nothing below needs the uniqueness. -/
def IsEnum (Lt : α → α → Prop) (S : α → Prop) (ps : List α) : Prop :=
  ps.Pairwise Lt ∧ ∀ p, p ∈ ps ↔ S p

/-- Over a finite type ordered by a linear order *relation*, every predicate
has a strictly increasing enumeration: sort the elements satisfying it. -/
theorem exists_isEnum [Finite α] {Le : α → α → Prop} (h : IsLinOrd Le) (S : α → Prop) :
    ∃ ps : List α, IsEnum (fun a b => Le a b ∧ a ≠ b) S ps := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : IsTrans α Le := ⟨h.2.1⟩
  have : Std.Antisymm Le := ⟨h.2.2.1⟩
  have : Std.Total Le := ⟨h.2.2.2⟩
  refine ⟨(Finset.univ.filter S).sort Le, (Finset.pairwise_sort _ Le).and ?_, fun p => ?_⟩
  · exact Finset.sort_nodup _ Le
  · rw [Finset.mem_sort]
    simp

end IsEnum

/-! ### Indices of a strictly sorted list

A strictly sorted list has no repetitions, so its order *is* the order of its
indices: that is the only property of the two parses the matching lemma below
uses. -/

section Sorted

variable {α : Type} {Lt : α → α → Prop}

/-- An asymmetric relation is irreflexive. -/
theorem irrefl_of_asymm (has : ∀ a b, Lt a b → Lt b a → False) (a : α) : ¬Lt a a :=
  fun h => has a a h h

/-- In a strictly sorted list, one entry precedes another exactly when its
index is smaller. -/
theorem lt_getElem_iff (has : ∀ a b, Lt a b → Lt b a → False) {l : List α}
    (hl : l.Pairwise Lt) {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
    Lt l[i] l[j] ↔ i < j := by
  refine ⟨fun h => ?_, fun h => pairwise_iff_getElem.mp hl i j hi hj h⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hij
  · subst hij
    exact absurd h (irrefl_of_asymm has _)
  · exact absurd h fun h' => has _ _ h' (pairwise_iff_getElem.mp hl j i hj hi hij)

end Sorted

/-! ### Lists built block by block -/

section Blocks

variable {γ α β : Type} {R : α → β → Prop} {f : γ → List α} {g : γ → List β}

/-- Two `flatMap`s over the same list are related entry by entry as soon as
their blocks are: the parse of a concatenation is the concatenation of the
parses. -/
theorem forall₂_flatMap :
    ∀ {l : List γ}, (∀ c ∈ l, List.Forall₂ R (f c) (g c)) →
      List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => List.Forall₂.nil
  | c :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h c (mem_cons_self ..))
      (forall₂_flatMap fun c' hc' => h c' (mem_cons_of_mem _ hc'))

/-- A list of witnesses for a list of existentials. -/
theorem exists_forall₂ {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ w : List β, List.Forall₂ R l w
  | [], _ => ⟨[], List.Forall₂.nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (mem_cons_self ..)
    obtain ⟨w, hw⟩ := exists_forall₂ fun a' ha' => h a' (mem_cons_of_mem _ ha')
    exact ⟨b :: w, List.Forall₂.cons hb hw⟩

/-- Two lists read off entry by entry along a matching agree, as soon as the
matched entries carry the same letter. -/
theorem eq_of_forall₂ {M : α → β → Prop} {δ : Type} {RU : α → δ → Prop} {RV : β → δ → Prop}
    (hcomp : ∀ x y ℓ ℓ', M x y → RU x ℓ → RV y ℓ' → ℓ = ℓ') {L₁ : List α} {L₂ : List β}
    (hM : List.Forall₂ M L₁ L₂) :
    ∀ {U V : List δ}, List.Forall₂ RU L₁ U → List.Forall₂ RV L₂ V → U = V := by
  induction hM with
  | nil =>
    intro U V hU hV
    cases hU
    cases hV
    rfl
  | cons hxy _ ih =>
    intro U V hU hV
    cases hU with
    | cons hu hU' =>
      cases hV with
      | cons hv hV' => rw [hcomp _ _ _ _ hxy hu hv, ih hU' hV']

end Blocks

/-! ### The lexicographic order on blocks and positions -/

section Lex

variable {D α : Type}

/-- The lexicographic order on pairs (block, position inside it), for two
strict orders. -/
def LexOf (R : D → D → Prop) (S : α → α → Prop) : D × α → D × α → Prop :=
  fun x y => R x.1 y.1 ∨ (x.1 = y.1 ∧ S x.2 y.2)

/-- The strict part of a linear order relation is asymmetric. -/
theorem asymm_strict {Le : D → D → Prop} (h : IsLinOrd Le) (a b : D)
    (hab : Le a b ∧ a ≠ b) (hba : Le b a ∧ b ≠ a) : False :=
  hab.2 (h.2.2.1 a b hab.1 hba.1)

/-- The lexicographic order of two asymmetric relations is asymmetric. -/
theorem asymm_lexOf {R : D → D → Prop} {S : α → α → Prop}
    (hR : ∀ a b, R a b → R b a → False) (hS : ∀ a b, S a b → S b a → False) (x y : D × α)
    (hxy : LexOf R S x y) (hyx : LexOf R S y x) : False := by
  rcases hxy with h | ⟨he, h⟩ <;> rcases hyx with h' | ⟨he', h'⟩
  · exact hR _ _ h h'
  · exact hR _ _ h (he' ▸ h)
  · exact hR _ _ h' (he ▸ h')
  · exact hS _ _ h h'

end Lex

/-! ### The index list of a parse

A parse of a concatenation is indexed by the pairs (block, position inside the
block), in lexicographic order: the *common word is never invented*, only the
two ways of cutting it into blocks are. -/

section Parse

variable {D α β : Type} {slots : List D} {ps : D → List α}

/-- **The index list of a parse**: the pairs (block, position used inside it),
block by block. -/
def parseIx (slots : List D) (ps : D → List α) : List (D × α) :=
  slots.flatMap fun s => (ps s).map fun p => (s, p)

@[simp]
theorem mem_parseIx {x : D × α} : x ∈ parseIx slots ps ↔ x.1 ∈ slots ∧ x.2 ∈ ps x.1 := by
  obtain ⟨s, p⟩ := x
  simp only [parseIx, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', p', hp', rfl, rfl⟩
    exact ⟨hs', hp'⟩
  · rintro ⟨hs, hp⟩
    exact ⟨s, hs, p, hp, rfl, rfl⟩

/-- The index list of a parse is sorted lexicographically: the blocks come in
order, and the positions inside a block come in order. -/
theorem pairwise_parseIx {R : D → D → Prop} {S : α → α → Prop} (hs : slots.Pairwise R)
    (hp : ∀ s, (ps s).Pairwise S) : (parseIx slots ps).Pairwise (LexOf R S) := by
  refine List.pairwise_flatMap.mpr ⟨fun s _ => ?_, hs.imp fun {s t} hst x hx y hy => ?_⟩
  · exact List.pairwise_map.mpr ((hp s).imp fun h => Or.inr ⟨rfl, h⟩)
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
    exact Or.inl hst

/-- The letters of a parse, read along its index list, are the letters of the
concatenation. -/
theorem forall₂_parseIx {T : D → α → β → Prop} {ws : D → List β}
    (h : ∀ s ∈ slots, List.Forall₂ (T s) (ps s) (ws s)) :
    List.Forall₂ (fun x ℓ => T x.1 x.2 ℓ) (parseIx slots ps) (slots.flatMap ws) :=
  forall₂_flatMap fun s hs => List.forall₂_map_left_iff.mpr (h s hs)

end Parse

/-! ### Reading a `Forall₂` as a function

The certificate of a yes-instance indexes its slots by `Fin n`, while the
semantics hands the words over as a `List.Forall₂`; this turns the one into
the other, once. -/

section AsFunction

variable {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}

/-- Entries of two lists related by `List.Forall₂` are related index by
index. -/
theorem forall₂_getElem (h : List.Forall₂ R l₁ l₂) {i : ℕ} (h₁ : i < l₁.length)
    (h₂ : i < l₂.length) : R l₁[i] l₂[i] :=
  (forall₂_iff_get.mp h).2 i h₁ h₂

/-- A `List.Forall₂` is a function on the indices of its left list. -/
theorem exists_fun_of_forall₂ (h : List.Forall₂ R l₁ l₂) :
    ∃ g : Fin l₁.length → β,
      (List.finRange l₁.length).map g = l₂ ∧ ∀ i, R (l₁.get i) (g i) := by
  have hlen : l₁.length = l₂.length := h.length_eq
  refine ⟨fun i => l₂[i.1]'(hlen ▸ i.2), ?_, fun i => ?_⟩
  · refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
    simp only [List.getElem_map, List.getElem_finRange]
    rfl
  · exact forall₂_getElem h i.2 (hlen ▸ i.2)

end AsFunction

/-! ### Matchings between two sorted lists -/

section Matching

variable {α β : Type} {Lt₁ : α → α → Prop} {Lt₂ : β → β → Prop}

/-- **A matching between two strictly sorted lists pairs their entries index by
index.** The relation is asked only for what a first-order kernel can check of
a relation variable – that it lands in the two lists, that it is defined
everywhere on both, and that it reflects the two orders – and this is already
enough to make it the unique order isomorphism, hence to identify the two
lists entry by entry. Functionality and injectivity are *not* hypotheses: they
follow from reflecting the order. -/
theorem forall₂_of_matching (has₁ : ∀ a b, Lt₁ a b → Lt₁ b a → False)
    (has₂ : ∀ a b, Lt₂ a b → Lt₂ b a → False) :
    ∀ {L₁ : List α} {L₂ : List β} {M : α → β → Prop}, L₁.Pairwise Lt₁ → L₂.Pairwise Lt₂ →
      (∀ x y, M x y → x ∈ L₁ ∧ y ∈ L₂) → (∀ x ∈ L₁, ∃ y, M x y) → (∀ y ∈ L₂, ∃ x, M x y) →
      (∀ x y x' y', M x y → M x' y' → (Lt₁ x x' ↔ Lt₂ y y')) → List.Forall₂ M L₁ L₂ := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ M _ _ hmem _ hright _
    have : L₂ = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun y hy => ?_
      obtain ⟨x, hx⟩ := hright y hy
      exact absurd (hmem x y hx).1 (List.not_mem_nil)
    exact this ▸ List.Forall₂.nil
  | cons a t ih =>
    intro L₂ M hp₁ hp₂ hmem hleft hright hmono
    obtain ⟨hat, hpt⟩ := List.pairwise_cons.mp hp₁
    -- the head of the left list is matched, so the right list is nonempty
    obtain ⟨y₀, hy₀⟩ := hleft a (mem_cons_self ..)
    obtain ⟨b, t', rfl⟩ : ∃ b t', L₂ = b :: t' := by
      match L₂, (hmem a y₀ hy₀).2 with
      | b :: t', _ => exact ⟨b, t', rfl⟩
    obtain ⟨hbt, hpt'⟩ := List.pairwise_cons.mp hp₂
    -- the two heads are matched to each other
    have hab : M a b := by
      obtain ⟨x₀, hx₀⟩ := hright b (mem_cons_self ..)
      rcases eq_or_ne x₀ a with rfl | hne
      · exact hx₀
      · have hax : Lt₁ a x₀ :=
          hat x₀ ((List.mem_cons.mp (hmem x₀ b hx₀).1).resolve_left fun h => hne h)
        have hyb : Lt₂ y₀ b := (hmono a y₀ x₀ b hy₀ hx₀).mp hax
        rcases List.mem_cons.mp (hmem a y₀ hy₀).2 with rfl | hy
        · exact absurd hyb (irrefl_of_asymm has₂ _)
        · exact absurd hyb fun h => has₂ _ _ h (hbt y₀ hy)
    -- and the tails match each other, by the same relation restricted to them
    refine List.Forall₂.cons hab
      ((ih (M := fun x y => M x y ∧ x ∈ t ∧ y ∈ t') hpt hpt'
        (fun _ _ hx => hx.2) (fun x hx => ?_) (fun y hy => ?_)
        (fun x y x' y' hx hx' => hmono x y x' y' hx.1 hx'.1)).imp fun _ _ h => h.1)
    · obtain ⟨y, hy⟩ := hleft x (mem_cons_of_mem _ hx)
      refine ⟨y, hy, hx, (List.mem_cons.mp (hmem x y hy).2).resolve_left fun hyb => ?_⟩
      exact irrefl_of_asymm has₂ b ((hmono a b x b hab (hyb ▸ hy)).mp (hat x hx))
    · obtain ⟨x, hx⟩ := hright y (mem_cons_of_mem _ hy)
      refine ⟨x, hx, (List.mem_cons.mp (hmem x y hx).1).resolve_left fun hxa => ?_, hy⟩
      exact irrefl_of_asymm has₁ a ((hmono a b a y hab (hxa ▸ hx)).mpr (hbt y hy))

end Matching

/-! ### The matching two lists of the same length carry -/

section IdxMatch

variable {α β : Type}

/-- **The pairing of two lists index by index**, as a relation: the matching a
yes-instance hands back once its two parses are known to be the same word. -/
def IdxMatch (L₁ : List α) (L₂ : List β) (x : α) (y : β) : Prop :=
  ∃ i : ℕ, ∃ h₁ : i < L₁.length, ∃ h₂ : i < L₂.length, L₁[i] = x ∧ L₂[i] = y

variable {L₁ : List α} {L₂ : List β}

/-- The index pairing relates members of the two lists. -/
theorem idxMatch_mem {x : α} {y : β} (h : IdxMatch L₁ L₂ x y) : x ∈ L₁ ∧ y ∈ L₂ := by
  obtain ⟨i, h₁, h₂, rfl, rfl⟩ := h
  exact ⟨List.getElem_mem h₁, List.getElem_mem h₂⟩

/-- The index pairing is defined on every member of the left list. -/
theorem idxMatch_left (hlen : L₁.length = L₂.length) {x : α} (hx : x ∈ L₁) :
    ∃ y, IdxMatch L₁ L₂ x y := by
  obtain ⟨i, h₁, rfl⟩ := List.getElem_of_mem hx
  exact ⟨L₂[i]'(hlen ▸ h₁), i, h₁, hlen ▸ h₁, rfl, rfl⟩

/-- The index pairing is defined on every member of the right list. -/
theorem idxMatch_right (hlen : L₁.length = L₂.length) {y : β} (hy : y ∈ L₂) :
    ∃ x, IdxMatch L₁ L₂ x y := by
  obtain ⟨i, h₂, rfl⟩ := List.getElem_of_mem hy
  exact ⟨L₁[i]'(hlen ▸ h₂), i, hlen ▸ h₂, h₂, rfl, rfl⟩

/-- The index pairing reflects the orders of two strictly sorted lists: both
read as the order of the indices. -/
theorem idxMatch_mono {Lt₁ : α → α → Prop} {Lt₂ : β → β → Prop}
    (has₁ : ∀ a b, Lt₁ a b → Lt₁ b a → False) (has₂ : ∀ a b, Lt₂ a b → Lt₂ b a → False)
    (hp₁ : L₁.Pairwise Lt₁) (hp₂ : L₂.Pairwise Lt₂) {x y x' y' : _}
    (h : IdxMatch L₁ L₂ x y) (h' : IdxMatch L₁ L₂ x' y') : Lt₁ x x' ↔ Lt₂ y y' := by
  obtain ⟨i, hi₁, hi₂, rfl, rfl⟩ := h
  obtain ⟨j, hj₁, hj₂, rfl, rfl⟩ := h'
  rw [lt_getElem_iff has₁ hp₁ hi₁ hj₁, lt_getElem_iff has₂ hp₂ hi₂ hj₂]

end IdxMatch

end Pcp

end DescriptiveComplexity
