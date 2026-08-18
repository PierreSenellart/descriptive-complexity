/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.Numbers.Binary
import DescriptiveComplexity.Problems.Knapsack.Defs

/-!
# The binary encoding of subset-sum instances, and what it decodes to

The catalog's weighted problems – Knapsack and everything reduced from it –
live on `FirstOrder.Language.binWeights` structures, whose numbers are *sets
of bit positions* read by `DescriptiveComplexity.binNum`. A user does not
start there: they start from a list of weights and a target. This file is the
bridge, and it is what the size discipline of `DescriptiveComplexity.Encoding`
is for, since for these problems the representation is part of the statement –
in unary they are solvable in polynomial time.

* `DescriptiveComplexity.binarySubsetSumEncoding` is the honest binary encoding
  of `DescriptiveComplexity.SubsetSumInstance = List ℕ × ℕ`: one element per
  item, one element per bit position, `bit` and `tgt` reading the binary
  digits, place values carried by the order. Both size bounds – `card_le` (no
  padding) and `le_card` (no compression) – are discharged at construction,
  against the declared size `DescriptiveComplexity.ssSize`, the total *bit
  length*. That they have teeth is `DescriptiveComplexity.no_unary_encoding`,
  in `DescriptiveComplexity.Encoding.UnaryBlowup`: no encoding sized this way
  can hold one universe element per unit of weight.
* The `BinarySubsetSum` namespace **decodes** it: the vocabulary's relations on
  an encoded instance (`BinarySubsetSum.item_itemPt` and friends), the order is
  linear (`BinarySubsetSum.isLinOrd`), the rank of a position is its index
  (`BinarySubsetSum.bitRank_posnPt`), and therefore each item's decoded weight
  is its list entry and the decoded target is the target
  (`BinarySubsetSum.weight_itemPt`, `BinarySubsetSum.target`).
* `DescriptiveComplexity.selection_toIndex` and
  `DescriptiveComplexity.selection_ofIndex` turn a *selection of items* on any
  structure into a `Finset` of indices and back, along any injective indexing
  of the items, preserving both the total weight and whether the selection is
  empty. They are the reusable half: any problem on `binWeights` that
  quantifies over selections of items – Knapsack here, and variants that
  constrain the selection further – gets both directions from these two.
* `DescriptiveComplexity.binarySubsetSumEncoding_faithful` closes the loop for
  Knapsack: `DescriptiveComplexity.ConcreteSubsetSum`, the textbook predicate
  on a list and a target, is exactly what `DescriptiveComplexity.Knapsack`
  computes on the encoded structure. Read through it,
  `DescriptiveComplexity.knapsack_NP_complete` is a statement about lists of
  binary-written numbers.
* `DescriptiveComplexity.bwDecoding` is the converse direction, the one
  *hardness* needs: a computable decoder from presented structures back to
  lists of weights. It needs no well-formedness condition, there being no junk
  to exclude – a structure whose order is not linear is a definite
  no-instance, and a concrete no-instance decodes it. Hence
  `DescriptiveComplexity.exists_concreteSubsetSum_iff`, for *every* nonempty
  finite structure.

The universe elements are named by `BinarySubsetSum.itemPt` and
`BinarySubsetSum.posnPt` rather than written as `Sum.inl`/`Sum.inr`: the
encoded universe `binarySubsetSumEncoding.Univ i` is a projection out of the
encoder, so it is opaque to `simp`'s type-correctness check, and a raw
constructor application would be typed at the unfolded sum instead. The two
constructors carry the right type by definition, and
`BinarySubsetSum.pt_cases` replaces `cases` on a universe element.
-/

namespace DescriptiveComplexity

open FirstOrder Finset

open Language Structure

/-! ### The instance type, its size, and the encoding -/

/-- A concrete subset-sum instance: a list of weights and a target. -/
abbrev SubsetSumInstance : Type := List ℕ × ℕ

/-- The honest size of a subset-sum instance: the total *bit length* of its
weights and of its target, plus the number of items (so that zero weights
still take room). An encoding sized this way must represent weights in
binary or violate `card_le`. -/
def ssSize : SubsetSumInstance → ℕ := fun i =>
  (i.1.map Nat.size).sum + Nat.size i.2 + i.1.length

/-- The honest **binary** encoding of subset-sum instances – one element per
item, one element per bit position, `bit` and `tgt` reading the binary digits,
place values carried by the order – which passes both size bounds with room to
spare. Its semantics is `binarySubsetSumEncoding_faithful`. -/
def binarySubsetSumEncoding : Encoding Language.binWeights SubsetSumInstance where
  size := ssSize
  Univ := fun i => Fin i.1.length ⊕ Fin (ssSize i + 1)
  deceq := fun _ => inferInstance
  fintype := fun _ => inferInstance
  relBool := fun i {n} R =>
    match n, R with
    | _, .item => fun x => (x 0).isLeft
    | _, .posn => fun x => (x 0).isRight
    | _, .bit => fun x =>
      match x 0, x 1 with
      | Sum.inl j, Sum.inr p => (i.1.get j).testBit p.1
      | _, _ => false
    | _, .tgt => fun x =>
      match x 0 with
      | Sum.inr p => i.2.testBit p.1
      | _ => false
    | _, .le => fun x =>
      match x 0, x 1 with
      | Sum.inl j, Sum.inl j' => decide (j ≤ j')
      | Sum.inl _, Sum.inr _ => true
      | Sum.inr _, Sum.inl _ => false
      | Sum.inr p, Sum.inr p' => decide (p ≤ p')
  card_le := Encoding.linear_bound (c := 2) fun i => by
    have hlen : i.1.length ≤ ssSize i := by
      simp only [ssSize]
      omega
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega
  le_card := Encoding.linear_bound (c := 1) fun i => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega

namespace BinarySubsetSum

variable {i : SubsetSumInstance}

/-! ### The two kinds of universe element -/

/-- The universe element carrying the item at list position `j`. -/
def itemPt (i : SubsetSumInstance) (j : Fin i.1.length) : binarySubsetSumEncoding.Univ i :=
  Sum.inl j

/-- The universe element carrying the bit position `p`. -/
def posnPt (i : SubsetSumInstance) (p : Fin (ssSize i + 1)) : binarySubsetSumEncoding.Univ i :=
  Sum.inr p

/-- The universe of an encoded instance is exactly its items and its bit
positions. This replaces `cases` on a universe element. -/
theorem pt_cases (q : binarySubsetSumEncoding.Univ i) :
    (∃ j, q = itemPt i j) ∨ ∃ p, q = posnPt i p := by
  cases q with
  | inl j => exact Or.inl ⟨j, rfl⟩
  | inr p => exact Or.inr ⟨p, rfl⟩

theorem itemPt_injective : Function.Injective (itemPt i) := fun _ _ h => Sum.inl_injective h

theorem posnPt_injective : Function.Injective (posnPt i) := fun _ _ h => Sum.inr_injective h

@[simp] theorem itemPt_inj {j j' : Fin i.1.length} : itemPt i j = itemPt i j' ↔ j = j' :=
  ⟨fun h => itemPt_injective h, fun h => h ▸ rfl⟩

@[simp] theorem posnPt_inj {p p' : Fin (ssSize i + 1)} : posnPt i p = posnPt i p' ↔ p = p' :=
  ⟨fun h => posnPt_injective h, fun h => h ▸ rfl⟩

@[simp] theorem itemPt_ne_posnPt (j : Fin i.1.length) (p : Fin (ssSize i + 1)) :
    itemPt i j ≠ posnPt i p := fun h => by simp [itemPt, posnPt] at h

@[simp] theorem posnPt_ne_itemPt (p : Fin (ssSize i + 1)) (j : Fin i.1.length) :
    posnPt i p ≠ itemPt i j := fun h => by simp [itemPt, posnPt] at h

/-! ### The vocabulary on an encoded instance

Every relation of `Language.binWeights` is the encoder's computation, read
back on the two kinds of element: the order puts all items before all
positions and orders each kind by index. All of it holds by computation, the
encoder being a plain `def`.
-/

@[simp] theorem item_itemPt (j : Fin i.1.length) : BWItem (itemPt i j) := rfl

@[simp] theorem item_posnPt (p : Fin (ssSize i + 1)) : ¬ BWItem (posnPt i p) :=
  fun h => Bool.noConfusion h

@[simp] theorem posn_itemPt (j : Fin i.1.length) : ¬ BWPosn (itemPt i j) :=
  fun h => Bool.noConfusion h

@[simp] theorem posn_posnPt (p : Fin (ssSize i + 1)) : BWPosn (posnPt i p) := rfl

@[simp] theorem bit_itemPt_posnPt (j : Fin i.1.length) (p : Fin (ssSize i + 1)) :
    BWBit (itemPt i j) (posnPt i p) ↔ (i.1.get j).testBit (p : ℕ) := Iff.rfl

@[simp] theorem bit_itemPt_itemPt (j j' : Fin i.1.length) :
    ¬ BWBit (itemPt i j) (itemPt i j') := fun h => Bool.noConfusion h

@[simp] theorem bit_posnPt (p : Fin (ssSize i + 1)) (q : binarySubsetSumEncoding.Univ i) :
    ¬ BWBit (posnPt i p) q := by
  rcases pt_cases q with ⟨j, rfl⟩ | ⟨p', rfl⟩ <;> exact fun h => Bool.noConfusion h

@[simp] theorem tgt_posnPt (p : Fin (ssSize i + 1)) :
    BWTgt (posnPt i p) ↔ i.2.testBit (p : ℕ) := Iff.rfl

@[simp] theorem tgt_itemPt (j : Fin i.1.length) : ¬ BWTgt (itemPt i j) :=
  fun h => Bool.noConfusion h

@[simp] theorem le_itemPt_itemPt (j j' : Fin i.1.length) :
    BWLe (itemPt i j) (itemPt i j') ↔ j ≤ j' := decide_eq_true_iff

@[simp] theorem le_itemPt_posnPt (j : Fin i.1.length) (p : Fin (ssSize i + 1)) :
    BWLe (itemPt i j) (posnPt i p) := rfl

@[simp] theorem le_posnPt_itemPt (p : Fin (ssSize i + 1)) (j : Fin i.1.length) :
    ¬ BWLe (posnPt i p) (itemPt i j) := fun h => Bool.noConfusion h

@[simp] theorem le_posnPt_posnPt (p p' : Fin (ssSize i + 1)) :
    BWLe (posnPt i p) (posnPt i p') ↔ p ≤ p' := decide_eq_true_iff

/-- The encoded order is linear: all items, in index order, then all
positions, in index order. -/
theorem isLinOrd : IsLinOrd (BWLe (A := binarySubsetSumEncoding.Univ i)) := by
  refine ⟨fun q => ?_, fun q r s hqr hrs => ?_, fun q r hqr hrq => ?_, fun q r => ?_⟩
  · rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩ <;> simp
  · rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩ <;>
      rcases pt_cases r with ⟨j', rfl⟩ | ⟨p', rfl⟩ <;>
      rcases pt_cases s with ⟨j'', rfl⟩ | ⟨p'', rfl⟩ <;>
      simp_all only [le_itemPt_itemPt, le_itemPt_posnPt, le_posnPt_itemPt,
        le_posnPt_posnPt] <;>
      exact le_trans hqr hrs
  · rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩ <;>
      rcases pt_cases r with ⟨j', rfl⟩ | ⟨p', rfl⟩ <;>
      simp_all only [le_itemPt_itemPt, le_itemPt_posnPt, le_posnPt_itemPt,
        le_posnPt_posnPt, itemPt_inj, posnPt_inj] <;>
      exact le_antisymm hqr hrq
  · rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩ <;>
      rcases pt_cases r with ⟨j', rfl⟩ | ⟨p', rfl⟩ <;>
      simp only [le_itemPt_itemPt, le_itemPt_posnPt, le_posnPt_itemPt,
        le_posnPt_posnPt, or_true, true_or] <;>
      exact le_total _ _

/-! ### Decoding the numbers

The rank of a position is its index, so `binNum` is the plain sum of place
values, and the encoder's `Nat.testBit` digits are read back as the number
they came from.
-/

/-- The rank of a bit position is its index: the positions strictly below it
are exactly those with a smaller index. -/
theorem bitRank_posnPt (p : Fin (ssSize i + 1)) :
    bitRank (BWLe (A := binarySubsetSumEncoding.Univ i)) BWPosn (posnPt i p) = (p : ℕ) := by
  classical
  have hset :
      {q : binarySubsetSumEncoding.Univ i | BWPosn q ∧ BWLe q (posnPt i p) ∧ q ≠ posnPt i p}
        = posnPt i '' ↑(Finset.Iio p) := by
    ext q
    rcases pt_cases q with ⟨j, rfl⟩ | ⟨p', rfl⟩
    · simp
    · simp only [Set.mem_setOf_eq, posn_posnPt, le_posnPt_posnPt, true_and, ne_eq,
        posnPt_inj, Set.mem_image, Finset.coe_Iio, Set.mem_Iio]
      constructor
      · rintro ⟨hle, hne⟩
        exact ⟨p', lt_of_le_of_ne hle hne, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨le_of_lt hx, ne_of_lt hx⟩
  unfold bitRank
  rw [hset, Set.ncard_image_of_injective _ posnPt_injective, Set.ncard_coe_finset,
    Fin.card_Iio]

open Classical in
/-- On an encoded instance, `binNum` is the plain sum of place values over the
bit positions. -/
theorem binNum_eq_sum (b : binarySubsetSumEncoding.Univ i → Prop) :
    binNum (BWLe (A := binarySubsetSumEncoding.Univ i)) BWPosn b
      = ∑ p : Fin (ssSize i + 1), if b (posnPt i p) then 2 ^ (p : ℕ) else 0 := by
  classical
  have hset : {q : binarySubsetSumEncoding.Univ i | BWPosn q ∧ b q}
      = posnPt i '' ↑(Finset.univ.filter fun p : Fin (ssSize i + 1) => b (posnPt i p)) := by
    ext q
    rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩
    · simp
    · simp
  unfold binNum
  rw [hset, finsum_mem_image posnPt_injective.injOn,
    finsum_mem_congr rfl fun p _ => by rw [bitRank_posnPt p], finsum_mem_coe_finset,
    Finset.sum_filter]

/-- **The decoding.** A set of bit positions carrying the binary digits of a
number that fits in the position block decodes to that number. -/
theorem binNum_eq (w : ℕ) (hw : w < 2 ^ (ssSize i + 1))
    (b : binarySubsetSumEncoding.Univ i → Prop)
    (hb : ∀ p : Fin (ssSize i + 1), b (posnPt i p) ↔ w.testBit (p : ℕ)) :
    binNum (BWLe (A := binarySubsetSumEncoding.Univ i)) BWPosn b = w := by
  classical
  have hval : binValue (Fin (ssSize i + 1)) (binEncode (Fin (ssSize i + 1)) w) = w :=
    binValue_binEncode (by simpa using hw)
  rw [binNum_eq_sum, ← hval, binValue]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : w.testBit (p : ℕ) <;> simp [binEncode, hb p, h]

/-! ### The weights and the target -/

/-- Every weight fits in the position block: its bit length is part of the
declared size. -/
theorem get_lt (j : Fin i.1.length) : i.1.get j < 2 ^ (ssSize i + 1) := by
  refine Nat.size_le.mp (le_trans ?_ (Nat.le_succ _))
  have hmem : Nat.size (i.1.get j) ∈ i.1.map Nat.size :=
    List.mem_map_of_mem (List.get_mem _ _)
  have hle := List.single_le_sum (l := i.1.map Nat.size) (fun x _ => Nat.zero_le x) _ hmem
  simp only [ssSize]
  omega

/-- The target fits in the position block, for the same reason. -/
theorem target_lt : i.2 < 2 ^ (ssSize i + 1) := by
  refine Nat.size_le.mp (le_trans ?_ (Nat.le_succ _))
  simp only [ssSize]
  omega

/-- An item's decoded weight is its list entry. -/
@[simp] theorem weight_itemPt (j : Fin i.1.length) :
    BWWeight (itemPt i j) = i.1.get j :=
  binNum_eq _ (get_lt j) _ fun p => by simp

/-- A bit position is not an item, and carries no weight. -/
@[simp] theorem weight_posnPt (p : Fin (ssSize i + 1)) :
    BWWeight (posnPt i p) = 0 := by
  unfold BWWeight
  rw [binNum_congr (b' := fun _ => False) fun q => ⟨fun h => absurd h (bit_posnPt p q), False.elim⟩,
    binNum_bot]

/-- The decoded target is the target. -/
@[simp] theorem target : BWTarget (binarySubsetSumEncoding.Univ i) = i.2 :=
  binNum_eq _ target_lt _ fun p => by simp

/-- The items of an encoded instance are exactly the elements it indexes. -/
theorem item_iff_range (q : binarySubsetSumEncoding.Univ i) :
    BWItem q ↔ ∃ j, itemPt i j = q := by
  rcases pt_cases q with ⟨j, rfl⟩ | ⟨p, rfl⟩
  · exact iff_of_true (item_itemPt j) ⟨j, rfl⟩
  · exact iff_of_false (item_posnPt p) (by rintro ⟨j, hj⟩; exact absurd hj (itemPt_ne_posnPt j p))

end BinarySubsetSum

/-! ### Selections of items, both ways

A selection of items is a set of indices, along *any* injective indexing of the
items – the encoding's own, or a decoder's listing of the items of a presented
structure. Both directions preserve the total weight and whether the selection
is empty, which is everything a problem on `binWeights` asks of a selection.
-/

section Selections

variable {A : Type} [Language.binWeights.Structure A] {n : ℕ} (f : Fin n → A)

/-- Every selection of items is a `Finset` of indices, with the same total
weight and the same emptiness. -/
theorem selection_toIndex (hf : Function.Injective f)
    (hrange : ∀ a, BWItem a ↔ ∃ j, f j = a) (S : A → Prop) (hS : ∀ a, S a → BWItem a) :
    ∃ J : Finset (Fin n),
      (∑ᶠ a ∈ {a | S a}, BWWeight a) = ∑ j ∈ J, BWWeight (f j) ∧ ((∃ a, S a) ↔ J.Nonempty) := by
  classical
  refine ⟨Finset.univ.filter fun j => S (f j), ?_, ?_⟩
  · have hset : {a : A | S a} = f '' ↑(Finset.univ.filter fun j => S (f j)) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha
        obtain ⟨j, rfl⟩ := (hrange a).mp (hS a ha)
        exact ⟨j, ha, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact hj
    rw [hset, finsum_mem_image hf.injOn, finsum_mem_coe_finset]
  · simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨j, rfl⟩ := (hrange a).mp (hS a ha)
      exact ⟨j, ha⟩
    · rintro ⟨j, hj⟩
      exact ⟨f j, hj⟩

/-- Conversely, every `Finset` of indices is a selection of items, with the
same total weight and the same emptiness. -/
theorem selection_ofIndex (hf : Function.Injective f) (hitem : ∀ j, BWItem (f j))
    (J : Finset (Fin n)) :
    ∃ S : A → Prop, (∀ a, S a → BWItem a) ∧
      (∑ᶠ a ∈ {a | S a}, BWWeight a) = ∑ j ∈ J, BWWeight (f j) ∧ ((∃ a, S a) ↔ J.Nonempty) := by
  classical
  refine ⟨fun a => ∃ j ∈ J, a = f j, ?_, ?_, ?_⟩
  · rintro a ⟨j, -, rfl⟩
    exact hitem j
  · have hset : {a : A | ∃ j ∈ J, a = f j} = f '' ↑J := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
      exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩⟩
    rw [hset, finsum_mem_image hf.injOn, finsum_mem_coe_finset]
  · constructor
    · rintro ⟨-, j, hj, -⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨f j, j, hj, rfl⟩

/-- **Knapsack, read along an indexing of the items**: the abstract problem is
the concrete subset-sum question about the indexed weights. -/
theorem hasSubsetSum_iff_index [Finite A] (hf : Function.Injective f)
    (hrange : ∀ a, BWItem a ↔ ∃ j, f j = a) (hlin : IsLinOrd (BWLe (A := A))) :
    HasSubsetSum A ↔ ∃ J : Finset (Fin n), ∑ j ∈ J, BWWeight (f j) = BWTarget A := by
  constructor
  · rintro ⟨-, -, S, hSi, hsum⟩
    obtain ⟨J, hJ, -⟩ := selection_toIndex f hf hrange S hSi
    exact ⟨J, by rw [← hJ, hsum]⟩
  · rintro ⟨J, hJ⟩
    obtain ⟨S, hSi, hsum, -⟩ := selection_ofIndex f hf (fun j => (hrange _).mpr ⟨j, rfl⟩) J
    exact ⟨inferInstance, hlin, S, hSi, by rw [hsum, hJ]⟩

end Selections

/-! ### Faithfulness for Knapsack -/

/-- The textbook subset-sum predicate on a concrete instance: some set of list
positions has weights summing to the target. Nothing here mentions model
theory; it is the problem as it is stated before any encoding. -/
def ConcreteSubsetSum (i : SubsetSumInstance) : Prop :=
  ∃ J : Finset (Fin i.1.length), ∑ j ∈ J, i.1.get j = i.2

/-- **The binary encoding is faithful**: on every encoded instance, `Knapsack`
computes the textbook predicate `ConcreteSubsetSum`. With the size bounds
discharged at construction, this is what makes `knapsack_NP_complete` a
statement about lists of binary-written numbers. -/
theorem binarySubsetSumEncoding_faithful :
    binarySubsetSumEncoding.Faithful ConcreteSubsetSum Knapsack := fun i =>
  Iff.symm <| (hasSubsetSum_iff_index (BinarySubsetSum.itemPt i)
    BinarySubsetSum.itemPt_injective BinarySubsetSum.item_iff_range
    BinarySubsetSum.isLinOrd).trans <| by
      simp only [BinarySubsetSum.weight_itemPt, BinarySubsetSum.target]
      exact Iff.rfl

/-! ### The decoding direction

Faithfulness reads *membership* back to concrete instances; reading *hardness*
back needs the converse – that the abstract problem is not hard only on junk
structures no encoding produces. Here there is no junk to exclude: every
presented `binWeights` structure decodes. A structure whose order is not
linear is a definite no-instance (`HasSubsetSum` carries `IsLinOrd` as a
conjunct), and any concrete no-instance decodes it; on the rest, the decoder
lists the items and reads their weights and the target off the presentation.
So the well-formedness condition is trivial, and
`exists_concreteSubsetSum_iff` holds for *every* nonempty finite structure.
-/

namespace BinarySubsetSum

section Decoder

variable (S : FinPresentation Language.binWeights)

/-! The vocabulary of a presentation is decidable, being a table of `Bool`s;
these instances are what lets a decoder build `Finset`s and sum over them. -/

instance : DecidablePred (BWItem (A := Fin S.card)) :=
  fun a => inferInstanceAs (Decidable (S.relBool bwItem ![a] = true))

instance : DecidablePred (BWPosn (A := Fin S.card)) :=
  fun a => inferInstanceAs (Decidable (S.relBool bwPosn ![a] = true))

instance : DecidablePred (BWTgt (A := Fin S.card)) :=
  fun a => inferInstanceAs (Decidable (S.relBool bwTgt ![a] = true))

instance : DecidableRel (BWBit (A := Fin S.card)) :=
  fun a b => inferInstanceAs (Decidable (S.relBool bwBit ![a, b] = true))

instance : DecidableRel (BWLe (A := Fin S.card)) :=
  fun a b => inferInstanceAs (Decidable (S.relBool bwLe ![a, b] = true))

/-- Is the presented order linear? -/
def isLinOrdB : Bool :=
  decide (∀ a b c : Fin S.card, BWLe a a ∧ (BWLe a b → BWLe b c → BWLe a c) ∧
    (BWLe a b → BWLe b a → a = b) ∧ (BWLe a b ∨ BWLe b a))

theorem isLinOrdB_iff : isLinOrdB S = true ↔ IsLinOrd (BWLe (A := Fin S.card)) := by
  rw [isLinOrdB, decide_eq_true_iff]
  constructor
  · intro h
    exact ⟨fun a => (h a a a).1, fun a b c => (h a b c).2.1, fun a b => (h a b b).2.2.1,
      fun a b => (h a b b).2.2.2⟩
  · rintro ⟨hr, ht, ha, hto⟩ a b c
    exact ⟨hr a, ht a b c, ha a b, hto a b⟩

/-- The items of a presentation, listed without duplicates. -/
def items : List (Fin S.card) := (List.finRange S.card).filter fun a => decide (BWItem a)

/-- The rank of a bit position, as a computation. -/
def rankB (p : Fin S.card) : ℕ := (Finset.univ.filter fun q => BWPosn q ∧ BWLe q p ∧ q ≠ p).card

/-- A binary number of the presentation, as a computation: the noncomputable
`binNum` is a `finsum`, and this is the `Finset` sum it equals. -/
def numB (b : Fin S.card → Prop) [DecidablePred b] : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p => BWPosn p ∧ b p), 2 ^ rankB S p

theorem numB_eq (b : Fin S.card → Prop) [DecidablePred b] :
    numB S b = binNum (BWLe (A := Fin S.card)) BWPosn b := by
  rw [numB, binNum_eq_finsetSum]
  exact Finset.sum_congr rfl fun p _ => by rw [rankB, bitRank_eq_card]

@[simp] theorem numB_bit (a : Fin S.card) : numB S (BWBit a) = BWWeight a := numB_eq S _

@[simp] theorem numB_tgt : numB S BWTgt = BWTarget (Fin S.card) := numB_eq S _

variable {S}

@[simp] theorem mem_items {a : Fin S.card} : a ∈ items S ↔ BWItem a := by
  simp [items, List.mem_filter]

theorem items_get_injective : Function.Injective (items S).get :=
  List.nodup_iff_injective_get.mp ((List.nodup_finRange _).filter _)

theorem items_range (a : Fin S.card) : BWItem a ↔ ∃ j, (items S).get j = a := by
  rw [← mem_items, List.mem_iff_get]

end Decoder

end BinarySubsetSum

/-- The decoder: on a presentation whose order is linear, list the items and
read their weights and the target off it; otherwise return a concrete
no-instance, the presented structure being one too. -/
def bwDecode (S : FinPresentation Language.binWeights) : Option SubsetSumInstance :=
  if BinarySubsetSum.isLinOrdB S then
    some ((BinarySubsetSum.items S).map fun a => BinarySubsetSum.numB S (BWBit a),
      BinarySubsetSum.numB S BWTgt)
  else some ([], 1)

/-- Reindexing a decoded weight list: the concrete question about `l.map g` is
the same question about `g` along `l`. -/
theorem concreteSubsetSum_map {α : Type} (l : List α) (g : α → ℕ) (t : ℕ) :
    ConcreteSubsetSum (l.map g, t) ↔ ∃ J : Finset (Fin l.length), ∑ j ∈ J, g (l.get j) = t := by
  have h : (l.map g).length = l.length := l.length_map g
  have key : ∀ J : Finset (Fin (l.map g).length),
      ∑ j ∈ J, (l.map g).get j = ∑ j ∈ J.map (finCongr h).toEmbedding, g (l.get j) := fun J => by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => by simp [List.get_eq_getElem, List.getElem_map]
  change (∃ J : Finset (Fin (l.map g).length), ∑ j ∈ J, (l.map g).get j = t) ↔ _
  constructor
  · rintro ⟨J, hJ⟩
    exact ⟨J.map (finCongr h).toEmbedding, (key J).symm.trans hJ⟩
  · rintro ⟨J, hJ⟩
    refine ⟨J.map (finCongr h.symm).toEmbedding, (key _).trans ?_⟩
    rw [← hJ]
    exact Finset.sum_congr (by ext j; simp) fun _ _ => rfl

/-- The empty list with a positive target is a concrete no-instance – what the
decoder returns on a structure that is a no-instance for lack of a linear
order. -/
theorem not_concreteSubsetSum_empty : ¬ ConcreteSubsetSum ([], 1) := by
  rintro ⟨J, hJ⟩
  rw [Finset.eq_empty_of_forall_notMem fun j (_ : j ∈ J) => j.elim0] at hJ
  simp at hJ

theorem bwDecode_sound (S : FinPresentation Language.binWeights) (i : SubsetSumInstance)
    (hi : i ∈ bwDecode S) : ConcreteSubsetSum i ↔ Knapsack (Fin S.card) := by
  unfold bwDecode at hi
  split at hi
  · next hlin =>
    rw [Option.mem_def, Option.some.injEq] at hi
    subst hi
    rw [concreteSubsetSum_map]
    refine Iff.symm ((hasSubsetSum_iff_index (BinarySubsetSum.items S).get
      BinarySubsetSum.items_get_injective BinarySubsetSum.items_range
      ((BinarySubsetSum.isLinOrdB_iff S).mp hlin)).trans ?_)
    simp only [BinarySubsetSum.numB_bit, BinarySubsetSum.numB_tgt]
  · next hlin =>
    rw [Option.mem_def, Option.some.injEq] at hi
    subst hi
    refine iff_of_false not_concreteSubsetSum_empty ?_
    rintro ⟨-, hl, -⟩
    exact hlin ((BinarySubsetSum.isLinOrdB_iff S).mpr hl)

theorem bwDecode_total (S : FinPresentation Language.binWeights) (_hpos : 0 < S.card)
    (_hW : DecisionProblem.ofSentence (⊤ : Language.binWeights.Sentence) (Fin S.card)) :
    (bwDecode S).isSome := by
  unfold bwDecode
  split <;> rfl

/-- **The computable decoding of binary-weighted structures.** Together with
`binarySubsetSumEncoding_faithful` it closes the loop: encoded instances are
equidecided, and *every* nonempty finite structure decodes to an equidecided
concrete instance, so `Knapsack` is nowhere hard only on junk. The
well-formedness condition is `⊤` because there is no junk to exclude. -/
def bwDecoding : Decoding Language.binWeights
    (DecisionProblem.ofSentence ⊤) ConcreteSubsetSum Knapsack where
  dec := bwDecode
  sound := bwDecode_sound
  total := bwDecode_total

/-- A presented three-element structure: element `0` an item, elements `1`
and `2` bit positions with `1` the low one, the item's weight and the target
both `1`. The decoder *runs* on it. -/
def bwPres : FinPresentation Language.binWeights where
  card := 3
  relBool := fun {n} R =>
    match n, R with
    | _, .item => fun x => decide (x 0 = 0)
    | _, .posn => fun x => decide (x 0 ≠ 0)
    | _, .bit => fun x => decide (x 0 = 0 ∧ x 1 = 1)
    | _, .tgt => fun x => decide (x 0 = 1)
    | _, .le => fun x => decide (x 0 ≤ x 1)

set_option linter.hashCommand false in
#guard bwDecode bwPres = some ([1], 1)

/-- **Hardness reads back to concrete data**: every nonempty finite
binary-weighted structure is decided by `Knapsack` exactly as some list of
weights and target is by the textbook predicate. -/
theorem exists_concreteSubsetSum_iff (A : Type) [Language.binWeights.Structure A]
    [Finite A] [Nonempty A] : ∃ i, ConcreteSubsetSum i ↔ Knapsack A :=
  bwDecoding.exists_conc_iff A (by simp)

end DescriptiveComplexity
