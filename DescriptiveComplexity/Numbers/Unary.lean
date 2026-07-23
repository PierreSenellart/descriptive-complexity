/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod

/-!
# Unary representation of numbers in finite structures

Representation (A) of the design notes: a number carried by an instance is
the *cardinality of a marked set* – `Set.ncard` is the decoding function, and
no order is needed. This file provides the shared lemma kit so that problem
files do not hand-roll cardinality reasoning:

* `DescriptiveComplexity.ncard_image_equiv` and its predicate form
  `DescriptiveComplexity.ncard_setOf_equiv`: invariance of the decoded number under
  equivalences (this is what feeds `DecisionProblem.iso_invariant` proofs);
* `DescriptiveComplexity.initSeg` and `DescriptiveComplexity.ncard_initSeg`: the canonical encoding
  of `k ≤ n` as the initial segment of `Fin n`;
* `DescriptiveComplexity.ncard_compl_eq` and
  `DescriptiveComplexity.ncard_compl_le_ncard_compl_iff`: complement cardinality
  (`n - k`) and the resulting *reversal* of comparisons, which is what the
  Vertex Cover ↔ Independent Set reductions run on;
* `DescriptiveComplexity.nonempty_embedding_iff_ncard_le`: comparing decoded numbers is
  comparing sizes – the bridge to the second-order rendering of a threshold,
  where the injection witnessing the comparison is guessed as a relation
  variable (used by the `Σ₁` definition of Clique);
* `DescriptiveComplexity.nonempty_embedding_iff_ncard_le₂` and
  `DescriptiveComplexity.ncard_setOf_equiv₂`: the same, for a threshold carried by a
  marked *binary* relation – the arity-2 form of the representation, which is
  what problems counting arcs rather than vertices need;
* `DescriptiveComplexity.ncard_tagged_eq_sum`: cardinality under tag-disjoint union –
  the tagged framework's *addition*;
* `DescriptiveComplexity.ncard_univ_pi`: cardinality of a product of marked sets over
  the coordinates of a tuple – the tagged framework's *multiplication*.

Unary representation keeps numbers polynomial in the instance size; problems
whose numbers must be exponential (SubsetSum and friends) use the binary
representation of `DescriptiveComplexity.Numbers.Binary` instead.
-/

namespace DescriptiveComplexity

open Set

/-- The decoded number is invariant under equivalences of the universe. -/
theorem ncard_image_equiv {A B : Type} (e : A ≃ B) (s : Set A) :
    (e '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s e.injective

/-- The number encoded by a marked set is invariant under an equivalence of
universes carrying one mark predicate to the other. This is the form the
transport of a threshold along an isomorphism (or along the equivalence
underlying a one-dimensional interpretation) takes in practice. -/
theorem ncard_setOf_equiv {A B : Type} (u : B ≃ A) {KB : B → Prop} {KA : A → Prop}
    (hK : ∀ b, KB b ↔ KA (u b)) : {b | KB b}.ncard = {a | KA a}.ncard := by
  rw [← ncard_image_equiv u {b | KB b}]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hK b).mp hb
  · intro ha
    exact ⟨u.symm a, (hK _).mpr (by simpa using ha), by simp⟩

/-- Pulling a mark predicate back along `u.symm` does not change the number it
encodes: the special case of `DescriptiveComplexity.ncard_setOf_equiv` where the
predicate on the target universe is the transported one. -/
theorem ncard_setOf_symm {A B : Type} (u : B ≃ A) (S : B → Prop) :
    {b | S b}.ncard = {a | S (u.symm a)}.ncard :=
  ncard_setOf_equiv u fun b => by simp

/-- The canonical unary encoding of `k` in a universe of size `n`: the
initial segment of `Fin n` of length `k`. -/
def initSeg (n k : ℕ) : Set (Fin n) := {i | (i : ℕ) < k}

/-- The initial segment of length `k ≤ n` indeed encodes `k`. -/
theorem ncard_initSeg (n k : ℕ) (h : k ≤ n) : (initSeg n k).ncard = k := by
  rw [← Nat.card_coe_set_eq]
  have e : initSeg n k ≃ Fin k :=
    { toFun := fun p => ⟨p.1.1, p.2⟩
      invFun := fun j => ⟨⟨j.1, lt_of_lt_of_le j.2 h⟩, j.2⟩
      left_inv := fun p => rfl
      right_inv := fun j => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A decoded number never exceeds the size of the universe. -/
theorem ncard_le_card {A : Type} [Finite A] (s : Set A) : s.ncard ≤ Nat.card A := by
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ s)

/-- Complement cardinality: the marked complement encodes `n - k`. -/
theorem ncard_compl_eq {A : Type} [Finite A] (s : Set A) :
    sᶜ.ncard = Nat.card A - s.ncard :=
  Set.ncard_compl s

/-- Complementation *reverses* the comparison of decoded numbers – the
subtraction `n - k` is monotone decreasing in `k`. This is the arithmetic
content of the Vertex Cover ↔ Independent Set reductions. -/
theorem ncard_compl_le_ncard_compl_iff {A : Type} [Finite A] (s t : Set A) :
    sᶜ.ncard ≤ tᶜ.ncard ↔ t.ncard ≤ s.ncard := by
  rw [ncard_compl_eq, ncard_compl_eq]
  have hs := ncard_le_card s
  have ht := ncard_le_card t
  omega

/-- Comparing a complement with a set, the two sides swap under
complementation: `n - k ≤ l` iff `n - l ≤ k`. -/
theorem ncard_compl_le_iff {A : Type} [Finite A] (s t : Set A) :
    sᶜ.ncard ≤ t.ncard ↔ tᶜ.ncard ≤ s.ncard := by
  rw [ncard_compl_eq, ncard_compl_eq]
  have hs := ncard_le_card s
  have ht := ncard_le_card t
  omega

/-- **Comparing decoded numbers is comparing sizes**: on a finite universe the
number encoded by the marked set `P` is at most the one encoded by `Q` exactly
when the `P`-elements inject into the `Q`-elements. This is the bridge between
the cardinality reading of a threshold and its second-order rendering, where
the injection is *guessed* as a binary relation variable. -/
theorem nonempty_embedding_iff_ncard_le {A : Type} [Finite A] (P Q : A → Prop) :
    Nonempty ({x // P x} ↪ {x // Q x}) ↔ {x | P x}.ncard ≤ {x | Q x}.ncard := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hP : {x | P x}.ncard = Nat.card {x // P x} := (Nat.card_coe_set_eq _).symm
  have hQ : {x | Q x}.ncard = Nat.card {x // Q x} := (Nat.card_coe_set_eq _).symm
  rw [hP, hQ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Function.Embedding.nonempty_iff_card_le

/-! ### Thresholds on pairs

Problems whose objective counts *arcs* rather than vertices – Feedback Arc Set,
Max Cut – need a threshold that can reach `n²`, which a marked subset of the
universe cannot. The same unary idea one arity up does reach it: the number is
the cardinality of a marked *binary* relation, decoded as the `Set.ncard` of the
corresponding set of pairs. It stays order-free and isomorphism-invariant, and
the whole kit above applies at the type `A × A`; the two lemmas below are just
its curried form. -/

/-- Comparing decoded numbers is comparing sizes, for thresholds carried by a
binary relation. -/
theorem nonempty_embedding_iff_ncard_le₂ {A : Type} [Finite A] (P Q : A → A → Prop) :
    Nonempty ({p : A × A // P p.1 p.2} ↪ {p : A × A // Q p.1 p.2}) ↔
      {p : A × A | P p.1 p.2}.ncard ≤ {p : A × A | Q p.1 p.2}.ncard :=
  nonempty_embedding_iff_ncard_le (fun p : A × A => P p.1 p.2) fun p : A × A => Q p.1 p.2

/-- The number encoded by a marked binary relation is invariant under an
equivalence of universes carrying one relation to the other. -/
theorem ncard_setOf_equiv₂ {A B : Type} (u : B ≃ A) {RB : B → B → Prop}
    {RA : A → A → Prop} (hR : ∀ b b', RB b b' ↔ RA (u b) (u b')) :
    {p : B × B | RB p.1 p.2}.ncard = {p : A × A | RA p.1 p.2}.ncard :=
  ncard_setOf_equiv (u.prodCongr u) fun p => hR p.1 p.2

/-- Cardinality under tag-disjoint union: on a universe of tagged elements,
the cardinalities of the per-tag marked sets add up. This is how the tagged
framework represents *addition*. -/
theorem ncard_tagged_eq_sum {T A : Type} [Fintype T] [Finite A] (s : T → Set A) :
    {p : T × A | p.2 ∈ s p.1}.ncard = ∑ t, (s t).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine (Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun t a => a ∈ s t)).trans ?_
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl fun t _ => Nat.card_coe_set_eq (s t)

/-- Cardinality of a product of marked sets over tuple coordinates: the
cardinalities multiply. This is how the tagged framework represents
*multiplication*. -/
theorem ncard_univ_pi {ι A : Type} [Fintype ι] [Finite A] (s : ι → Set A) :
    (Set.univ.pi s).ncard = ∏ i, (s i).ncard := by
  rw [← Nat.card_coe_set_eq]
  have e : Set.univ.pi s ≃ ∀ i, s i :=
    (Equiv.subtypeEquivRight fun w => by simp [Set.mem_pi]).trans
      (Equiv.subtypePiEquivPi (p := fun i a => a ∈ s i))
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_coe_set_eq (s i)

end DescriptiveComplexity
