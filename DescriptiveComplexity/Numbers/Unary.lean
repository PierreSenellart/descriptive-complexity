/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod

/-!
# Unary representation of numbers in finite structures

Representation (A) of the design notes: a number carried by an instance is
the *cardinality of a marked set* – `Set.ncard` is the decoding function, and
no order is needed. This file provides the shared lemma kit so that problem
files do not hand-roll cardinality reasoning:

* `DescriptiveComplexity.ncard_image_equiv`: invariance of the decoded number under
  equivalences (this is what feeds `DecisionProblem.iso_invariant` proofs);
* `DescriptiveComplexity.initSeg` and `DescriptiveComplexity.ncard_initSeg`: the canonical encoding
  of `k ≤ n` as the initial segment of `Fin n`;
* `DescriptiveComplexity.ncard_compl_eq`: complement cardinality (`n - k`), as used by
  the Vertex Cover ↔ Independent Set reductions;
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

/-- Complement cardinality: the marked complement encodes `n - k`. -/
theorem ncard_compl_eq {A : Type} [Finite A] (s : Set A) :
    sᶜ.ncard = Nat.card A - s.ncard :=
  Set.ncard_compl s

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
