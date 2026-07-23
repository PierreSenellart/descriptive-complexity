/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Defs

/-!
# Adding up binary weights along the item order

The certificate of a binary-weighted problem walks the items in order and
carries the running total: `PS i` is the total over the chosen items up to
`i`, and `Cy i` the carries of the step that appends `i`. The conditions the
walk must satisfy – every bit the exclusive or of the three inputs, every
carry their majority, no carry into the lowest position, none out of the
highest – are `DescriptiveComplexity.IsChain`, and this file proves the two
statements the `Σ₁` definitions need:

* `DescriptiveComplexity.chain_sound`: a walk really does compute the running
  totals, so at the last item it computes the total;
* `DescriptiveComplexity.exists_chain`: whenever the total fits in the positions,
  a walk exists – the certificate a yes-instance offers.

Nothing here mentions a vocabulary: the items, their order and the bit
positions are all parameters, because the clients need different ones.

* Knapsack walks the instance's own positions, its running totals being
  bounded by the target, which is written there;
* Partition cannot – each half is `total / 2`, which may exceed every number
  the instance can write – so it walks the wider positions of
  `DescriptiveComplexity.Numbers.Wide`;
* 0-1 integer programming walks the same positions as Knapsack but needs one
  walk *per row*, so its guessed relations carry a row argument and each slice
  is a walk of its own.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Chain

variable {A : Type} [Finite A] {ILe : A → A → Prop} {IItem : A → Prop}

/-! ### Partial sums along the item order -/

/-- The running total of the weights `w` over the chosen items up to `i`. -/
noncomputable def PartSum (Le : A → A → Prop) (S : A → Prop) (w : A → ℕ) (i : A) : ℕ :=
  ∑ᶠ j ∈ {j : A | S j ∧ Le j i}, w j

omit [Finite A] in
open Classical in
/-- At the first item, the running total is that item's contribution. -/
theorem partSum_min {S : A → Prop} {w : A → ℕ} (hlin : IsLinOrd (ILe))
    (hS : ∀ i, S i → IItem i) {i : A} (hi : MinPos ILe IItem i) :
    PartSum ILe S w i = if S i then w i else 0 := by
  have hset : {j : A | S j ∧ ILe j i} = {j : A | j = i ∧ S j} := by
    ext j
    constructor
    · rintro ⟨hj, hji⟩
      exact ⟨hlin.2.2.1 j i hji (hi.2 j (hS j hj)), hj⟩
    · rintro ⟨rfl, hj⟩
      exact ⟨hj, hlin.1 j⟩
  by_cases hSi : S i
  · have hsingle : {j : A | j = i ∧ S j} = {i} := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hSi⟩⟩
    rw [PartSum, hset, hsingle, finsum_mem_singleton, if_pos hSi]
  · have hempty : {j : A | j = i ∧ S j} = (∅ : Set A) := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hj⟩
      exact hSi hj
    rw [PartSum, hset, hempty, finsum_mem_empty, if_neg hSi]

open Classical in
/-- Each step of the walk adds one item's contribution. -/
theorem partSum_succ {S : A → Prop} {w : A → ℕ} (hlin : IsLinOrd (ILe))
    (hS : ∀ i, S i → IItem i) {h i : A} (hsucc : SuccPos ILe IItem h i) :
    PartSum ILe S w i = PartSum ILe S w h + if S i then w i else 0 := by
  have hset : {j : A | S j ∧ ILe j i} =
      {j : A | S j ∧ ILe j h} ∪ {j : A | j = i ∧ S j} := by
    ext j
    constructor
    · rintro ⟨hj, hji⟩
      rcases eq_or_ne j i with rfl | hjne
      · exact Or.inr ⟨rfl, hj⟩
      · refine Or.inl ⟨hj, ?_⟩
        rcases hlin.2.2.2 j h with hle | hle
        · exact hle
        · rcases hsucc.2.2.2.2 j (hS j hj) hle hji with h1 | h1
          · exact h1 ▸ hlin.1 j
          · exact absurd h1 hjne
    · rintro (⟨hj, hjh⟩ | ⟨rfl, hj⟩)
      · exact ⟨hj, hlin.2.1 j h i hjh hsucc.2.2.1⟩
      · exact ⟨hj, hlin.1 j⟩
  have hdisj : Disjoint {j : A | S j ∧ ILe j h} {j : A | j = i ∧ S j} := by
    rw [Set.disjoint_left]
    rintro j ⟨hj, hjh⟩ ⟨rfl, -⟩
    exact hsucc.2.2.2.1 (hlin.2.2.1 h j hsucc.2.2.1 hjh)
  rw [PartSum, hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  by_cases hSi : S i
  · have hsingle : {j : A | j = i ∧ S j} = {i} := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hSi⟩⟩
    rw [hsingle, finsum_mem_singleton, if_pos hSi]
    rfl
  · have hempty : {j : A | j = i ∧ S j} = (∅ : Set A) := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hj⟩
      exact hSi hj
    rw [hempty, finsum_mem_empty, if_neg hSi]
    rfl

/-- A running total never exceeds the total. -/
theorem partSum_le {S : A → Prop} {w : A → ℕ} (i : A) :
    PartSum ILe S w i ≤ ∑ᶠ j ∈ {j : A | S j}, w j := by
  classical
  have hset : {j : A | S j} =
      {j : A | S j ∧ ILe j i} ∪ {j : A | S j ∧ ¬ILe j i} := by
    ext j
    constructor
    · intro hj
      by_cases hle : ILe j i
      · exact Or.inl ⟨hj, hle⟩
      · exact Or.inr ⟨hj, hle⟩
    · rintro (⟨hj, -⟩ | ⟨hj, -⟩) <;> exact hj
  have hdisj : Disjoint {j : A | S j ∧ ILe j i} {j : A | S j ∧ ¬ILe j i} := by
    rw [Set.disjoint_left]
    rintro j ⟨-, hle⟩ ⟨-, hnle⟩
    exact hnle hle
  rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  exact Nat.le_add_right _ _

omit [Finite A] in
/-- At the last item, the running total is the total. -/
theorem partSum_max {S : A → Prop} {w : A → ℕ} (hS : ∀ i, S i → IItem i) {i : A}
    (hi : MaxPos ILe IItem i) : PartSum ILe S w i = ∑ᶠ j ∈ {j : A | S j}, w j := by
  have hset : {j : A | S j ∧ ILe j i} = {j : A | S j} := by
    ext j
    exact ⟨fun h => h.1, fun h => ⟨h, hi.2 j (hS j h)⟩⟩
  rw [PartSum, hset]

/-- The parity of three bits, as an iterated equivalence. -/
theorem xor3_iff (x y z : Prop) : Xor x (Xor y z) ↔ (x ↔ (y ↔ z)) := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;> simp [Xor, hx, hy, hz]

/-! ### Walks along the item order -/

variable {P : Type} [Finite P]

/-- The bit that an item contributes at a position: its own bit, if chosen. -/
def ChainAdd (S : A → Prop) (wt : A → P → Prop) (i : A) (p : P) : Prop := S i ∧ wt i p

omit [Finite A] [Finite P] in
open Classical in
/-- An item contributes its weight, or nothing. -/
theorem binNum_chainAdd (PLe : P → P → Prop) (PPosn : P → Prop) (S : A → Prop)
    (wt : A → P → Prop) (i : A) :
    binNum PLe PPosn (ChainAdd S wt i) =
      if S i then binNum PLe PPosn (wt i) else 0 := by
  classical
  by_cases hSi : S i
  · rw [if_pos hSi]
    exact binNum_congr fun p => ⟨fun h => h.2, fun h => ⟨hSi, h⟩⟩
  · rw [if_neg hSi]
    have : binNum PLe PPosn (ChainAdd S wt i) = binNum PLe PPosn (fun _ => False) :=
      binNum_congr fun p => ⟨fun h => hSi h.1, fun h => h.elim⟩
    rw [this, binNum_bot]

/-- **A ripple-carry walk along the items**: `PS i` is the running total up to
`i` and `Cy i` the carries of the step appending `i`. -/
def IsChain (Le : A → A → Prop) (Item : A → Prop) (PLe : P → P → Prop) (PPosn : P → Prop)
    (S : A → Prop) (wt PS Cy : A → P → Prop) : Prop :=
  (∀ i p, MinPos Le Item i → PPosn p → (PS i p ↔ ChainAdd S wt i p)) ∧
  (∀ i j p, SuccPos Le Item i j → PPosn p →
    (PS j p ↔ (PS i p ↔ (ChainAdd S wt j p ↔ Cy j p)))) ∧
  (∀ i j p q, SuccPos Le Item i j → SuccPos PLe PPosn p q →
    (Cy j q ↔ maj (PS i p) (ChainAdd S wt j p) (Cy j p))) ∧
  (∀ i j p, SuccPos Le Item i j → MinPos PLe PPosn p → ¬Cy j p) ∧
  (∀ i j p, SuccPos Le Item i j → MaxPos PLe PPosn p →
    ¬maj (PS i p) (ChainAdd S wt j p) (Cy j p))

variable {PLe : P → P → Prop} {PPosn : P → Prop} {S : A → Prop} {wt PS Cy : A → P → Prop}

/-- **A walk computes the running totals.** -/
theorem chain_sound (hlin : IsLinOrd (ILe)) (hPlin : IsLinOrd PLe)
    (hS : ∀ i, S i → IItem i) (hchain : IsChain ILe IItem PLe PPosn S wt PS Cy) :
    ∀ i : A, IItem i →
      binNum PLe PPosn (PS i) = PartSum ILe S (fun j => binNum PLe PPosn (wt j)) i := by
  obtain ⟨hbase, hstepsum, hstepcarry, hstepbot, hsteptop⟩ := hchain
  have hkey : ∀ (m : ℕ) (i : A), bitRank ILe IItem i = m → IItem i →
      binNum PLe PPosn (PS i) = PartSum ILe S (fun j => binNum PLe PPosn (wt j)) i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro i hr hi
      by_cases hmin : MinPos ILe IItem i
      · rw [partSum_min hlin hS hmin, ← binNum_chainAdd PLe PPosn S wt i]
        exact binNum_congr_on fun p hp => hbase i p hmin hp
      · obtain ⟨h, hsucc⟩ := exists_predPos hlin hi hmin
        have hlt : bitRank ILe IItem h < m := by
          rw [← hr]
          exact bitRank_lt hlin hsucc.1 hsucc.2.2.1 hsucc.2.2.2.1
        have hIH := IH (bitRank ILe IItem h) hlt h rfl hsucc.1
        have hripple := binNum_ripple (a := PS h) (b := ChainAdd S wt i) (s := PS i)
          hPlin ({p : P | PPosn p} : Set P).ncard PPosn (Cy i) False False rfl
          (fun p hp => (hstepsum h i p hsucc hp).trans (xor3_iff _ _ _).symm)
          (fun p q hpq => hstepcarry h i p q hsucc hpq)
          (fun p hp => iff_false_intro (hstepbot h i p hsucc hp))
          (fun p hp => (iff_false_intro (hsteptop h i p hsucc hp)).symm)
          (fun _ => Iff.rfl)
        rw [if_neg not_false, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at hripple
        rw [hripple, hIH, partSum_succ hlin hS hsucc]
        congr 1
        exact binNum_chainAdd PLe PPosn S wt i
  exact fun i hi => hkey _ i rfl hi

/-- **A walk exists** whenever the total fits in the positions: this is the
certificate a yes-instance offers. -/
theorem exists_chain (hlin : IsLinOrd (ILe)) (hPlin : IsLinOrd PLe)
    (hS : ∀ i, S i → IItem i)
    (hbound : (∑ᶠ j ∈ {j : A | S j}, binNum PLe PPosn (wt j)) <
      2 ^ ({p : P | PPosn p} : Set P).ncard) :
    ∃ PS Cy : A → P → Prop, IsChain ILe IItem PLe PPosn S wt PS Cy := by
  classical
  set w : A → ℕ := fun j => binNum PLe PPosn (wt j) with hw
  -- the running totals, decoded
  have hPSex : ∀ i : A, ∃ b : P → Prop, binNum PLe PPosn b = PartSum ILe S w i := fun i =>
    exists_binNum hPlin _ PPosn rfl (PartSum ILe S w i) (lt_of_le_of_lt (partSum_le i) hbound)
  choose PS hPS using hPSex
  -- the carries of each step
  have hCyex : ∀ i : A, ∃ c : P → Prop, ∀ h : A, SuccPos ILe IItem h i →
      (∀ p, PPosn p → (PS i p ↔ (PS h p ↔ (ChainAdd S wt i p ↔ c p)))) ∧
      (∀ p q, SuccPos PLe PPosn p q →
        (c q ↔ maj (PS h p) (ChainAdd S wt i p) (c p))) ∧
      (∀ p, MinPos PLe PPosn p → ¬c p) ∧
      (∀ p, MaxPos PLe PPosn p → ¬maj (PS h p) (ChainAdd S wt i p) (c p)) := by
    intro i
    by_cases hpred : ∃ h, SuccPos ILe IItem h i
    · obtain ⟨h, hsucc⟩ := hpred
      have hstep : PartSum ILe S w h + (if S i then w i else 0) = PartSum ILe S w i :=
        (partSum_succ hlin hS hsucc).symm
      have hb : binNum PLe PPosn (PS h) + binNum PLe PPosn (ChainAdd S wt i) <
          2 ^ ({p : P | PPosn p} : Set P).ncard := by
        rw [hPS h, binNum_chainAdd PLe PPosn S wt i, hstep]
        exact lt_of_le_of_lt (partSum_le i) hbound
      obtain ⟨s, c, hs1, hs2, hs3, hs4, hval⟩ :=
        exists_ripple hPlin _ PPosn (PS h) (ChainAdd S wt i) False rfl (by simpa using hb)
      have hagree : ∀ p, PPosn p → (s p ↔ PS i p) := by
        refine binNum_inj_on hPlin _ PPosn rfl s (PS i) ?_
        rw [hPS i, ← hstep, ← hPS h, ← binNum_chainAdd PLe PPosn S wt i]
        simpa using hval
      refine ⟨c, fun h' hsucc' => ?_⟩
      obtain rfl : h' = h := succPos_left_unique hlin hsucc' hsucc
      exact ⟨fun p hp => ((hagree p hp).symm.trans (hs1 p hp)).trans (xor3_iff _ _ _),
        hs2, fun p hp => (hs3 p hp).mp, hs4⟩
    · exact ⟨fun _ => False, fun h hsucc => absurd ⟨h, hsucc⟩ hpred⟩
  choose Cy hCy using hCyex
  refine ⟨PS, Cy, ?_, ?_, ?_, ?_, ?_⟩
  · -- at the first item the total is that item's contribution
    intro i p hi hp
    refine binNum_inj_on hPlin _ PPosn rfl (PS i) (ChainAdd S wt i) ?_ p hp
    rw [hPS i, binNum_chainAdd PLe PPosn S wt i, partSum_min hlin hS hi]
  · exact fun i j p hij hp => (hCy j i hij).1 p hp
  · exact fun i j p q hij hpq => (hCy j i hij).2.1 p q hpq
  · exact fun i j p hij hp => (hCy j i hij).2.2.1 p hp
  · exact fun i j p hij hp => (hCy j i hij).2.2.2 p hp

end Chain

end DescriptiveComplexity
