/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Increment

/-!
# An address, read block by block

A reduction into a wide machine chooses the order `wmLe` of the instance it
draws, and the whole design of the sweep depends on choosing it **block-major**:
the universe of the instance is a product `T × V` – a block index and a
coordinate – ordered by `DescriptiveComplexity.lexRel`, so that an address is a
*family of blocks*, one per index (`DescriptiveComplexity.wmBlk`). One block per
variable of the kernel, one for the scratch, and the sweep's two structural facts
become theorems about this decomposition:

* **the address order is lexicographic on blocks**
  (`DescriptiveComplexity.wmSetLt_lexRel_iff`): two addresses compare at the least
  index where their blocks differ. So the addresses agreeing on a prefix of the
  blocks form a *contiguous stretch* of the tape, which is what lets a guessed
  relation of arity smaller than the number of variables be kept consistent by
  one state bit rather than by comparing distant cells;
* **the increment carries block by block**
  (`DescriptiveComplexity.wmIncr_lexRel_iff`): there is a last index whose block
  is not full, that block increments, every later block is emptied and every
  earlier one is untouched. That is the roll-over information the sweep folds its
  accumulators by – “which variables have just been requantified” – and it is what
  a machine computes when it increments the mirror of its own head position.

A third fact comes from the same reading and is what a program *on a clock*
lives on:

* **the addresses avoiding a set of blocks are an initial stretch**
  (`DescriptiveComplexity.wmAvoids_of_wmSetLe`), provided the set is closed
  downwards in the index order – the smallest index being the most significant
  digit. So a program that keeps its data in the least significant blocks and
  leaves the others empty never leaves a segment of the tape at the bottom, and
  the surplus blocks multiply its clock while costing it nothing.

All of them are stated at arbitrary linear order relations on `T` and on `V`, so
they apply to whatever key a reduction chooses;
`DescriptiveComplexity.isLinOrd_lexRel` supplies the linearity of the product.
-/

namespace DescriptiveComplexity

/-! ### The blocks of an address -/

section Blocks

variable {T V : Type} {LeT : T → T → Prop} {LeV : V → V → Prop}

/-- **The block of an address at an index**: the coordinates the address holds
there. -/
def wmBlk (s : T × V → Prop) (τ : T) : V → Prop := fun v => s (τ, v)

@[simp]
theorem wmBlk_apply (s : T × V → Prop) (τ : T) (v : V) : wmBlk s τ v ↔ s (τ, v) :=
  Iff.rfl

/-- **The strict order of a block-major product**: strictly earlier index, or the
same index and a strictly earlier coordinate. -/
theorem wmLt_lexRel_iff (hT : IsLinOrd LeT) (p q : T × V) :
    WMLt (lexRel LeT LeV) p q ↔ (WMLt LeT p.1 q.1 ∨ (p.1 = q.1 ∧ WMLt LeV p.2 q.2)) := by
  rcases eq_or_ne p.1 q.1 with heq | hne
  · have hfst : ¬WMLt LeT p.1 q.1 := fun hc => hc.2 (heq ▸ hT.1 q.1)
    have hl : ∀ u v : T × V, u.1 = v.1 → (lexRel LeT LeV u v ↔ LeV u.2 v.2) := by
      intro u v huv
      exact ⟨fun hc => hc.elim (fun hc' => absurd huv hc'.2) fun hc' => hc'.2,
        fun hc => Or.inr ⟨huv, hc⟩⟩
    rw [WMLt, hl p q heq, hl q p heq.symm]
    exact ⟨fun hc => Or.inr ⟨heq, hc⟩,
      fun hc => hc.elim (fun hc' => absurd hc' hfst) fun hc' => hc'.2⟩
  · have hl : ∀ u v : T × V, u.1 ≠ v.1 → (lexRel LeT LeV u v ↔ LeT u.1 v.1) := by
      intro u v huv
      exact ⟨fun hc => hc.elim (fun hc' => hc'.1) fun hc' => absurd hc'.1 huv,
        fun hc => Or.inl ⟨hc, huv⟩⟩
    rw [WMLt, hl p q hne, hl q p (Ne.symm hne)]
    exact ⟨fun hc => Or.inl hc, fun hc => hc.elim id fun hc' => absurd hc'.1 hne⟩

/-- Inside one block, the order of the product is the order of the block. -/
theorem wmLt_same_iff (hT : IsLinOrd LeT) (τ : T) (u w : V) :
    WMLt (lexRel LeT LeV) (τ, u) (τ, w) ↔ WMLt LeV u w :=
  (wmLt_lexRel_iff (LeV := LeV) hT (τ, u) (τ, w)).trans
    ⟨fun hc => hc.elim (fun hc' => absurd (hT.1 τ) hc'.2) fun hc' => hc'.2,
      fun hc => Or.inr ⟨rfl, hc⟩⟩

/-- Two coordinates of the same block name the same element exactly when they are
equal. -/
theorem pair_eq_iff (τ : T) (u w : V) : ((τ, w) = (τ, u)) ↔ w = u :=
  ⟨fun hc => congrArg Prod.snd hc, fun hc => by rw [hc]⟩

/-- **The address order is lexicographic on blocks**: two addresses compare at the
least index where their blocks differ, and there by the order of that block. So
the addresses agreeing on a prefix of the blocks are consecutive. -/
theorem wmSetLt_lexRel_iff (hT : IsLinOrd LeT) (s t : T × V → Prop) :
    WMSetLt (lexRel LeT LeV) s t ↔
      ∃ τ, (∀ σ, WMLt LeT σ τ → ∀ v, (wmBlk s σ v ↔ wmBlk t σ v)) ∧
        WMSetLt LeV (wmBlk s τ) (wmBlk t τ) := by
  constructor
  · rintro ⟨⟨τ, v⟩, hbelow, hs, ht⟩
    refine ⟨τ, fun σ hσ w => hbelow (σ, w) ?_, v, fun w hw => hbelow (τ, w) ?_, hs, ht⟩
    · exact (wmLt_lexRel_iff hT (σ, w) (τ, v)).mpr (Or.inl hσ)
    · exact (wmLt_same_iff hT τ w v).mpr hw
  · rintro ⟨τ, hprefix, v, hbelow, hs, ht⟩
    refine ⟨(τ, v), fun q hq => ?_, hs, ht⟩
    obtain ⟨σ, w⟩ := q
    rcases (wmLt_lexRel_iff hT (σ, w) (τ, v)).mp hq with hc | ⟨hc, hc'⟩
    · exact hprefix σ hc w
    · have hst : σ = τ := hc
      rw [hst]
      exact hbelow w hc'

/-! ### The working region

A program that keeps its data in the *least significant* blocks and leaves the
others empty never leaves an initial stretch of the tape: the smallest block
index is the most significant digit, so putting anything in a block a program
avoids makes an address bigger than every address that avoids it. That is what
buys a clocked program its budget – the surplus blocks multiply the clock and
cost the program nothing – and what makes “the region” a segment rather than a
scattered set. -/

/-- **An address avoids a set of block indices** when its blocks there are
empty. -/
def wmAvoids (H : T → Prop) (s : T × V → Prop) : Prop := ∀ τ, H τ → ∀ v, ¬s (τ, v)

/-- The greatest address avoiding a set of blocks: full everywhere else. -/
def wmAvoidTop (H : T → Prop) : T × V → Prop := fun p => ¬H p.1

/-- **Every address avoiding a set of blocks is at or below its top.** -/
theorem wmSetLe_wmAvoidTop [Finite T] [Finite V] (hT : IsLinOrd LeT) (hV : IsLinOrd LeV)
    {H : T → Prop}
    {s : T × V → Prop} (hs : wmAvoids H s) :
    WMSetLe (lexRel LeT LeV) s (wmAvoidTop H) :=
  wmSetLe_of_subset (isLinOrd_lexRel hT hV) fun p hp hc => hs p.1 hc p.2 hp

/-- **The region is an initial stretch of the tape**: an address below one that
avoids a *downward-closed* set of blocks avoids it too. So a sweep upwards stays
in the region until it leaves it once and for all, and the program never has to
say where it is. -/
theorem wmAvoids_of_wmSetLe [Finite T] [Finite V] (hT : IsLinOrd LeT) (hV : IsLinOrd LeV)
    {H : T → Prop} (hdown : ∀ τ σ : T, LeT τ σ → H σ → H τ)
    {s t : T × V → Prop} (hle : WMSetLe (lexRel LeT LeV) s t) (ht : wmAvoids H t) :
    wmAvoids H s := by
  intro τ hτ v hs
  -- The least avoided block `s` is not empty at.
  obtain ⟨τ₀, ⟨hτ₀, w, hw⟩, hmin⟩ :=
    exists_least hT (P := fun σ => H σ ∧ ∃ v, s (σ, v)) ⟨τ, hτ, v, hs⟩
  -- There `t` is empty and `s` is not, and below it both are: so `t < s`.
  have hlt : WMSetLt (lexRel LeT LeV) t s := by
    refine (wmSetLt_lexRel_iff hT t s).mpr ⟨τ₀, fun σ hσ u => ?_, ?_⟩
    · have hσH : H σ := hdown σ τ₀ hσ.1 hτ₀
      exact iff_of_false (ht σ hσH u) fun hc => hσ.2 (hmin σ ⟨hσH, u, hc⟩)
    · refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_empty hV (ht τ₀ hτ₀) _, fun hc => ?_⟩
      exact ht τ₀ hτ₀ w ((iff_of_eq (congrFun hc w)).mpr hw)
  -- and that contradicts `s ≤ t`.
  exact ((wmSetLt_iff t s).mp hlt).2
    ((isLinOrd_wmSetLe (isLinOrd_lexRel hT hV)).2.2.1 t s ((wmSetLt_iff t s).mp hlt).1 hle)

/-- **A product plus an opening fits the clock**: a counted program's cost is
not «rounds × width» alone – there is the opening before the evaluation and the
odd step between phases – and an additive term of the region's own size still
fits, at the price of *one more* surplus block than the product alone needs.

The arithmetic: `a · b + s ≤ 2 ^ (2km) + 2 ^ (km) ≤ 2 ^ (2km + 1)`, and
`2km + 1 < (k + j)m` as soon as `k + 1 < j`. -/
theorem mul_add_lt_two_pow {k j m a b s : ℕ} (hkj : k + 1 < j) (hm : 0 < m)
    (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m)) (hs : s ≤ 2 ^ (k * m)) :
    a * b + s < 2 ^ ((k + j) * m) := by
  have hprod : a * b ≤ 2 ^ (k * m) * 2 ^ (k * m) := Nat.mul_le_mul ha hb
  have hsum : a * b + s ≤ 2 ^ (k * m) * 2 ^ (k * m) + 2 ^ (k * m) :=
    Nat.add_le_add hprod hs
  have hle : 2 ^ (k * m) ≤ 2 ^ (k * m) * 2 ^ (k * m) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (k * m))
  have hdouble : 2 ^ (k * m) * 2 ^ (k * m) + 2 ^ (k * m) ≤ 2 ^ (k * m + k * m + 1) := by
    rw [Nat.pow_succ, Nat.pow_add]
    omega
  refine lt_of_le_of_lt (hsum.trans hdouble) (Nat.pow_lt_pow_right (by omega) ?_)
  nlinarith

/-- **A product and an opening twice the region fit the clock**: the same sum as
`mul_add_lt_two_pow` with the additive term allowed a whole extra factor of
`2 ^ m` – which is what an opening that sweeps the file *and* the region costs,
where the region is `2 ^ (k · m)` and the sweep goes out and back. One working
block is enough for it (`1 ≤ k`), since the opening is then below the product
itself. -/
theorem mul_add_lt_two_pow' {k j m a b s : ℕ} (hk : 1 ≤ k) (hkj : k + 1 < j)
    (hm : 0 < m) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hs : s ≤ 2 ^ ((k + 1) * m)) :
    a * b + s < 2 ^ ((k + j) * m) := by
  have hprod : a * b ≤ 2 ^ (k * m) * 2 ^ (k * m) := Nat.mul_le_mul ha hb
  have hsle : s ≤ 2 ^ (k * m) * 2 ^ (k * m) := by
    refine hs.trans ?_
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hsum : a * b + s ≤ 2 ^ (k * m) * 2 ^ (k * m) + 2 ^ (k * m) * 2 ^ (k * m) :=
    Nat.add_le_add hprod hsle
  have hdouble : 2 ^ (k * m) * 2 ^ (k * m) + 2 ^ (k * m) * 2 ^ (k * m) ≤
      2 ^ (k * m + k * m + 1) := by
    rw [Nat.pow_succ, Nat.pow_add]
    omega
  refine lt_of_le_of_lt (hsum.trans hdouble) (Nat.pow_lt_pow_right (by omega) ?_)
  nlinarith

/-- **The increment of an address carries block by block**: at the last index
whose block is not full, that block increments; every later block is emptied and
every earlier one is left alone. The index is the *carry index*, and which blocks
it empties is exactly the roll-over information the sweep folds by. -/
theorem wmIncr_lexRel_iff (hT : IsLinOrd LeT) (s t : T × V → Prop) :
    WMIncr (lexRel LeT LeV) s t ↔
      ∃ τ, (∀ σ, WMLt LeT τ σ → ∀ v, wmBlk s σ v) ∧
        WMIncr LeV (wmBlk s τ) (wmBlk t τ) ∧
        (∀ σ, WMLt LeT σ τ → ∀ v, (wmBlk t σ v ↔ wmBlk s σ v)) ∧
        ∀ σ, WMLt LeT τ σ → ∀ v, ¬wmBlk t σ v := by
  constructor
  · rintro ⟨⟨τ, u⟩, hu, habove, ht⟩
    have hfull : ∀ σ, WMLt LeT τ σ → ∀ v, s (σ, v) := fun σ hσ v =>
      habove (σ, v) ((wmLt_lexRel_iff hT (τ, u) (σ, v)).mpr (Or.inl hσ))
    refine ⟨τ, hfull, ⟨u, hu, fun w hw => habove (τ, w) ((wmLt_same_iff hT τ u w).mpr hw),
      fun w => ?_⟩, fun σ hσ v => ?_, fun σ hσ v => ?_⟩
    · refine (ht (τ, w)).trans (or_congr (pair_eq_iff τ u w)
        (and_congr Iff.rfl (not_congr (wmLt_same_iff hT τ u w))))
    · have hne : (σ, v) ≠ (τ, u) := by
        intro hc
        have hst : σ = τ := congrArg Prod.fst hc
        rw [hst] at hσ
        exact hσ.2 (hT.1 τ)
      have hna : ¬WMLt (lexRel LeT LeV) (τ, u) (σ, v) := by
        rw [wmLt_lexRel_iff hT]
        rintro (hc | ⟨hc, -⟩)
        · exact hσ.2 hc.1
        · rw [show σ = τ from hc.symm] at hσ
          exact hσ.2 (hT.1 τ)
      refine (ht (σ, v)).trans ⟨fun hc => (hc.resolve_left hne).1, fun hc => Or.inr ⟨hc, hna⟩⟩
    · intro hc
      rcases (ht (σ, v)).mp hc with hc' | ⟨-, hc'⟩
      · have hst : σ = τ := congrArg Prod.fst hc'
        rw [hst] at hσ
        exact hσ.2 (hT.1 τ)
      · exact hc' ((wmLt_lexRel_iff hT (τ, u) (σ, v)).mpr (Or.inl hσ))
  · rintro ⟨τ, hfull, ⟨u, hu, habove, hblk⟩, hbefore, hafter⟩
    refine ⟨(τ, u), hu, fun q hq => ?_, fun q => ?_⟩
    · obtain ⟨σ, w⟩ := q
      rcases (wmLt_lexRel_iff hT (τ, u) (σ, w)).mp hq with hc | ⟨hc, hc'⟩
      · exact hfull σ hc w
      · have hst : τ = σ := hc
        rw [← hst]
        exact habove w hc'
    · obtain ⟨σ, v⟩ := q
      rcases eq_or_ne σ τ with hst | hne
      · rw [hst]
        exact (hblk v).trans (or_congr (pair_eq_iff τ u v).symm
          (and_congr Iff.rfl (not_congr (wmLt_same_iff hT τ u v).symm)))
      · rcases hT.2.2.2 σ τ with hle | hle
        · have hσ : WMLt LeT σ τ := ⟨hle, fun hc => hne (hT.2.2.1 σ τ hle hc)⟩
          have hne' : (σ, v) ≠ (τ, u) := fun hc => hne (congrArg Prod.fst hc)
          have hna : ¬WMLt (lexRel LeT LeV) (τ, u) (σ, v) := by
            rw [wmLt_lexRel_iff hT]
            rintro (hc | ⟨hc, -⟩)
            · exact hσ.2 hc.1
            · exact hne hc.symm
          exact (hbefore σ hσ v).trans
            ⟨fun hc => Or.inr ⟨hc, hna⟩, fun hc => (hc.resolve_left hne').1⟩
        · have hσ : WMLt LeT τ σ := ⟨hle, fun hc => hne (hT.2.2.1 σ τ hc hle)⟩
          refine iff_of_false (hafter σ hσ v) ?_
          rintro (hc | ⟨-, hc⟩)
          · exact hne (congrArg Prod.fst hc)
          · exact hc ((wmLt_lexRel_iff hT (τ, u) (σ, v)).mpr (Or.inl hσ))

end Blocks

end DescriptiveComplexity
