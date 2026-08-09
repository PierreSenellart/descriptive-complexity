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

Both are stated at arbitrary linear order relations on `T` and on `V`, so they
apply to whatever key a reduction chooses;
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
