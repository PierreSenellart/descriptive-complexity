/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefTower
import DescriptiveComplexity.Problems.Wide.DrawStageAtom

/-!
# The two guards the program's own sites are written from, and the stage atom

Above the combinators the program stops being generic: its checkpoints are
guarded by `DescriptiveComplexity.Draw.DrawData.exitG` – at the marker, which is
nobody's register – and its trips are named by
`DescriptiveComplexity.Draw.DrawData.nameG` – this cell is the canonically padded
cell of the element whose block is `b` and whose first `dd0` coordinates the
control holds. Both are conjunctions of the three atoms, so both are definable
once and for all, and with them the **stage atom's machinery** – the largest
single subroutine of the program – follows kit by kit.

The naming guard is stated at an arbitrary coordinate function
(`DescriptiveComplexity.Draw.DrawData.nameGF`), the caller owing the
*comparison* `g (name j) = cf f j` rather than the value: the leaf reads of the
element loops compute an encoded tuple there, and what they owe is the same
shape as what the coordinate loops owe.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} {dt : DrawData L} {Q P : Type} [Fintype Q]
variable [Fintype dt.SlotIx]

/-! ### The two guards -/

/-- **The standard exit guard is definable**: at the marker, which is nobody's
register. -/
theorem uGDefinable_exitG :
    UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g => dt.exitG e.one g :=
  ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).and
    (uGDefinable_trkOne (L := L) (Q := Q) (Slot.reg : dt.SlotIx)).not).congr
    fun _ _ _ => Iff.rfl

/-- **A naming guard is definable**, given that each of its coordinates is
compared definably: the block flag and the padding flag are atoms, and the
comparison is the caller's. -/
theorem uGDefinable_nameGF {b : Fin dt.ko ⊕ Fin dt.ki}
    {cf : ∀ e : Env L, (Q → e.α) → Fin dt.dd0 → e.α}
    (hcf : ∀ j : Fin dt.dd0, UGDefinable (Q := Q) (W := dt.SlotIx)
      fun e f g => g (Slot.name j) = cf e f j) :
    UGDefinable (L := L) fun e (f : Q → e.α) g => dt.nameGF e.one b (cf e) f g :=
  (((uGDefinable_trkOne (L := L) (Q := Q) (Slot.blk (some b) : dt.SlotIx)).and
    ((uGDefinable_trkOne (L := L) (Q := Q) (Slot.pdd : dt.SlotIx)).and
      (uGDefinable_forall hcf))).congr fun _ _ _ => Iff.rfl)

/-- **The naming guard of a coordinate loop is definable**: its coordinates are
control slots, so each comparison is one atom. -/
theorem uGDefinable_nameG (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q) :
    UGDefinable (L := L) fun e (f : Q → e.α) g => dt.nameG e.one b coord f g :=
  uGDefinable_nameGF fun j =>
    (uGDefinable_mixEq (L := L) (W := dt.SlotIx) (coord j) (Slot.name j)).congr
      fun _ _ _ => eq_comm

/-! ### The stage atom -/

section Stage

variable {k : ℕ}

/-- **A stage atom's machinery is definable**: eleven kits and their exit
rules, the exits all guarded by the standard one, plus the argument tuple
loops, whose two naming guards are the coordinate loops'. -/
theorem uRulesDefinable_stageRule {emb : StagePh k → P}
    {srcTrack : Fin k → dt.SlotIx}
    {srcBlk dstBlk : Fin k → Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {bitFlag : ∀ e : Env L, (Q → e.α) → Prop}
    {setBit : ∀ e : Env L, Bool → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {initLv advLv : ∀ e : Env L, (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {IsMaxLv : ∀ e : Env L, (Q → e.α) → Prop} {oldSlot : dt.SlotIx}
    {setAv : ∀ e : Env L, Bool → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {exitPh : P}
    (hbit : UGDefinable fun e f (_ : dt.SlotIx → e.α) => bitFlag e f)
    (hset : ∀ b : Bool, UStDefinable fun e => setBit e b)
    (hinit : UStDefinable initLv) (hadv : UStDefinable advLv)
    (hmax : UGDefinable fun e f (_ : dt.SlotIx → e.α) => IsMaxLv e f)
    (hav : ∀ b : Bool, UStDefinable fun e => setAv e b) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.stageRule e.zero e.one emb srcTrack srcBlk dstBlk coord (bitFlag e)
        (setBit e) (initLv e) (advLv e) (IsMaxLv e) oldSlot (setAv e) exitPh := by
  have hex : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g => dt.exitG e.one g :=
    uGDefinable_exitG
  have hstay : UGDefinable (L := L) (Q := Q)
      fun e (_ : Q → e.α) (g : dt.SlotIx → e.α) => ¬(g Slot.wk = e.one) :=
    (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
  rintro (- | - | ⟨ℓ, c⟩ | - | - | - | - | - | - | - | - | -) ρ
  · match ρ with
    | Sum.inl σ => exact CopyKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex hinit fun _ _ _ => rfl
  · exact uRulesDefinable_tupleRule (wk := Slot.wk) (rg := Slot.reg)
      (tSrc := srcTrack ℓ) (tDst := Slot.tgt)
      (emb := fun p => emb (StagePh.tupP ℓ p)) (exitPh := stageNextTup emb ℓ)
      (uGDefinable_nameG (srcBlk ℓ) coord) (uGDefinable_nameG (dstBlk ℓ) coord)
      hbit hset hinit hadv hmax c ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl)
        (uTrDefinable_id.update Slot.wk uSlotDefinable_zero)
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ResetKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact SeekKit.uRuleDefinable σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩
        (hex.and ((uGDefinable_trkOne (L := L) (Q := Q) oldSlot).iff
          (uGDefinable_const (b = true)))) (hav b) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact CopyKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl)
        (uTrDefinable_id.update Slot.wk uSlotDefinable_zero)
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ResetKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact SeekKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hex (fun _ _ _ => rfl) fun _ _ _ => rfl

end Stage

end DrawData

end Draw

end DescriptiveComplexity
