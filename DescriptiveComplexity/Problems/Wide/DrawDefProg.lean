/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefVar
import DescriptiveComplexity.Problems.Wide.DrawVar
import DescriptiveComplexity.Problems.Wide.DrawRound

/-!
# The last four layers, and the program's own kits

One round, one variable's machinery, the evaluation's spine and the outer loop
are the four remaining combinators, and each is checkpoints over machineries
that are already discharged. What is new here is small and concrete: the
program's own kits (`DescriptiveComplexity.Draw.Data.compareKit`,
`copyKit`, `seekKit`, `advKit`, `clearMirKit`, `tgtTopKit`) and the two
questions they are written from — every stage track agrees with its next
(`DescriptiveComplexity.Draw.Data.cmpG`), and the working cell is at an
argument-tagged block. Each is a conjunction, a disjunction or an equivalence
of the three atoms, indexed by a finite type.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} {Q P : Type} [Fintype Q]
variable [Fintype dt.SlotIx]

/-! ### One round -/

/-- **One round's rules are definable**: the branch checkpoint's dispatches
read the two gate flags, which are control slots. -/
theorem uRulesDefinable_roundRule {PG PX SG SX : Type} {ShG : SG → Type}
    {ShX : SX → Type} {emb : RoundPh PG PX → P}
    {ruleG : ∀ (e : Env L) (s : SG), ShG s → Rule e.α Q dt.SlotIx P}
    {ruleX : ∀ (e : Env L) (s : SX), ShX s → Rule e.α Q dt.SlotIx P}
    {pxEntry exitPh : P} {existFlag allFlag : Q}
    (hG : URulesDefinable ruleG) (hX : URulesDefinable ruleX) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.roundRule e.one emb (ruleG e) (ruleX e) pxEntry exitPh existFlag
        allFlag := by
  have hflags : UGDefinable (L := L) (Q := Q)
      fun e f (_ : dt.SlotIx → e.α) => f existFlag = e.one ∧ f allFlag = e.one :=
    (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) existFlag).and
      (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) allFlag)
  rintro (s | - | s) ρ
  · exact hG s ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hflags)
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hflags.not)
        (fun _ _ _ => rfl) fun _ _ _ => rfl
  · exact hX s ρ

/-! ### One variable's machinery -/

/-- **One variable's machinery is definable**: five checkpoints, the VAL
clear, the exhaustion test and the block-indexed increment, with the folds as
the caller's control updates and the two stage writes as single-slot
updates. -/
theorem uRulesDefinable_varRule {PG PX SG SX : Type} {ShG : SG → Type}
    {ShX : SX → Type} {emb : VarPh dt.CarryB PG PX → P}
    {ruleG : ∀ (e : Env L) (s : SG), ShG s → Rule e.α Q dt.SlotIx P}
    {ruleX : ∀ (e : Env L) (s : SX), ShX s → Rule e.α Q dt.SlotIx P}
    {pgEntry pxEntry exitPh : P} {newSlot : dt.SlotIx} {gateFlag : Q}
    {accBit : ∀ e : Env L, (Q → e.α) → Prop}
    {enterSt initSt postFold :
      ∀ e : Env L, (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    {storeCarry : ∀ e : Env L,
      dt.CarryB → (Q → e.α) → (dt.SlotIx → e.α) → Q → e.α}
    (hG : URulesDefinable ruleG) (hX : URulesDefinable ruleX)
    (hacc : UGDefinable fun e f (_ : dt.SlotIx → e.α) => accBit e f)
    (henter : UStDefinable enterSt) (hinit : UStDefinable initSt)
    (hpost : UStDefinable postFold)
    (hcarry : ∀ b : dt.CarryB, UStDefinable fun e => storeCarry e b) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.varRule e.zero e.one emb (ruleG e) (ruleX e) pgEntry pxEntry exitPh
        newSlot gateFlag (accBit e) (enterSt e) (initSt e) (postFold e)
        (storeCarry e) := by
  have hstay : UGDefinable (L := L) (Q := Q)
      fun e (_ : Q → e.α) (g : dt.SlotIx → e.α) => ¬(g Slot.wk = e.one) :=
    (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
  have hgate := uGDefinable_ctlOne (L := L) (W := dt.SlotIx) gateFlag
  rintro (- | s | - | - | s | - | - | - | -) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG henter fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact hG s ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hgate)
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hgate.not)
        (fun _ _ _ => rfl) (uTrDefinable_id.update newSlot uSlotDefinable_zero)
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG hinit fun _ _ _ => rfl
  · exact hX s ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG hpost fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · have hvalTop : UGDefinable (L := L) (Q := Q)
        fun e (_ : Q → e.α) (g : dt.SlotIx → e.α) =>
          (g Slot.val = e.one ↔
            ∃ j : Fin dt.ki, g (Slot.blk (some (Sum.inr j))) = e.one) :=
      (uGDefinable_trkOne (L := L) (Q := Q) (Slot.val : dt.SlotIx)).iff
        (uGDefinable_exists fun j : Fin dt.ki =>
          uGDefinable_trkOne (L := L) (Q := Q)
            (Slot.blk (some (Sum.inr j)) : dt.SlotIx))
    match ρ with
    | Sum.inl σ => exact TestKit.uRuleDefinable hvalTop σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact IncrKit.uRuleDefinable σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (hcarry b)
        fun _ _ _ => rfl
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        (uTrDefinable_id.update newSlot (uSlotDefinable_bitVal hacc))
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl

/-! ### The evaluation's spine -/

/-- **The evaluation's spine is definable**: one checkpoint per variable
position, the last one erasing the marker towards the sweep's advance or the
post-sweep reset. -/
theorem uRulesDefinable_evalRule {PM SM : Type} {nv : ℕ} {ShM : SM → Type}
    {ruleM : ∀ (e : Env L) (s : SM), ShM s →
      Rule e.α Q dt.SlotIx (OuterPh (EvalPh nv PM))}
    {subEntry : Fin nv → PM} (hM : URulesDefinable ruleM) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.evalRule e.zero e.one (ruleM e) subEntry := by
  have hltp := uGDefinable_trkOne (L := L) (Q := Q) (Slot.ltp : dt.SlotIx)
  rintro (k | s) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      by_cases hk : (k : ℕ) < nv
      · simp only [evalRule, dif_pos hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
          fun _ _ _ => rfl
      · simp only [evalRule, dif_neg hk]
        exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hltp.not)
          (fun _ _ _ => rfl) (uTrDefinable_id.update Slot.wk uSlotDefinable_zero)
    | .dspB =>
      by_cases hk : (k : ℕ) < nv
      · simp only [evalRule, if_pos hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
          fun _ _ _ => rfl
      · simp only [evalRule, if_neg hk]
        exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ (uGDefinable_exitG.and hltp)
          (fun _ _ _ => rfl) (uTrDefinable_id.update Slot.wk uSlotDefinable_zero)
  · exact hM s ρ

/-! ### The program's own questions and rewrite -/

/-- **The convergence test's question is definable**: one equivalence per
fixed-point variable. -/
theorem uGDefinable_cmpG :
    UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g => dt.cmpG e.one g :=
  (uGDefinable_forall fun i : dt.d.B.ι =>
    (uGDefinable_trkOne (L := L) (Q := Q) (Slot.old i : dt.SlotIx)).iff
      (uGDefinable_trkOne (L := L) (Q := Q) (Slot.new i : dt.SlotIx))).congr
    fun _ _ _ => Iff.rfl

/-- **The copy-back's rewrite is definable**: every stage track takes its
next's digit, and every other slot rides along – a decision made slot by
slot. -/
theorem uTrDefinable_copyKit_wrG {ph : P} :
    UTrDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
      (dt.copyKit (A := e.α) (Q := Q) (P := P) ph).wrG g := by
  intro s
  match s with
  | .old i => exact (uSlotDefinable_trk (Slot.new i : dt.SlotIx)).congr fun _ _ _ => rfl
  | .reg => exact (uSlotDefinable_trk (Slot.reg : dt.SlotIx)).congr fun _ _ _ => rfl
  | .regFirst =>
    exact (uSlotDefinable_trk (Slot.regFirst : dt.SlotIx)).congr fun _ _ _ => rfl
  | .regLast =>
    exact (uSlotDefinable_trk (Slot.regLast : dt.SlotIx)).congr fun _ _ _ => rfl
  | .blk b => exact (uSlotDefinable_trk (Slot.blk b : dt.SlotIx)).congr fun _ _ _ => rfl
  | .name j => exact (uSlotDefinable_trk (Slot.name j : dt.SlotIx)).congr fun _ _ _ => rfl
  | .pdd => exact (uSlotDefinable_trk (Slot.pdd : dt.SlotIx)).congr fun _ _ _ => rfl
  | .mir => exact (uSlotDefinable_trk (Slot.mir : dt.SlotIx)).congr fun _ _ _ => rfl
  | .tgt => exact (uSlotDefinable_trk (Slot.tgt : dt.SlotIx)).congr fun _ _ _ => rfl
  | .sav => exact (uSlotDefinable_trk (Slot.sav : dt.SlotIx)).congr fun _ _ _ => rfl
  | .val => exact (uSlotDefinable_trk (Slot.val : dt.SlotIx)).congr fun _ _ _ => rfl
  | .wk => exact (uSlotDefinable_trk (Slot.wk : dt.SlotIx)).congr fun _ _ _ => rfl
  | .bot => exact (uSlotDefinable_trk (Slot.bot : dt.SlotIx)).congr fun _ _ _ => rfl
  | .ltp => exact (uSlotDefinable_trk (Slot.ltp : dt.SlotIx)).congr fun _ _ _ => rfl
  | .new i => exact (uSlotDefinable_trk (Slot.new i : dt.SlotIx)).congr fun _ _ _ => rfl

/-! ### The outer loop -/

/-- **The outer program's rules are definable**: thirteen kits with their exit
rules, the initial step, and the evaluation's rules as the parameter. -/
theorem uRulesDefinable_outerRule {PE SE : Type} {ShE : SE → Type}
    {ruleE : ∀ (e : Env L) (s : SE), ShE s → Rule e.α Q dt.SlotIx (OuterPh PE)}
    {evalEntry evalEntryOut : PE} (hE : URulesDefinable ruleE) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.outerRule e.zero e.one (ruleE e) evalEntry evalEntryOut := by
  have hltp := uGDefinable_trkOne (L := L) (Q := Q) (Slot.ltp : dt.SlotIx)
  rintro (- | - | - | - | - | - | - | - | - | - | - | - | - | - | s) ρ
  · exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      ((uTrDefinable_id.update Slot.wk uSlotDefinable_one).update Slot.bot
        uSlotDefinable_one)
  · match ρ with
    | Sum.inl σ =>
      exact MapKit.uRuleDefinable
        (uGDefinable_exists fun b : Fin dt.ko ⊕ Fin dt.ki =>
          uGDefinable_trkOne (L := L) (Q := Q)
            (Slot.blk (some b) : dt.SlotIx)) σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact SeekKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        ((uTrDefinable_id.update Slot.wk uSlotDefinable_zero).update Slot.ltp
          uSlotDefinable_one)
  · match ρ with
    | Sum.inl σ => exact ResetKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact AdvKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ResetKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ClearKit.uRuleDefinable σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩
        (uGDefinable_exitG.and (uGDefinable_cmpG.iff (uGDefinable_const (b = true))))
        (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact FlagSweepKit.uRuleDefinable uGDefinable_cmpG σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hltp (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        (uTrDefinable_copyKit_wrG (P := OuterPh PE) (ph := OuterPh.copyP))
  · match ρ with
    | Sum.inl σ =>
      exact WriteSweepKit.uRuleDefinable
        (wrG := fun e =>
          (dt.copyKit (A := e.α) (Q := Q) (P := OuterPh PE) OuterPh.copyP).wrG)
        (uTrDefinable_copyKit_wrG (P := OuterPh PE) (ph := OuterPh.copyP)) σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hltp (fun _ _ _ => rfl) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact ρ.elim
  · exact hE s ρ

end Data

end Draw

end DescriptiveComplexity
