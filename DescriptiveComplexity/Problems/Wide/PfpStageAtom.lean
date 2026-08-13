/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTuple
import DescriptiveComplexity.Problems.Wide.PfpSites
import DescriptiveComplexity.Problems.Wide.PfpReset

/-!
# The stage atom's machinery: a random access

The largest atom subroutine of the EXPSPACE program: to evaluate a stage atom
`R i' (w̄)`, the machine saves its mirror,
builds the target address – one tuple loop per argument position, copying
the source block of VAL or MIRROR into the target's block by named bits –
resets to the bottom and seeks the target, reads the stage bit under the
head, and comes back: restore the target from the save, reset, seek home.

The sites: two `DescriptiveComplexity.Pfp.CopyKit` trips (save and
restore), a `DescriptiveComplexity.Pfp.ClearKit` trip (the target's blocks
not written by any loop), the per-argument
`DescriptiveComplexity.Pfp.tupleRule` loops chained head to tail, two
`DescriptiveComplexity.Pfp.ResetKit`+`ClearKit` pairs with their erasing
entry checkpoints, and two `DescriptiveComplexity.Pfp.SeekKit` instances –
the first's verdict exits are the **read under the head**, branching on the
stage track's digit at the sought cell and storing it into the control.

As everywhere in the assembly, the semantic parameters – the loop-variable
updates, the stored-bit updates, the verdict store – are `dstSt`/guard
parameters; the shapes and their separation are what this file fixes.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The phases of a stage atom's machinery.** -/
inductive StagePh (k : ℕ) : Type
  /-- Saving the mirror. -/
  | savP : TrackPh → StagePh k
  /-- Clearing the target. -/
  | clrP : TrackPh → StagePh k
  /-- The `ℓ`-th argument's tuple loop. -/
  | tupP : Fin k → ChainPh 3 TuplePS → StagePh k
  /-- The checkpoint entering the first reset. -/
  | cR1 : StagePh k
  /-- The first reset. -/
  | rst1P : ResetPh → StagePh k
  /-- Clearing the mirror before the seek out. -/
  | cm1P : TrackPh → StagePh k
  /-- The seek to the target. -/
  | skP : SeekPh → StagePh k
  /-- Restoring the target from the save. -/
  | resP : TrackPh → StagePh k
  /-- The checkpoint entering the second reset. -/
  | cR2 : StagePh k
  /-- The second reset. -/
  | rst2P : ResetPh → StagePh k
  /-- Clearing the mirror before the seek home. -/
  | cm2P : TrackPh → StagePh k
  /-- The seek home. -/
  | sk2P : SeekPh → StagePh k

/-- **The sites of a stage atom's machinery.** -/
inductive StageSite (k : ℕ) : Type
  /-- The mirror save. -/
  | sav : StageSite k
  /-- The target clear. -/
  | clr : StageSite k
  /-- An argument's tuple loop. -/
  | tup : Fin k → ChainSite 3 TupleSS → StageSite k
  /-- The first reset's entry checkpoint. -/
  | cR1 : StageSite k
  /-- The first reset. -/
  | rst1 : StageSite k
  /-- The first mirror clear. -/
  | cm1 : StageSite k
  /-- The seek to the target. -/
  | sk : StageSite k
  /-- The target restore. -/
  | res : StageSite k
  /-- The second reset's entry checkpoint. -/
  | cR2 : StageSite k
  /-- The second reset. -/
  | rst2 : StageSite k
  /-- The second mirror clear. -/
  | cm2 : StageSite k
  /-- The seek home. -/
  | sk2 : StageSite k

/-- **The rule shape of each site.** -/
def StageSh (k : ℕ) : StageSite k → Type
  | .sav => TrackRule ⊕ Unit
  | .clr => TrackRule ⊕ Unit
  | .tup _ c => ChainSh 3 TupleSS TupleSh c
  | .cR1 => EvalChkRule
  | .rst1 => ResetRule ⊕ Unit
  | .cm1 => TrackRule ⊕ Unit
  | .sk => SeekRule ⊕ Bool
  | .res => TrackRule ⊕ Unit
  | .cR2 => EvalChkRule
  | .rst2 => ResetRule ⊕ Unit
  | .cm2 => TrackRule ⊕ Unit
  | .sk2 => SeekRule ⊕ Unit

/-- **The owner of each phase of a stage atom's machinery.** -/
def stageOwn {k : ℕ} : StagePh k → StageSite k
  | .savP _ => .sav
  | .clrP _ => .clr
  | .tupP ℓ c => .tup ℓ (tupleOwn c)
  | .cR1 => .cR1
  | .rst1P _ => .rst1
  | .cm1P _ => .cm1
  | .skP _ => .sk
  | .resP _ => .res
  | .cR2 => .cR2
  | .rst2P _ => .rst2
  | .cm2P _ => .cm2
  | .sk2P _ => .sk2

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A Q P : Type} {k : ℕ}
variable (zero one : A)

section Rules

variable (emb : StagePh k → P)
variable (srcTrack : Fin k → dt.SlotIx)
variable (srcBlk dstBlk : Fin k → Fin dt.ko ⊕ Fin dt.ki)
variable (coord : Fin dt.dd0 → Q)
variable (bitFlag : (Q → A) → Prop)
variable (setBit : Bool → (Q → A) → (dt.SlotIx → A) → (Q → A))
variable (initLv advLv : (Q → A) → (dt.SlotIx → A) → (Q → A))
variable (IsMaxLv : (Q → A) → Prop)
variable (oldSlot : dt.SlotIx)
variable (setAv : Bool → (Q → A) → (dt.SlotIx → A) → (Q → A))
variable (exitPh : P)

/-- The phase entering the loops, or the first reset checkpoint when there
is no argument. -/
def stageFirstTup : P :=
  if h : 0 < k then emb (.tupP ⟨0, h⟩ (.chk 0)) else emb .cR1

/-- The phase after the `ℓ`-th loop. -/
def stageNextTup (ℓ : Fin k) : P :=
  if h : (ℓ : ℕ) + 1 < k then emb (.tupP ⟨(ℓ : ℕ) + 1, h⟩ (.chk 0))
  else emb .cR1

/-- **The rules of a stage atom's machinery.** -/
noncomputable def stageRule :
    ∀ i : StageSite k, StageSh k i → Rule A Q dt.SlotIx P
  | .sav, Sum.inl ρ =>
    (CopyKit.mk (A := A) (Q := Q) Slot.sav Slot.mir Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.savP t))).rule one ρ
  | .sav, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.savP .run)
      dstPh := emb (.clrP .up)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .clr, Sum.inl ρ =>
    (ClearKit.mk (A := A) (Q := Q) Slot.tgt Slot.reg Slot.regLast Slot.wk
      (fun t => emb (.clrP t))).rule zero one ρ
  | .clr, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.clrP .run)
      dstPh := stageFirstTup emb
      dstSt := initLv
      wr := fun _ g => g
      moveRight := True }
  | .tup ℓ c, ρ =>
    tupleRule zero one Slot.wk Slot.reg (fun p => emb (.tupP ℓ p))
      (srcTrack ℓ) Slot.tgt
      (dt.nameG one (srcBlk ℓ) coord) (dt.nameG one (dstBlk ℓ) coord)
      bitFlag setBit initLv advLv IsMaxLv (stageNextTup emb ℓ) c ρ
  | .cR1, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .cR1
      dstPh := emb .cR1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .cR1, .dspA =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb .cR1
      dstPh := emb (.rst1P .scan)
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g Slot.wk zero
      moveRight := True }
  | .cR1, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .cR1
      dstPh := emb .cR1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .rst1, Sum.inl ρ =>
    (ResetKit.mk (A := A) (Q := Q) Slot.mir Slot.bot Slot.wk
      (fun t => emb (.rst1P t))).rule one ρ
  | .rst1, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.rst1P .done)
      dstPh := emb (.cm1P .up)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .cm1, Sum.inl ρ =>
    (ClearKit.mk (A := A) (Q := Q) Slot.mir Slot.reg Slot.regLast Slot.wk
      (fun t => emb (.cm1P t))).rule zero one ρ
  | .cm1, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.cm1P .run)
      dstPh := emb (.skP .chk)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .sk, Sum.inl ρ =>
    (SeekKit.mk (A := A) (Q := Q) Slot.mir Slot.tgt Slot.reg Slot.regLast
      Slot.wk (fun p => emb (.skP p))).rule zero one ρ
  | .sk, Sum.inr b =>
    { guard := fun _ g => dt.exitG one g ∧ (g oldSlot = one ↔ b = true)
      srcPh := emb (.skP .ty)
      dstPh := emb (.resP .up)
      dstSt := setAv b
      wr := fun _ g => g
      moveRight := True }
  | .res, Sum.inl ρ =>
    (CopyKit.mk (A := A) (Q := Q) Slot.tgt Slot.sav Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.resP t))).rule one ρ
  | .res, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.resP .run)
      dstPh := emb .cR2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .cR2, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .cR2
      dstPh := emb .cR2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .cR2, .dspA =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb .cR2
      dstPh := emb (.rst2P .scan)
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g Slot.wk zero
      moveRight := True }
  | .cR2, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .cR2
      dstPh := emb .cR2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .rst2, Sum.inl ρ =>
    (ResetKit.mk (A := A) (Q := Q) Slot.mir Slot.bot Slot.wk
      (fun t => emb (.rst2P t))).rule one ρ
  | .rst2, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.rst2P .done)
      dstPh := emb (.cm2P .up)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .cm2, Sum.inl ρ =>
    (ClearKit.mk (A := A) (Q := Q) Slot.mir Slot.reg Slot.regLast Slot.wk
      (fun t => emb (.cm2P t))).rule zero one ρ
  | .cm2, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.cm2P .run)
      dstPh := emb (.sk2P .chk)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .sk2, Sum.inl ρ =>
    (SeekKit.mk (A := A) (Q := Q) Slot.mir Slot.tgt Slot.reg Slot.regLast
      Slot.wk (fun p => emb (.sk2P p))).rule zero one ρ
  | .sk2, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.sk2P .ty)
      dstPh := exitPh
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }

variable {emb}

/-- **Every rule of a stage atom's machinery fires from a phase its site
owns**; the tuple loops' obligation is their own. -/
theorem stageHosrc :
    ∀ (i : StageSite k) (ρ : StageSh k i),
      ∃ p : StagePh k,
        (dt.stageRule zero one emb srcTrack srcBlk dstBlk coord bitFlag setBit
          initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).srcPh = emb p ∧
          stageOwn p = i := by
  intro i ρ
  match i, ρ with
  | .sav, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .sav, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .clr, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .clr, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .tup ℓ c, ρ =>
    obtain ⟨p, hp, ho⟩ :=
      tupleHosrc zero one Slot.wk Slot.reg (srcTrack ℓ) Slot.tgt
        (dt.nameG one (srcBlk ℓ) coord) (dt.nameG one (dstBlk ℓ) coord)
        bitFlag setBit initLv advLv IsMaxLv (stageNextTup emb ℓ)
        (emb := fun p => emb (.tupP ℓ p)) c ρ
    exact ⟨.tupP ℓ p, hp, congrArg (StageSite.tup ℓ) ho⟩
  | .cR1, .stay => exact ⟨_, rfl, rfl⟩
  | .cR1, .dspA => exact ⟨_, rfl, rfl⟩
  | .cR1, .dspB => exact ⟨_, rfl, rfl⟩
  | .rst1, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .rst1, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .cm1, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .cm1, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .sk, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .sk, Sum.inr b => exact ⟨_, rfl, rfl⟩
  | .res, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .res, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .cR2, .stay => exact ⟨_, rfl, rfl⟩
  | .cR2, .dspA => exact ⟨_, rfl, rfl⟩
  | .cR2, .dspB => exact ⟨_, rfl, rfl⟩
  | .rst2, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .rst2, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .cm2, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .cm2, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .sk2, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .sk2, Sum.inr _ => exact ⟨_, rfl, rfl⟩

variable (hzo : zero ≠ one) (hemb : Function.Injective emb)

include hzo hemb in
/-- **A stage atom's machinery separates in-shape.** -/
theorem stageSep :
    ∀ (i : StageSite k) (ρ ρ' : StageSh k i) (f : Q → A) (g : dt.SlotIx → A),
      (dt.stageRule zero one emb srcTrack srcBlk dstBlk coord bitFlag setBit
        initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).guard f g →
      (dt.stageRule zero one emb srcTrack srcBlk dstBlk coord bitFlag setBit
        initLv advLv IsMaxLv oldSlot setAv exitPh i ρ').guard f g →
      (dt.stageRule zero one emb srcTrack srcBlk dstBlk coord bitFlag setBit
        initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).srcPh =
        (dt.stageRule zero one emb srcTrack srcBlk dstBlk coord bitFlag setBit
          initLv advLv IsMaxLv oldSlot setAv exitPh i ρ').srcPh →
      ρ = ρ' := by
  have hsav : Function.Injective (fun t => emb (.savP t) : TrackPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hclr : Function.Injective (fun t => emb (.clrP t) : TrackPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hres : Function.Injective (fun t => emb (.resP t) : TrackPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hcm1 : Function.Injective (fun t => emb (.cm1P t) : TrackPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hcm2 : Function.Injective (fun t => emb (.cm2P t) : TrackPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hr1 : Function.Injective (fun t => emb (.rst1P t) : ResetPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hr2 : Function.Injective (fun t => emb (.rst2P t) : ResetPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hsk : Function.Injective (fun p => emb (.skP p) : SeekPh → P) :=
    fun x y h => by cases hemb h; rfl
  have hsk2 : Function.Injective (fun p => emb (.sk2P p) : SeekPh → P) :=
    fun x y h => by cases hemb h; rfl
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .sav, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (CopyKit.sep _ one hsav σ σ' f g hg hg' hph)
  | .sav, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      CopyKit.exit_disjoint _ one hsav σ f g hg hg'.1 hg'.2 hp)
  | .sav, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      CopyKit.exit_disjoint _ one hsav σ f g hg' hg.1 hg.2 hp)
  | .sav, Sum.inr _, Sum.inr _ => rfl
  | .clr, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hclr σ σ' f g hg hg' hph)
  | .clr, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hclr σ f g hg hg'.1 hg'.2 hp)
  | .clr, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hclr σ f g hg' hg.1 hg.2 hp)
  | .clr, Sum.inr _, Sum.inr _ => rfl
  | .tup ℓ c, ρ, ρ' =>
    exact tupleSep zero one Slot.wk Slot.reg (srcTrack ℓ) Slot.tgt
      (dt.nameG one (srcBlk ℓ) coord) (dt.nameG one (dstBlk ℓ) coord)
      bitFlag setBit initLv advLv IsMaxLv (stageNextTup emb ℓ)
      (fun x y h => by cases hemb h; rfl) c ρ ρ' f g hg hg' hph
  | .cR1, .stay, .stay => rfl
  | .cR1, .dspA, .dspA => rfl
  | .cR1, .dspB, .dspB => rfl
  | .cR1, .stay, .dspA => exact absurd hg'.1 hg
  | .cR1, .dspA, .stay => exact absurd hg.1 hg'
  | .cR1, .stay, .dspB => exact hg'.elim
  | .cR1, .dspB, .stay => exact hg.elim
  | .cR1, .dspA, .dspB => exact hg'.elim
  | .cR1, .dspB, .dspA => exact hg.elim
  | .rst1, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ResetKit.sep _ one hr1 σ σ' f g hg hg' hph)
  | .rst1, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp => ResetKit.exit_disjoint _ one hr1 σ f g hg hp)
  | .rst1, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ResetKit.exit_disjoint _ one hr1 σ f g hg' hp)
  | .rst1, Sum.inr _, Sum.inr _ => rfl
  | .cm1, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hcm1 σ σ' f g hg hg' hph)
  | .cm1, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hcm1 σ f g hg hg'.1 hg'.2 hp)
  | .cm1, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hcm1 σ f g hg' hg.1 hg.2 hp)
  | .cm1, Sum.inr _, Sum.inr _ => rfl
  | .sk, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (SeekKit.sep _ zero one hzo hsk σ σ' f g hg hg' hph)
  | .sk, Sum.inl σ, Sum.inr b =>
    exact absurd hph (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk σ f g hg hg'.1.1 hg'.1.2 hp)
  | .sk, Sum.inr b, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk σ f g hg' hg.1.1 hg.1.2 hp)
  | .sk, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hg.2.symm.trans hg'.2
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .res, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (CopyKit.sep _ one hres σ σ' f g hg hg' hph)
  | .res, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      CopyKit.exit_disjoint _ one hres σ f g hg hg'.1 hg'.2 hp)
  | .res, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      CopyKit.exit_disjoint _ one hres σ f g hg' hg.1 hg.2 hp)
  | .res, Sum.inr _, Sum.inr _ => rfl
  | .cR2, .stay, .stay => rfl
  | .cR2, .dspA, .dspA => rfl
  | .cR2, .dspB, .dspB => rfl
  | .cR2, .stay, .dspA => exact absurd hg'.1 hg
  | .cR2, .dspA, .stay => exact absurd hg.1 hg'
  | .cR2, .stay, .dspB => exact hg'.elim
  | .cR2, .dspB, .stay => exact hg.elim
  | .cR2, .dspA, .dspB => exact hg'.elim
  | .cR2, .dspB, .dspA => exact hg.elim
  | .rst2, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ResetKit.sep _ one hr2 σ σ' f g hg hg' hph)
  | .rst2, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp => ResetKit.exit_disjoint _ one hr2 σ f g hg hp)
  | .rst2, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ResetKit.exit_disjoint _ one hr2 σ f g hg' hp)
  | .rst2, Sum.inr _, Sum.inr _ => rfl
  | .cm2, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hcm2 σ σ' f g hg hg' hph)
  | .cm2, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hcm2 σ f g hg hg'.1 hg'.2 hp)
  | .cm2, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hcm2 σ f g hg' hg.1 hg.2 hp)
  | .cm2, Sum.inr _, Sum.inr _ => rfl
  | .sk2, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (SeekKit.sep _ zero one hzo hsk2 σ σ' f g hg hg' hph)
  | .sk2, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk2 σ f g hg hg'.1 hg'.2 hp)
  | .sk2, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      SeekKit.exit_disjoint _ zero one hsk2 σ f g hg' hg.1 hg.2 hp)
  | .sk2, Sum.inr _, Sum.inr _ => rfl

end Rules

end PfpData

end Pfp

end DescriptiveComplexity
