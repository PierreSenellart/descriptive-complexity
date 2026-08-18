/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawEval

/-!
# One variable's machinery: gates, the VAL loop, the stage write

The spine of the per-variable evaluation
(`DescriptiveComplexity.Problems.Wide.DrawEval` dispatches into it, once per
variable position): the gates decide whether the working address's outer
blocks encode points – their machinery is abstract here, their verdict a
control flag – the junk path writes `False` into the stage track directly,
and the valid path runs the **VAL loop**: clear the VAL register, evaluate
the matrix at the empty valuation, then rounds of exhaustion test, increment
and matrix until VAL is exhausted, the accumulator folds riding in the
dispatching rules' `dstSt` (separation never reads `dstSt`, so the folds are
*parameters* here – `initSt` at the empty valuation, `storeCarry` at each
increment's block-indexed landing, `postFold` after each matrix pass – and
their content is fixed with the runs, not with the shapes).

Everything is generic over the program's phase type: the spine's phases
embed by a parameter, the gates' and the matrix's machineries come with
their own rules, and the exit – writing the variable's next-stage bit at the
marker off the verdict accumulator – targets a parameter phase. One copy of
this file's shapes per variable position is instantiated at assembly.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The phases of one variable's machinery**: the four checkpoints, the
kit copies, and the two abstract blocks. `B` is the carry-block index of
the VAL increment. -/
inductive VarPh (B PG PX : Type) : Type
  /-- The entry checkpoint: walk to the marker, begin the gates. -/
  | vchk0 : VarPh B PG PX
  /-- A phase of the gates' machinery. -/
  | gatesP : PG → VarPh B PG PX
  /-- After the gates: dispatch on their verdict flag. -/
  | vchk1 : VarPh B PG PX
  /-- Clearing the VAL register. -/
  | clearValP : TrackPh → VarPh B PG PX
  /-- A phase of the matrix's machinery. -/
  | matrixP : PX → VarPh B PG PX
  /-- After a matrix pass: fold and begin the exhaustion test. -/
  | mchk1 : VarPh B PG PX
  /-- The exhaustion test on VAL. -/
  | valTestP : TestPh → VarPh B PG PX
  /-- The increment of VAL, landing per carry block. -/
  | valIncrP : IncrPh B → VarPh B PG PX
  /-- Converged: write the stage bit and leave. -/
  | vchk2 : VarPh B PG PX

/-- **The sites of one variable's machinery.** -/
inductive VarSite (SG SX : Type) : Type
  /-- The entry checkpoint. -/
  | vchk0 : VarSite SG SX
  /-- A gates site. -/
  | gates : SG → VarSite SG SX
  /-- The verdict checkpoint. -/
  | vchk1 : VarSite SG SX
  /-- The VAL clear. -/
  | clearVal : VarSite SG SX
  /-- A matrix site. -/
  | matrix : SX → VarSite SG SX
  /-- The post-matrix checkpoint. -/
  | mchk1 : VarSite SG SX
  /-- The exhaustion test. -/
  | valTest : VarSite SG SX
  /-- The VAL increment. -/
  | valIncr : VarSite SG SX
  /-- The exit checkpoint. -/
  | vchk2 : VarSite SG SX

/-- **The rule shape of each site**: kit rules summed with exits, the
checkpoints' the three-rule gadget of the spine layer. -/
def VarSh (SG SX : Type) (ShG : SG → Type) (ShX : SX → Type) (B : Type) :
    VarSite SG SX → Type
  | .vchk0 => EvalChkRule
  | .gates s => ShG s
  | .vchk1 => EvalChkRule
  | .clearVal => TrackRule ⊕ Unit
  | .matrix s => ShX s
  | .mchk1 => EvalChkRule
  | .valTest => TestRule ⊕ Bool
  | .valIncr => IncrRule B ⊕ B
  | .vchk2 => EvalChkRule

/-- **The owner of each phase of one variable's machinery**, over the gates'
and the matrix's owners. -/
def varOwn {B PG PX SG SX : Type} (ownG : PG → SG) (ownX : PX → SX) :
    VarPh B PG PX → VarSite SG SX
  | .vchk0 => .vchk0
  | .gatesP p => .gates (ownG p)
  | .vchk1 => .vchk1
  | .clearValP _ => .clearVal
  | .matrixP p => .matrix (ownX p)
  | .mchk1 => .mchk1
  | .valTestP _ => .valTest
  | .valIncrP _ => .valIncr
  | .vchk2 => .vchk2

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q P PG PX SG SX : Type}
variable (zero one : A) {ShG : SG → Type} {ShX : SX → Type}

/-- The carry-block index of the VAL increment. -/
abbrev CarryB : Type := Option (Fin dt.ko ⊕ Fin dt.ki)

/-- **The rules of one variable's machinery.** Parameters: the phase
embedding, the two abstract machineries with their entry phases, the exit
phase, the variable's stage slot, the gates' verdict flag, the verdict
accumulator, and the three fold updates. -/
noncomputable def varRule
    (emb : VarPh dt.CarryB PG PX → P)
    (ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P)
    (ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P)
    (pgEntry pxEntry exitPh : P)
    (newSlot : dt.SlotIx) (gateFlag : Q)
    (accBit : (Q → A) → Prop)
    (enterSt initSt postFold : (Q → A) → (dt.SlotIx → A) → Q → A)
    (storeCarry : dt.CarryB → (Q → A) → (dt.SlotIx → A) → Q → A) :
    ∀ i : VarSite SG SX, VarSh SG SX ShG ShX dt.CarryB i → Rule A Q dt.SlotIx P
  | .vchk0, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .vchk0
      dstPh := emb .vchk0
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .vchk0, .dspA =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb .vchk0
      dstPh := pgEntry
      dstSt := enterSt
      wr := fun _ g => g
      moveRight := True }
  | .vchk0, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .vchk0
      dstPh := emb .vchk0
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .gates s, ρ => ruleG s ρ
  | .vchk1, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .vchk1
      dstPh := emb .vchk1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .vchk1, .dspA =>
    { guard := fun f g => dt.exitG one g ∧ f gateFlag = one
      srcPh := emb .vchk1
      dstPh := emb (.clearValP .up)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .vchk1, .dspB =>
    { guard := fun f g => dt.exitG one g ∧ f gateFlag ≠ one
      srcPh := emb .vchk1
      dstPh := exitPh
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g newSlot zero
      moveRight := True }
  | .clearVal, Sum.inl ρ =>
    (ClearKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
      (fun t => emb (.clearValP t))).rule zero one ρ
  | .clearVal, Sum.inr _ =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.clearValP .run)
      dstPh := pxEntry
      dstSt := initSt
      wr := fun _ g => g
      moveRight := True }
  | .matrix s, ρ => ruleX s ρ
  | .mchk1, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .mchk1
      dstPh := emb .mchk1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .mchk1, .dspA =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb .mchk1
      dstPh := emb (.valTestP .up)
      dstSt := postFold
      wr := fun _ g => g
      moveRight := True }
  | .mchk1, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .mchk1
      dstPh := emb .mchk1
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .valTest, Sum.inl ρ =>
    (TestKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
      (fun g => (g Slot.val = one ↔
        ∃ j : Fin dt.ki, g (.blk (some (Sum.inr j))) = one))
      (fun t => emb (.valTestP t))).rule one ρ
  | .valTest, Sum.inr b =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.valTestP (if b then .ty else .tn))
      dstPh := if b then emb .vchk2 else emb (.valIncrP .up)
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .valIncr, Sum.inl ρ =>
    (IncrKit.mk (A := A) (Q := Q) Slot.val Slot.reg Slot.regLast Slot.wk
      (fun b => Slot.blk b) (fun t => emb (.valIncrP t))).rule zero one ρ
  | .valIncr, Sum.inr b =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb (.valIncrP (.pd b))
      dstPh := pxEntry
      dstSt := storeCarry b
      wr := fun _ g => g
      moveRight := True }
  | .vchk2, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .vchk2
      dstPh := emb .vchk2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .vchk2, .dspA =>
    { guard := fun _ g => dt.exitG one g
      srcPh := emb .vchk2
      dstPh := exitPh
      dstSt := fun f _ => f
      wr := fun f g => Function.update g newSlot (bitVal zero one (accBit f))
      moveRight := True }
  | .vchk2, .dspB =>
    { guard := fun _ _ => False
      srcPh := emb .vchk2
      dstPh := emb .vchk2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }

section Hosrc

variable {emb : VarPh dt.CarryB PG PX → P}
variable {ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P}
variable {ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P}
variable (pgEntry pxEntry exitPh : P)
variable (newSlot : dt.SlotIx) (gateFlag : Q)
variable (accBit : (Q → A) → Prop)
variable (enterSt initSt postFold : (Q → A) → (dt.SlotIx → A) → Q → A)
variable (storeCarry : dt.CarryB → (Q → A) → (dt.SlotIx → A) → Q → A)
variable {ownG : PG → SG} {ownX : PX → SX}

/-- **A variable's machinery leaves only into its own phases or its exit**: the
gates' and the matrix's rules are the parameters' business, the three trips stay
inside their own phases, and only the two verdict dispatches leave. -/
theorem varRule_dstPh
    (hdstG : ∀ (s : SG) (ρ : ShG s),
      (∃ p : PG, (ruleG s ρ).dstPh = emb (.gatesP p)) ∨
        (ruleG s ρ).dstPh = emb .vchk1)
    (hdstX : ∀ (s : SX) (ρ : ShX s),
      (∃ p : PX, (ruleX s ρ).dstPh = emb (.matrixP p)) ∨
        (ruleX s ρ).dstPh = emb .mchk1)
    (hpg : ∃ p : PG, pgEntry = emb (.gatesP p))
    (hpx : ∃ p : PX, pxEntry = emb (.matrixP p))
    (i : VarSite SG SX) (ρ : VarSh SG SX ShG ShX dt.CarryB i) :
    (∃ p : VarPh dt.CarryB PG PX,
      (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot gateFlag
        accBit enterSt initSt postFold storeCarry i ρ).dstPh = emb p) ∨
    (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot gateFlag
      accBit enterSt initSt postFold storeCarry i ρ).dstPh = exitPh := by
  match i, ρ with
  | .vchk0, .stay => exact Or.inl ⟨_, rfl⟩
  | .vchk0, .dspA =>
    obtain ⟨p, hp⟩ := hpg
    exact Or.inl ⟨.gatesP p, hp⟩
  | .vchk0, .dspB => exact Or.inl ⟨_, rfl⟩
  | .gates s, ρ =>
    rcases hdstG s ρ with ⟨p, hp⟩ | hp
    · exact Or.inl ⟨.gatesP p, hp⟩
    · exact Or.inl ⟨.vchk1, hp⟩
  | .vchk1, .stay => exact Or.inl ⟨_, rfl⟩
  | .vchk1, .dspA => exact Or.inl ⟨_, rfl⟩
  | .vchk1, .dspB => exact Or.inr rfl
  | .clearVal, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (ClearKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun t => emb (.clearValP t))).dstPh_emb zero
      one ρ'
    exact Or.inl ⟨.clearValP t, ht⟩
  | .clearVal, Sum.inr _ =>
    obtain ⟨p, hp⟩ := hpx
    exact Or.inl ⟨.matrixP p, hp⟩
  | .matrix s, ρ =>
    rcases hdstX s ρ with ⟨p, hp⟩ | hp
    · exact Or.inl ⟨.matrixP p, hp⟩
    · exact Or.inl ⟨.mchk1, hp⟩
  | .mchk1, .stay => exact Or.inl ⟨_, rfl⟩
  | .mchk1, .dspA => exact Or.inl ⟨_, rfl⟩
  | .mchk1, .dspB => exact Or.inl ⟨_, rfl⟩
  | .valTest, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (TestKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun g => (g Slot.val = one ↔
        ∃ j : Fin dt.ki, g (.blk (some (Sum.inr j))) = one))
      (fun t => emb (.valTestP t))).dstPh_emb one ρ'
    exact Or.inl ⟨.valTestP t, ht⟩
  | .valTest, Sum.inr b =>
    cases b with
    | true => exact Or.inl ⟨.vchk2, rfl⟩
    | false => exact Or.inl ⟨.valIncrP .up, rfl⟩
  | .valIncr, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (IncrKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun b => Slot.blk b)
      (fun t => emb (.valIncrP t))).dstPh_emb zero one ρ'
    exact Or.inl ⟨.valIncrP t, ht⟩
  | .valIncr, Sum.inr b =>
    obtain ⟨p, hp⟩ := hpx
    exact Or.inl ⟨.matrixP p, hp⟩
  | .vchk2, .stay => exact Or.inl ⟨_, rfl⟩
  | .vchk2, .dspA => exact Or.inr rfl
  | .vchk2, .dspB => exact Or.inl ⟨_, rfl⟩

/-- **A property of a variable machinery's phases and its exit holds of every
phase it can move to**, given it holds of the gates' and the matrix's. -/
theorem varRule_dstIn {S : P → Prop} (hemb : ∀ p : VarPh dt.CarryB PG PX, S (emb p))
    (hexit : S exitPh)
    (hG : ∀ (s : SG) (ρ : ShG s), S (ruleG s ρ).dstPh)
    (hX : ∀ (s : SX) (ρ : ShX s), S (ruleX s ρ).dstPh)
    (hpg : S pgEntry) (hpx : S pxEntry)
    (i : VarSite SG SX) (ρ : VarSh SG SX ShG ShX dt.CarryB i) :
    S (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot gateFlag
      accBit enterSt initSt postFold storeCarry i ρ).dstPh := by
  match i, ρ with
  | .vchk0, .stay => exact hemb _
  | .vchk0, .dspA => exact hpg
  | .vchk0, .dspB => exact hemb _
  | .gates s, ρ => exact hG s ρ
  | .vchk1, .stay => exact hemb _
  | .vchk1, .dspA => exact hemb _
  | .vchk1, .dspB => exact hexit
  | .clearVal, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (ClearKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun t => emb (.clearValP t))).dstPh_emb zero
      one ρ'
    rw [show (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry .clearVal
        (Sum.inl ρ')).dstPh = _ from ht]
    exact hemb _
  | .clearVal, Sum.inr _ => exact hpx
  | .matrix s, ρ => exact hX s ρ
  | .mchk1, .stay => exact hemb _
  | .mchk1, .dspA => exact hemb _
  | .mchk1, .dspB => exact hemb _
  | .valTest, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (TestKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun g => (g Slot.val = one ↔
        ∃ j : Fin dt.ki, g (.blk (some (Sum.inr j))) = one))
      (fun t => emb (.valTestP t))).dstPh_emb one ρ'
    rw [show (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry .valTest
        (Sum.inl ρ')).dstPh = _ from ht]
    exact hemb _
  | .valTest, Sum.inr b =>
    cases b with
    | true => exact hemb .vchk2
    | false => exact hemb (.valIncrP .up)
  | .valIncr, Sum.inl ρ' =>
    obtain ⟨t, ht⟩ := (IncrKit.mk (A := A) (Q := Q) (W := dt.SlotIx) Slot.val
      Slot.reg Slot.regLast Slot.wk (fun b => Slot.blk b)
      (fun t => emb (.valIncrP t))).dstPh_emb zero one ρ'
    rw [show (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry .valIncr
        (Sum.inl ρ')).dstPh = _ from ht]
    exact hemb _
  | .valIncr, Sum.inr b => exact hpx
  | .vchk2, .stay => exact hemb _
  | .vchk2, .dspA => exact hexit
  | .vchk2, .dspB => exact hemb _

/-- **Every rule of one variable's machinery fires from a phase its site
owns**; the two abstract machineries' obligations are parameters. -/
theorem varHosrc
    (hosrcG : ∀ (s : SG) (ρ : ShG s),
      ∃ p : PG, (ruleG s ρ).srcPh = emb (.gatesP p) ∧ ownG p = s)
    (hosrcX : ∀ (s : SX) (ρ : ShX s),
      ∃ p : PX, (ruleX s ρ).srcPh = emb (.matrixP p) ∧ ownX p = s) :
    ∀ (i : VarSite SG SX) (ρ : VarSh SG SX ShG ShX dt.CarryB i),
      ∃ p : VarPh dt.CarryB PG PX,
        (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
          gateFlag accBit enterSt initSt postFold storeCarry i ρ).srcPh = emb p ∧
          varOwn ownG ownX p = i := by
  intro i ρ
  match i, ρ with
  | .vchk0, .stay => exact ⟨_, rfl, rfl⟩
  | .vchk0, .dspA => exact ⟨_, rfl, rfl⟩
  | .vchk0, .dspB => exact ⟨_, rfl, rfl⟩
  | .gates s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcG s ρ
    exact ⟨.gatesP p, hp, congrArg VarSite.gates ho⟩
  | .vchk1, .stay => exact ⟨_, rfl, rfl⟩
  | .vchk1, .dspA => exact ⟨_, rfl, rfl⟩
  | .vchk1, .dspB => exact ⟨_, rfl, rfl⟩
  | .clearVal, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .clearVal, Sum.inr _ => exact ⟨_, rfl, rfl⟩
  | .matrix s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcX s ρ
    exact ⟨.matrixP p, hp, congrArg VarSite.matrix ho⟩
  | .mchk1, .stay => exact ⟨_, rfl, rfl⟩
  | .mchk1, .dspA => exact ⟨_, rfl, rfl⟩
  | .mchk1, .dspB => exact ⟨_, rfl, rfl⟩
  | .valTest, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .valTest, Sum.inr b => cases b <;> exact ⟨_, rfl, rfl⟩
  | .valIncr, Sum.inl σ => cases σ <;> exact ⟨_, rfl, rfl⟩
  | .valIncr, Sum.inr b => exact ⟨_, rfl, rfl⟩
  | .vchk2, .stay => exact ⟨_, rfl, rfl⟩
  | .vchk2, .dspA => exact ⟨_, rfl, rfl⟩
  | .vchk2, .dspB => exact ⟨_, rfl, rfl⟩

end Hosrc

section Sep

variable (hzo : zero ≠ one)
variable {emb : VarPh dt.CarryB PG PX → P} (hemb : Function.Injective emb)
variable {ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P}
variable {ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P}
variable {pgEntry pxEntry exitPh : P}
variable {newSlot : dt.SlotIx} {gateFlag : Q}
variable {accBit : (Q → A) → Prop}
variable {enterSt initSt postFold : (Q → A) → (dt.SlotIx → A) → Q → A}
variable {storeCarry : dt.CarryB → (Q → A) → (dt.SlotIx → A) → Q → A}

include hzo hemb in
/-- **One variable's machinery separates in-shape**: the checkpoints by
their guards, the kits by their `sep` and `exit_disjoint`, the exit pairs by
the phases the embedding keeps apart; the two abstract machineries by their
parameters. -/
theorem varSep
    (hsepG : ∀ (s : SG) (ρ ρ' : ShG s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleG s ρ).guard f g → (ruleG s ρ').guard f g →
      (ruleG s ρ).srcPh = (ruleG s ρ').srcPh → ρ = ρ')
    (hsepX : ∀ (s : SX) (ρ ρ' : ShX s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleX s ρ).guard f g → (ruleX s ρ').guard f g →
      (ruleX s ρ).srcPh = (ruleX s ρ').srcPh → ρ = ρ') :
    ∀ (i : VarSite SG SX) (ρ ρ' : VarSh SG SX ShG ShX dt.CarryB i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry i ρ).guard f g →
      (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry i ρ').guard f g →
      (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
        gateFlag accBit enterSt initSt postFold storeCarry i ρ).srcPh =
        (dt.varRule zero one emb ruleG ruleX pgEntry pxEntry exitPh newSlot
          gateFlag accBit enterSt initSt postFold storeCarry i ρ').srcPh →
      ρ = ρ' := by
  have hclr : Function.Injective (fun t => emb (.clearValP t)) :=
    fun x y h => by cases hemb h; rfl
  have htst : Function.Injective (fun t => emb (.valTestP t)) :=
    fun x y h => by cases hemb h; rfl
  have hinc : Function.Injective (fun t => emb (.valIncrP t)) :=
    fun x y h => by cases hemb h; rfl
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .vchk0, .stay, .stay => rfl
  | .vchk0, .dspA, .dspA => rfl
  | .vchk0, .dspB, .dspB => rfl
  | .vchk0, .stay, .dspA => exact absurd hg'.1 hg
  | .vchk0, .dspA, .stay => exact absurd hg.1 hg'
  | .vchk0, .stay, .dspB => exact hg'.elim
  | .vchk0, .dspB, .stay => exact hg.elim
  | .vchk0, .dspA, .dspB => exact hg'.elim
  | .vchk0, .dspB, .dspA => exact hg.elim
  | .gates s, ρ, ρ' => exact hsepG s ρ ρ' f g hg hg' hph
  | .vchk1, .stay, .stay => rfl
  | .vchk1, .dspA, .dspA => rfl
  | .vchk1, .dspB, .dspB => rfl
  | .vchk1, .stay, .dspA => exact absurd hg'.1.1 hg
  | .vchk1, .dspA, .stay => exact absurd hg.1.1 hg'
  | .vchk1, .stay, .dspB => exact absurd hg'.1.1 hg
  | .vchk1, .dspB, .stay => exact absurd hg.1.1 hg'
  | .vchk1, .dspA, .dspB => exact absurd hg.2 hg'.2
  | .vchk1, .dspB, .dspA => exact absurd hg'.2 hg.2
  | .clearVal, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (ClearKit.sep _ zero one hclr σ σ' f g hg hg' hph)
  | .clearVal, Sum.inl σ, Sum.inr _ =>
    exact absurd hph (fun hp =>
      ClearKit.exit_disjoint _ zero one hclr σ f g hg hg'.1 hg'.2 hp)
  | .clearVal, Sum.inr _, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      ClearKit.exit_disjoint _ zero one hclr σ f g hg' hg.1 hg.2 hp)
  | .clearVal, Sum.inr _, Sum.inr _ => rfl
  | .matrix s, ρ, ρ' => exact hsepX s ρ ρ' f g hg hg' hph
  | .mchk1, .stay, .stay => rfl
  | .mchk1, .dspA, .dspA => rfl
  | .mchk1, .dspB, .dspB => rfl
  | .mchk1, .stay, .dspA => exact absurd hg'.1 hg
  | .mchk1, .dspA, .stay => exact absurd hg.1 hg'
  | .mchk1, .stay, .dspB => exact hg'.elim
  | .mchk1, .dspB, .stay => exact hg.elim
  | .mchk1, .dspA, .dspB => exact hg'.elim
  | .mchk1, .dspB, .dspA => exact hg.elim
  | .valTest, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (TestKit.sep _ one htst σ σ' f g hg hg' hph)
  | .valTest, Sum.inl σ, Sum.inr b =>
    refine absurd hph (fun hp => TestKit.exit_disjoint _ one htst σ f g hg
      hg'.1 hg'.2 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .valTest, Sum.inr b, Sum.inl σ =>
    refine absurd hph.symm (fun hp => TestKit.exit_disjoint _ one htst σ f g hg'
      hg.1 hg.2 ?_)
    cases b
    · exact Or.inr hp
    · exact Or.inl hp
  | .valTest, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hemb hph
      injection h2 with h3
      cases b <;> cases b' <;> simp_all
    rw [hbb]
  | .valIncr, Sum.inl σ, Sum.inl σ' =>
    exact congrArg Sum.inl (IncrKit.sep _ zero one hzo hinc σ σ' f g hg hg' hph)
  | .valIncr, Sum.inl σ, Sum.inr b =>
    exact absurd hph (fun hp =>
      IncrKit.exit_disjoint _ zero one hinc σ f g b hg hg'.1 hg'.2 hp)
  | .valIncr, Sum.inr b, Sum.inl σ =>
    exact absurd hph.symm (fun hp =>
      IncrKit.exit_disjoint _ zero one hinc σ f g b hg' hg.1 hg.2 hp)
  | .valIncr, Sum.inr b, Sum.inr b' =>
    have hbb : b = b' := by
      have h2 := hemb hph
      injection h2 with h3
      injection h3 with h4
    rw [hbb]
  | .vchk2, .stay, .stay => rfl
  | .vchk2, .dspA, .dspA => rfl
  | .vchk2, .dspB, .dspB => rfl
  | .vchk2, .stay, .dspA => exact absurd hg'.1 hg
  | .vchk2, .dspA, .stay => exact absurd hg.1 hg'
  | .vchk2, .stay, .dspB => exact hg'.elim
  | .vchk2, .dspB, .stay => exact hg.elim
  | .vchk2, .dspA, .dspB => exact hg'.elim
  | .vchk2, .dspB, .dspA => exact hg.elim

end Sep

end Data

end Draw

end DescriptiveComplexity
