/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawOuter
import DescriptiveComplexity.Problems.Wide.DrawEval

/-!
# One round of the VAL loop: inner gates, branch, matrix

The leaf the VAL loop folds is the **gated** matrix
(`DescriptiveComplexity.Draw.Data.leafP`): every ∃-level of the register
must hold an encoding, and only if every ∀-level does is the matrix read.
The machinery of a round therefore runs, before the matrix pass, one gate
block per quantified level of the variable's pack – at the `Sum.inr` blocks
of the VAL register – conjoining each level's verdict into one of two flags
by the level's polarity, and a branch checkpoint then either enters the
matrix (both flags set: every block the atoms read is an encoding, which is
what their semantic packs require) or skips it. The stale verdict slots a
skip leaves behind are harmless: the leaf is
`exist ∧ (all → matrix)`, decided by the flags alone whenever the matrix
did not run.

This composite is slotted into the **matrix parameter** of
`DescriptiveComplexity.Draw.Data.varRule` – which is generic in its `PX`/`SX`
types and enters them only through `pxEntry` – so the variable machinery,
its run theorem and everything above them are untouched.

Shapes only; the runs are the instantiation files'.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The shapes -/

/-- **The phases of one round's machinery**: the inner gates, the branch
checkpoint, and the matrix. -/
inductive RoundPh (PG PX : Type) : Type
  /-- A phase of the inner gates. -/
  | igP : PG → RoundPh PG PX
  /-- The branch checkpoint: dispatch on the two gate flags. -/
  | rchk : RoundPh PG PX
  /-- A phase of the matrix. -/
  | matP : PX → RoundPh PG PX

instance {PG PX : Type} [Finite PG] [Finite PX] : Finite (RoundPh PG PX) :=
  Finite.of_injective
    (fun p => match p with
      | .igP p => (Sum.inl p : PG ⊕ Unit ⊕ PX)
      | .rchk => Sum.inr (Sum.inl ())
      | .matP p => Sum.inr (Sum.inr p))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The sites of one round's machinery.** -/
inductive RoundSite (SG SX : Type) : Type
  /-- An inner-gates site. -/
  | ig : SG → RoundSite SG SX
  /-- The branch checkpoint. -/
  | rchk : RoundSite SG SX
  /-- A matrix site. -/
  | mat : SX → RoundSite SG SX

instance {SG SX : Type} [Finite SG] [Finite SX] : Finite (RoundSite SG SX) :=
  Finite.of_injective
    (fun p => match p with
      | .ig s => (Sum.inl s : SG ⊕ Unit ⊕ SX)
      | .rchk => Sum.inr (Sum.inl ())
      | .mat s => Sum.inr (Sum.inr s))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- **The rule shape of each site**: the checkpoint's the three-rule gadget
of the spine layer. -/
def RoundSh (SG SX : Type) (ShG : SG → Type) (ShX : SX → Type) :
    RoundSite SG SX → Type
  | .ig s => ShG s
  | .rchk => EvalChkRule
  | .mat s => ShX s

/-- **The owner of each phase**, over the sub-machineries' owners. -/
def roundOwn {PG PX SG SX : Type} (ownG : PG → SG) (ownX : PX → SX) :
    RoundPh PG PX → RoundSite SG SX
  | .igP p => .ig (ownG p)
  | .rchk => .rchk
  | .matP p => .mat (ownX p)

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q P PG PX SG SX : Type}
variable (zero one : A) {ShG : SG → Type} {ShX : SX → Type}

/-- **The rules of one round's machinery.** Parameters: the phase
embedding, the two sub-machineries, the matrix's entry, the exit phase
(the variable's post-matrix checkpoint – reached through the matrix or by
the skip), and the two gate flags. -/
noncomputable def roundRule
    (emb : RoundPh PG PX → P)
    (ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P)
    (ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P)
    (pxEntry exitPh : P) (existFlag allFlag : Q) :
    ∀ i : RoundSite SG SX, RoundSh SG SX ShG ShX i → Rule A Q dt.SlotIx P
  | .ig s, ρ => ruleG s ρ
  | .rchk, .stay =>
    { guard := fun _ g => g Slot.wk ≠ one
      srcPh := emb .rchk
      dstPh := emb .rchk
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .rchk, .dspA =>
    { guard := fun f g => dt.exitG one g ∧
        (f existFlag = one ∧ f allFlag = one)
      srcPh := emb .rchk
      dstPh := pxEntry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .rchk, .dspB =>
    { guard := fun f g => dt.exitG one g ∧
        ¬(f existFlag = one ∧ f allFlag = one)
      srcPh := emb .rchk
      dstPh := exitPh
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .mat s, ρ => ruleX s ρ

section Hosrc

variable {emb : RoundPh PG PX → P}
variable {ruleG : ∀ s : SG, ShG s → Rule A Q dt.SlotIx P}
variable {ruleX : ∀ s : SX, ShX s → Rule A Q dt.SlotIx P}
variable (pxEntry exitPh : P) (existFlag allFlag : Q)
variable {ownG : PG → SG} {ownX : PX → SX}

/-- **A property of a round's phases and its exit holds of every phase it can
move to**, given it holds of the two sub-machineries'. -/
theorem roundRule_dstIn {S : P → Prop} (hemb : ∀ p : RoundPh PG PX, S (emb p))
    (hexit : S exitPh)
    (hG : ∀ (s : SG) (ρ : ShG s), S (ruleG s ρ).dstPh)
    (hX : ∀ (s : SX) (ρ : ShX s), S (ruleX s ρ).dstPh)
    (hpx : S pxEntry)
    (i : RoundSite SG SX) (ρ : RoundSh SG SX ShG ShX i) :
    S (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag allFlag
      i ρ).dstPh := by
  match i, ρ with
  | .ig s, ρ => exact hG s ρ
  | .rchk, .stay => exact hemb _
  | .rchk, .dspA => exact hpx
  | .rchk, .dspB => exact hexit
  | .mat s, ρ => exact hX s ρ

/-- **Every rule of one round's machinery fires from a phase its site
owns**; the two sub-machineries' obligations are parameters. -/
theorem roundHosrc
    (hosrcG : ∀ (s : SG) (ρ : ShG s),
      ∃ p : PG, (ruleG s ρ).srcPh = emb (.igP p) ∧ ownG p = s)
    (hosrcX : ∀ (s : SX) (ρ : ShX s),
      ∃ p : PX, (ruleX s ρ).srcPh = emb (.matP p) ∧ ownX p = s) :
    ∀ (i : RoundSite SG SX) (ρ : RoundSh SG SX ShG ShX i),
      ∃ p : RoundPh PG PX,
        (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag
          allFlag i ρ).srcPh = emb p ∧ roundOwn ownG ownX p = i := by
  intro i ρ
  match i, ρ with
  | .ig s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcG s ρ
    exact ⟨.igP p, hp, congrArg RoundSite.ig ho⟩
  | .rchk, .stay => exact ⟨.rchk, rfl, rfl⟩
  | .rchk, .dspA => exact ⟨.rchk, rfl, rfl⟩
  | .rchk, .dspB => exact ⟨.rchk, rfl, rfl⟩
  | .mat s, ρ =>
    obtain ⟨p, hp, ho⟩ := hosrcX s ρ
    exact ⟨.matP p, hp, congrArg RoundSite.mat ho⟩

/-- **One round's machinery separates in-shape**: the sub-machineries by
their own separations, the checkpoint by its guards. -/
theorem roundSep
    (hsepG : ∀ (s : SG) (ρ ρ' : ShG s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleG s ρ).guard f g → (ruleG s ρ').guard f g →
      (ruleG s ρ).srcPh = (ruleG s ρ').srcPh → ρ = ρ')
    (hsepX : ∀ (s : SX) (ρ ρ' : ShX s) (f : Q → A) (g : dt.SlotIx → A),
      (ruleX s ρ).guard f g → (ruleX s ρ').guard f g →
      (ruleX s ρ).srcPh = (ruleX s ρ').srcPh → ρ = ρ') :
    ∀ (i : RoundSite SG SX) (ρ ρ' : RoundSh SG SX ShG ShX i) (f : Q → A)
      (g : dt.SlotIx → A),
      (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag
        allFlag i ρ).guard f g →
      (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag
        allFlag i ρ').guard f g →
      (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag
        allFlag i ρ).srcPh =
        (dt.roundRule one emb ruleG ruleX pxEntry exitPh existFlag
          allFlag i ρ').srcPh →
      ρ = ρ' := by
  intro i ρ ρ' f g hg hg' hph
  match i, ρ, ρ' with
  | .ig s, ρ, ρ' => exact hsepG s ρ ρ' f g hg hg' hph
  | .mat s, ρ, ρ' => exact hsepX s ρ ρ' f g hg hg' hph
  | .rchk, .stay, .stay => rfl
  | .rchk, .dspA, .dspA => rfl
  | .rchk, .dspB, .dspB => rfl
  | .rchk, .stay, .dspA => exact absurd hg'.1.1 hg
  | .rchk, .dspA, .stay => exact absurd hg.1.1 hg'
  | .rchk, .stay, .dspB => exact absurd hg'.1.1 hg
  | .rchk, .dspB, .stay => exact absurd hg.1.1 hg'
  | .rchk, .dspA, .dspB => exact absurd hg.2 hg'.2
  | .rchk, .dspB, .dspA => exact absurd hg'.2 hg.2

end Hosrc

end Data

end Draw

end DescriptiveComplexity
