/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpIxVar
import DescriptiveComplexity.Problems.Wide.PfpRoundSem

/-!
# The round flags and the pass's pack, at an arbitrary file

`DescriptiveComplexity.Problems.Wide.PfpRoundSem` read at a coarse file: the
flags' semantic readings, the pass they jointly deliver, the valuation and the
semantic pack built from it, and the leaf's two readings.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {I : Type} [Finite I] (F : LaidFile dt A R P I)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section RoundSem

variable (vi : dt.VarIx) (st : TapeSt dt A R P I)
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → I → Prop)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi (dt.ixRoundSt st (mV a)) elt (dt.kindOf vi b))

/-! ### The flags along the VAL loop, without quantified levels -/

variable {vi st mV semOf} in
omit [Finite I] [Finite R] [Finite P] in
/-- **Without quantified levels the two flags are constant along the VAL
loop**: the entry seeded them `True`, the inner-gates thread is empty, and
no fold update writes a flag. -/
theorem ixCtlBit_flag_varFM_of_nIn_zero (hzo : PR.zero ≠ PR.one)
    (hn0 : dt.nIn vi = 0) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (v : Univ A R P dt.KIx dt.dd → Prop) (fG : dt.CtlIx → A) (a : ιV) :
    dt.ctlBit PR.one (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) q := by
  classical
  have hleaf : q ≠ dt.leafC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  induction a using order_induction with
  | hmin z hz =>
    rw [show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG z =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v) from iterOrd_bot hz]
    change dt.ctlBit PR.one
      (dt.setCtl PR.zero PR.one dt.existGateC True
        (dt.setCtl PR.zero PR.one dt.allGateC True
          (dt.initAcc PR.zero PR.one (dt.polOf vi) fG))) q
    rcases hq with rfl | rfl
    · exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
    · refine (ctlBit_setCtl_of_ne (show dt.allGateC ≠ dt.existGateC
          from fun h => by
            injection h with h'
            exact absurd h' (by decide)) _ _).mpr ?_
      exact (ctlBit_setCtl_self hzo _ _ _).mpr trivial
  | hstep w z hwz hnb ih =>
    have hcov := iterOrd_covers
      (init := (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
          (dt.ixRoundSt st (fun _ => False)) v))
      (step := fun a q' =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (dt.ixCarryBlk F (mV a))
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf q' a)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV a)) v))
      hwz hnb
    rw [show dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG z = _ from hcov]
    have hne : ∀ j : Fin dt.naDim, q ≠ dt.accC j := fun j => by
      rcases hq with rfl | rfl <;> exact fun h => nomatch h
    -- the store rides
    have hstore : ∀ (b : Option dt.KIx) (f : dt.CtlIx → A)
        (g : dt.SlotIx → A),
        dt.ctlBit PR.one
          ((dt.varArgsOf PR.zero PR.one vi).storeCarry b f g) q ↔
        dt.ctlBit PR.one f q := by
      intro b f g
      change dt.ctlBit PR.one
        (dt.carryAcc PR.zero PR.one (dt.polOf vi)
          (match b with
            | some (Sum.inr j') => (j' : ℕ)
            | _ => 0) f) q ↔ dt.ctlBit PR.one f q
      rw [carryAcc]
      exact iff_of_eq (congrArg (· = PR.one) (putAcc_of_not_acc hne))
    rw [hstore]
    -- the fold rides
    have hfold : ∀ f : dt.CtlIx → A,
        dt.ctlBit PR.one
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf f w)
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV w)) v))
          q ↔
        dt.ctlBit PR.one (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf f w) q := by
      intro f
      change dt.ctlBit PR.one (dt.setLeaf PR.zero PR.one _ _) q ↔ _
      rw [setLeaf]
      exact ctlBit_setCtl_of_ne hleaf _ _
    rw [hfold]
    -- the round's exit reads the flags off the (empty) inner gates
    have hround : ∀ f : dt.CtlIx → A,
        dt.ctlBit PR.one (dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf f w) q ↔
        dt.ctlBit PR.one f q := by
      intro f
      have h0 : dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV w)) v f
          (dt.nIn vi) = f := by
        rw [hn0]
        rfl
      rw [show dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf f w =
        dt.ixRoundCtl (elt := elt) F hinj hhasP heltP
          PR.zero_ne_one vi (dt.ixRoundSt st (mV w)) v (semOf w)
          f from rfl,
        ctlBit, ctlBit,
        dt.ixRoundCtl_apply_roundFlag (elt := elt) F hinj hhasP heltP
          hq vi (dt.ixRoundSt st (mV w)) v
          (semOf w) f, h0]
    rw [hround]
    exact ih

variable {vi st mV semOf} in
omit [Finite I] [Finite R] [Finite P] in
/-- **A round flag at the round's exit reads as the per-polarity pass**:
every quantified level of the flag's polarity holds an encoding-shaped,
one-hot, domain-satisfying block value. The capstone's `hEx`/`hAll`. -/
theorem ixCtlBit_roundFX_pass_iff (hzo : PR.zero ≠ PR.one) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (v : Univ A R P dt.KIx dt.dd → Prop) (fG : dt.CtlIx → A) (a : ιV) :
    dt.ctlBit PR.one
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
        q ↔
      ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = q →
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ := by
  classical
  have hIG : dt.ctlBit PR.one
      (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
        vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
      q ↔
      dt.ctlBit PR.one
        (dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi)) q := by
    rw [show dt.ixRoundFX (elt := elt) F hinj hhasP heltP vi st v mV semOf
        (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a =
      dt.ixRoundCtl (elt := elt) F hinj hhasP heltP
        PR.zero_ne_one vi (dt.ixRoundSt st (mV a)) v (semOf a)
        (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) from rfl,
      ctlBit, ctlBit,
      dt.ixRoundCtl_apply_roundFlag (elt := elt) F hinj hhasP heltP hq vi (dt.ixRoundSt st (mV a)) v
        (semOf a) (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a)]
  rcases Nat.eq_zero_or_pos (dt.nIn vi) with hn0 | hpos
  · have hL : dt.ctlBit PR.one
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) a)
        q := by
      rw [hIG]
      have h0 : dt.ixIGFs (elt := elt) F PR.zero PR.one hhasP vi (dt.ixRoundSt st (mV a)) v
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a) (dt.nIn vi) =
          dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a := by
        rw [hn0]
        rfl
      rw [h0]
      exact dt.ixCtlBit_flag_varFM_of_nIn_zero (elt := elt) F hinj hhasP heltP hzo hn0 hq v fG a
    exact iff_of_true hL (fun ℓ => absurd ℓ.isLt (by omega))
  · rw [hIG, ctlBit_flag_ixIGFs (F := F) (elt := elt) (hinj := hinj) (helt := heltP)
      (hhas := hhasP) (hzo := hzo) (hq := hq) (vi := vi)
      (stV := dt.ixRoundSt st (mV a)) (v := v)
      (f₀ := dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG a)
      (h1 := hpos) (hn := le_refl _)]
    exact ⟨fun h ℓ => h ℓ ℓ.isLt, fun h ℓ _ => h ℓ⟩

variable {vi} in
omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
/-- **The two polarity readings deliver the full pass**: every level's
flag is one of the two. The capstone's `hPass`. -/
theorem ixRoundPass_of_polarities {zero one : A} {stV : TapeSt dt A R P I}
    (hEx : ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
      dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (hAl : ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
      dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) :
    ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ := by
  intro ℓ
  have hflagn : dt.igFlag vi ℓ = dt.existGateC ∨
      dt.igFlag vi ℓ = dt.allGateC := by
    rw [igFlag]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hflagn with hf | hf
  · exact hEx ℓ hf
  · exact hAl ℓ hf

end RoundSem

/-! ### The pack, built from the pass -/

section PassPack

variable (zero one : A)
-- The marks-to-shapes bridge at a coarse file: a level's gate passes exactly
-- when the block its **address** holds is an encoding. Free at the elementwise
-- file (`DescriptiveComplexity.Pfp.PfpData.igPassP_iff_isEnc`); at a coarse one
-- it is what the file's coverage of the argument blocks buys.
variable (hpassEnc : ∀ (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F zero one vi stV ℓ ↔
    IsEnc dt.ly zero one (wmBlk (ixAddr elt stV.val)
      (PfpTag.arg (toLex (dt.igBlk vi ℓ)) : PfpTag R P dt.KIx)))

open Classical in
/-- **The valuation a passing round holds**: the gated address's points at
the free levels, the points the pass's encodings choose at the quantified
ones. -/
noncomputable def ixPassW (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A) (j : Fin (dt.nOf vi)) :
    dt.X.Map A :=
  if h : (j : ℕ) < dt.arOf vi then mbW ⟨(j : ℕ), h⟩
  else ((hpassEnc vi stV
    ⟨(j : ℕ) - dt.arOf vi, by
      have h1 := j.isLt
      simp only [nIn]
      omega⟩).mp (hp _)).choose

variable {zero one}

omit [Finite I] [Fintype dt.SlotIx] [L.IsRelational] [Finite R] [Finite P] in
/-- **The master encoding fact of a passing round**: every level's block —
the working address's at the free levels, the round register's at the
quantified ones — encodes the valuation's point. The capstone's `hENC`,
and `DescriptiveComplexity.Pfp.PfpData.ixMkKindSem`'s input. -/
theorem ixPassW_hENC (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk (ixAddr elt stV.mir)
        (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (mbW ℓ))
    (j : Fin (dt.nOf vi)) :
    wmBlk (ixAddr elt (dt.lvSet stV vi j))
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one (dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
        (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
        (hp := hp) (mbW := mbW) j) := by
  rw [lvSet, lvBlk, ixPassW]
  by_cases h : (j : ℕ) < dt.arOf vi
  · rw [if_pos h, dif_pos h, dif_pos h]
    exact hmb ⟨(j : ℕ), h⟩
  · rw [if_neg h, dif_neg h, dif_neg h]
    have hspec := ((hpassEnc vi stV
      ⟨(j : ℕ) - dt.arOf vi, by
        have h1 := j.isLt
        simp only [nIn]
        omega⟩).mp (hp _)).choose_spec
    have hblk : dt.igBlk vi
        ⟨(j : ℕ) - dt.arOf vi, by
          have h1 := j.isLt
          simp only [nIn]
          omega⟩ =
        (Sum.inr ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          Fin dt.ko ⊕ Fin dt.ki) := by
      rw [igBlk]
      congr 1
      exact Fin.ext (by
        change dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ)
        omega)
    rw [← hblk]
    exact hspec

/-- **The semantic pack of a passing round**, constructed: the capstone's
`semOf`, with `hsem` definitional. -/
noncomputable def ixPassSem (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk (ixAddr elt stV.mir)
        (PfpTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (mbW ℓ)) :
    ∀ b : Fin (dt.natOf vi), dt.IxKindSem zero one vi stV elt (dt.kindOf vi b) :=
  fun b => dt.ixMkKindSem (elt := elt) zero one vi stV
    (dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
      (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
      (hp := hp) (mbW := mbW))
    (dt.ixPassW_hENC (elt := elt) (F := F) (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
      (hp := hp) (mbW := mbW) (hmb := hmb))
    (dt.kindOf vi b)

end PassPack

/-! ### The stage tracks at the composed target -/

section StageDict

variable (zero one : A)
variable (hhas : F.toLayout.HasName zero)
variable (helt : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhas b c) = dt.blkElt b (pad zero c))

variable {zero one} in
omit [Finite I] [L.Structure A] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
include hinj helt in
/-- **The composed TARGET's address, in closed form**: the coarse file's
`DescriptiveComplexity.Pfp.PfpData.ixStageTgt` read as a set of elements is
the elementwise closed form – the destination cells are the elements the
destination registers stand for, and the source bits are read at the source
registers' elements. -/
theorem ixAddr_ixStageTgt_iff (vi : dt.VarIx) (iv : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    (st : TapeSt dt A R P I) (n : ℕ) (x : Univ A R P dt.KIx dt.dd) :
    ixAddr elt (dt.ixStageTgt F hhas vi ts st n) x ↔
      ∃ (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)),
        (ℓ : ℕ) < n ∧ x = dt.stageXD zero iv ℓ b ∧
          ixAddr elt (dt.lvSet st vi (ts ℓ)) (dt.stageXS zero vi iv ts ℓ b) := by
  have hD : ∀ (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)),
      elt (dt.ixStageXD F hhas ℓ b) = dt.stageXD zero iv ℓ b := by
    intro ℓ b
    rw [ixStageXD, helt]
    rfl
  have hS : ∀ (ℓ : Fin (dt.d.B.arity iv)) (b : Lex (Fin dt.dd0 → A)),
      elt (dt.ixStageXS F hhas vi ts ℓ b) = dt.stageXS zero vi iv ts ℓ b := by
    intro ℓ b
    rw [ixStageXS, helt]
    rfl
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨ℓ, b, hlt, rfl, hsrc⟩ := (dt.ixStageTgt_iff F hhas vi ts st n u).mp hu
    exact ⟨ℓ, b, hlt, hD ℓ b, (hS ℓ b) ▸ ⟨_, rfl, hsrc⟩⟩
  · rintro ⟨ℓ, b, hlt, rfl, hsrcA⟩
    refine ⟨dt.ixStageXD F hhas ℓ b, hD ℓ b, ?_⟩
    refine (dt.ixStageTgt_iff F hhas vi ts st n _).mpr ⟨ℓ, b, hlt, rfl, ?_⟩
    have h := hsrcA
    rw [← hS ℓ b, ixAddr_elt hinj] at h
    exact h

variable {zero one} in
omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
include hinj helt in
/-- **The composed TARGET's argument blocks are the sources'**: after all
copy loops, block `ℓ` of TARGET is the position's source block — the copy
is faithful on the padded cells, and an encoding holds no others. -/
theorem ixWmBlk_stageTgtD_eq_encMap
    (vi : dt.VarIx) (iv : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    (stV : TapeSt dt A R P I)
    {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (ixAddr elt (dt.lvSet stV vi (ts ℓ)))
        (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ))
    (ℓ : Fin (dt.d.B.arity iv)) :
    wmBlk (ixAddr elt (dt.ixStageTgt F hhas vi ts stV (dt.d.B.arity iv)))
        (PfpTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one (p ℓ) := by
  classical
  funext w
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨ℓ', u, -, hy, hsrcbit⟩ :=
      (dt.ixAddr_ixStageTgt_iff (F := F) (hhas := hhas) (helt := helt)
        (zero := zero) (hinj := hinj) vi iv ts stV (dt.d.B.arity iv)
        ((PfpTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx), w)).mp h
    -- the destination cell decodes the position and the tuple
    have htag := congrArg Prod.fst hy
    have hsnd := congrArg Prod.snd hy
    have hℓ : ℓ' = ℓ := by
      have h1 : (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki)) : Lex (Fin dt.ko ⊕ Fin dt.ki)) =
          toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ') :
            Fin dt.ko ⊕ Fin dt.ki)) := by
        injection htag
      have h2 : (Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki) =
          Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ') :=
        congrArg ofLex h1
      have h3 := Sum.inl.inj h2
      exact (Fin.castLE_injective _ h3).symm
    subst hℓ
    rw [show w = pad (dd := dt.dd) zero (ofLex u) from hsnd]
    have hbit : wmBlk (ixAddr elt (dt.lvSet stV vi (ts ℓ')))
        (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ'))) : PfpTag R P dt.KIx)
        (pad (dd := dt.dd) zero (ofLex u)) := hsrcbit
    rw [hsrc ℓ'] at hbit
    exact hbit
  · have hpadded : w = pad (dd := dt.dd) zero (unpad dt.dd0Le w) :=
      (pad_unpad dt.dd0Le fun j hj => isPad_of_encMap h j hj).symm
    refine (dt.ixAddr_ixStageTgt_iff (F := F) (hhas := hhas) (helt := helt)
      (zero := zero) (hinj := hinj) vi iv ts stV (dt.d.B.arity iv)
      ((PfpTag.arg (toLex ((Sum.inl
        (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) : PfpTag R P dt.KIx), w)).mpr
      ⟨ℓ, toLex (unpad dt.dd0Le w), ℓ.isLt, ?_, ?_⟩
    · refine Prod.ext rfl ?_
      exact hpadded
    · change wmBlk (ixAddr elt (dt.lvSet stV vi (ts ℓ)))
        (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : PfpTag R P dt.KIx)
        (pad (dd := dt.dd) zero (unpad dt.dd0Le w))
      rw [hsrc ℓ, ← hpadded]
      exact h

variable {zero one} in
omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
include hinj helt in
/-- **The composed TARGET *is* the canonical address of the points it names**:
its blocks below the arity are their encodings and it marks nothing else, which
is `tupAddr_of_blocks`. This is what lets a dictionary be asked for at canonical
addresses alone – and so lets one be *read off* an arbitrary set of marked
addresses, which is what a backward reading of a run has to do. -/
theorem ixAddr_ixStageTgt_eq_tupAddr
    (vi : dt.VarIx) (iv : dt.d.B.ι) (ha : dt.d.B.arity iv ≤ dt.ko)
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    (stV : TapeSt dt A R P I)
    {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (ixAddr elt (dt.lvSet stV vi (ts ℓ)))
        (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ)) :
    ixAddr elt (dt.ixStageTgt F hhas vi ts stV (dt.d.B.arity iv)) =
      tupAddr dt.ly zero one (R := R) (P := P) (ki := dt.ki) ha p := by
  -- every marked point is a destination cell, whose tag is the block of its
  -- position — so the address marks argument blocks below the arity alone
  have hpt : ∀ u : Univ A R P dt.KIx dt.dd,
      ixAddr elt (dt.ixStageTgt F hhas vi ts stV (dt.d.B.arity iv)) u →
      ∃ ℓ : Fin (dt.d.B.arity iv), u.1 = argOut dt.ki
        (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) := by
    intro u hu
    obtain ⟨ℓ, b, -, rfl, -⟩ :=
      (dt.ixAddr_ixStageTgt_iff (F := F) (hhas := hhas) (helt := helt)
        (zero := zero) (hinj := hinj) vi iv ts stV (dt.d.B.arity iv) u).mp hu
    exact ⟨ℓ, rfl⟩
  refine tupAddr_of_blocks ha
    (fun ℓ => ?_) (fun k hk v hv => ?_) (fun u hu => ?_)
  · have h := ixWmBlk_stageTgtD_eq_encMap (dt := dt) (F := F) (hhas := hhas)
      (helt := helt) (hinj := hinj) (vi := vi) (iv := iv) (ts := ts) (stV := stV)
      (p := p) (hsrc := hsrc) (ℓ := ℓ)
    have hcast : (Fin.castLE ha ℓ : Fin dt.ko) =
        Fin.castLE (dt.arOf_le_ko (some iv)) ℓ := Fin.ext rfl
    rw [hcast]
    exact h
  · obtain ⟨ℓ, hℓ⟩ := hpt _ hv
    have hkeq : (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ : Fin dt.ko) = k :=
      argOut_injective hℓ.symm
    have hval : ((k : ℕ)) = (ℓ : ℕ) := congrArg Fin.val hkeq.symm
    have := ℓ.isLt
    omega
  · obtain ⟨ℓ, hℓ⟩ := hpt u hu
    exact ⟨_, hℓ⟩

variable {zero one} in
omit [Finite I] [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
include hinj helt in
/-- **A stage track reads the dictionary at the composed target**, asking for
the dictionary at *canonical addresses only*: the target is the canonical
address of the points it names (`ixAddr_ixStageTgt_eq_tupAddr`), so what a run
has to know about its stage tracks is one bit per tuple, not one per address.
Forwards that is weaker than asking for the dictionary at every address, and
the guess supplies it just the same; backwards it is the difference between a
dictionary that can be read off a run and one that cannot. -/
theorem ixOld_stage_of_dict
    (vi : dt.VarIx) (iv : dt.d.B.ι) (ha : dt.d.B.arity iv ≤ dt.ko)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (stV : TapeSt dt A R P I)
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ x : Fin (dt.d.B.arity iv) → dt.X.Map A,
      Below (tupAddr dt.ly zero one (R := R) (P := P) (ki := dt.ki) ha x) →
      (stV.old iv (tupAddr dt.ly zero one (R := R) (P := P) (ki := dt.ki) ha x) ↔
        σ iv x))
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (ixAddr elt (dt.lvSet stV vi (ts ℓ)))
        (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ))
    (hbelow : Below (ixAddr elt
      (dt.ixStageTgt F hhas vi ts stV (dt.d.B.arity iv)))) :
    stV.old iv (ixAddr elt (dt.ixStageTgt F hhas vi ts stV (dt.d.B.arity iv))) ↔
      σ iv p := by
  have heq := ixAddr_ixStageTgt_eq_tupAddr (dt := dt) (F := F) (hhas := hhas)
    (helt := helt) (hinj := hinj) (zero := zero) (one := one) vi iv ha ts stV hsrc
  rw [heq]
  rw [heq] at hbelow
  exact hdict p hbelow

end StageDict

/-! ### The leaf, read at the round's register -/

section LeafSem

variable (zero one : A)
-- The marks-to-shapes bridge at a coarse file: a level's gate passes exactly
-- when the block its **address** holds is an encoding. Free at the elementwise
-- file (`DescriptiveComplexity.Pfp.PfpData.igPassP_iff_isEnc`); at a coarse one
-- it is what the file's coverage of the argument blocks buys.
variable (hpassEnc : ∀ (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F zero one vi stV ℓ ↔
    IsEnc dt.ly zero one (wmBlk (ixAddr elt stV.val)
      (PfpTag.arg (toLex (dt.igBlk vi ℓ)) : PfpTag R P dt.KIx)))

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite I] [L.IsRelational] in
variable {zero one} in
include hpassEnc in
/-- **A per-polarity pass is the split's gate clause**, reindexed from the
quantified levels to the pack's indices. -/
theorem ixRoundPass_iff_split_gen (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    {q : dt.CtlIx} {bpol : Bool}
    (hqiff : ∀ ℓ : Fin (dt.nIn vi),
      dt.igFlag vi ℓ = q ↔ dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = bpol) :
    (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = q →
        dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) ↔
      ∀ j : Fin (dt.nOf vi), dt.arOf vi ≤ (j : ℕ) →
        dt.polOf vi (j : ℕ) = bpol →
        IsEnc dt.ly zero one
          (ixBlk (argIn dt.ko) (ixAddr elt stV.val)
            ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩) := by
  constructor
  · intro h j hj hpol
    have hℓlt : (j : ℕ) - dt.arOf vi < dt.nIn vi := by
      have h1 := j.isLt
      simp only [nIn]
      omega
    set ℓj : Fin (dt.nIn vi) := ⟨(j : ℕ) - dt.arOf vi, hℓlt⟩ with hℓj
    have hnat : dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ) := by omega
    have hflag : dt.igFlag vi ℓj = q := by
      rw [hqiff ℓj]
      rw [show dt.arOf vi + (ℓj : ℕ) = (j : ℕ) from hnat]
      exact hpol
    have hIE := (hpassEnc vi stV ℓj).mp
      (h ℓj hflag)
    have hblk : (PfpTag.arg (toLex (dt.igBlk vi ℓj)) : PfpTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      exact congrArg PfpTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext hnat)))
    rw [show (ixBlk (argIn dt.ko) (ixAddr elt stV.val)
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk (ixAddr elt stV.val)
        (argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩)
      from rfl, ← hblk]
    exact hIE
  · intro h ℓ hflag
    have hjlt : dt.arOf vi + (ℓ : ℕ) < dt.nOf vi := by
      have h1 := ℓ.isLt
      simp only [nIn] at h1
      omega
    have hIE := h ⟨dt.arOf vi + (ℓ : ℕ), hjlt⟩ (Nat.le_add_right _ _)
      ((hqiff ℓ).mp hflag)
    refine (hpassEnc vi stV ℓ).mpr ?_
    have hblk : (PfpTag.arg (toLex (dt.igBlk vi ℓ)) : PfpTag R P dt.KIx) =
        argIn dt.ko
          ⟨dt.arOf vi + (ℓ : ℕ),
            lt_of_lt_of_le hjlt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      exact congrArg PfpTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext rfl)))
    rw [show (wmBlk (ixAddr elt stV.val)
        (PfpTag.arg (toLex (dt.igBlk vi ℓ)) : PfpTag R P dt.KIx) :
          (Fin dt.dd → A) → Prop) =
      ixBlk (argIn dt.ko) (ixAddr elt stV.val)
        ⟨dt.arOf vi + (ℓ : ℕ), lt_of_lt_of_le hjlt (dt.nOf_le_ki vi)⟩
      from by rw [hblk]; rfl]
    exact hIE

variable [LinearOrder (dt.X.Map A)]

variable {zero one} in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite I] [L.IsRelational]
  [LinearOrder (dt.X.Map A)] in
include hpassEnc in
/-- **The valuation the leaf decodes is the pass's**: every level's block
of the leaf's reading encodes `ixPassW`'s point. -/
theorem ixLevelVal_encMap (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ)
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (j : Fin (dt.nOf vi)) :
    dt.levelVal vi mb (ixBlk (argIn dt.ko) (ixAddr elt stV.val)) j =
      encMap dt.ly zero one
        (dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
        (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
        (hp := hp) (mbW := mbW) j) := by
  rw [levelVal, ixPassW]
  by_cases h : (j : ℕ) < dt.arOf vi
  · rw [dif_pos h, dif_pos h]
    exact hmb ⟨(j : ℕ), h⟩
  · rw [dif_neg h, dif_neg h]
    have hspec := ((hpassEnc vi stV
      ⟨(j : ℕ) - dt.arOf vi, by
        have h1 := j.isLt
        simp only [nIn]
        omega⟩).mp (hp _)).choose_spec
    have hblk : (PfpTag.arg (toLex (dt.igBlk vi
        ⟨(j : ℕ) - dt.arOf vi, by
          have h1 := j.isLt
          simp only [nIn]
          omega⟩)) : PfpTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      refine congrArg PfpTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext ?_)))
      change dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ)
      omega
    rw [show (ixBlk (argIn dt.ko) (ixAddr elt stV.val)
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk (ixAddr elt stV.val)
        (argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩)
      from rfl, ← hblk]
    exact hspec

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite I] [L.IsRelational] in
variable {zero one} in
include hpassEnc in
/-- **The leaf at a passing round is the matrix's value at the pass's
points** — the capstone's `hPsPass`, with `Ps` the gated matrix
`DescriptiveComplexity.Pfp.PfpData.leafP`. -/
theorem ixLeafP_pass_iff (hzo : zero ≠ one) (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) :
    dt.leafP zero one vi σ mb (ixBlk (argIn dt.ko) (ixAddr elt stV.val)) ↔
      qfValue (dt.matOf vi)
        (fun atm => (matAtom? atm).elim False
          (MatAtom.holds σ
            (dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
              (hpassEnc := hpassEnc) (vi := vi)
              (stV := stV) (hp := hp) (mbW := mbW)))) := by
  have houter : ∀ k : Fin dt.ko, (k : ℕ) < dt.arOf vi →
      IsEnc dt.ly zero one (mb k) := by
    intro k hk
    exact ⟨mbW ⟨(k : ℕ), hk⟩, hmb ⟨(k : ℕ), hk⟩⟩
  rw [leafP_iff_split vi σ mb _ houter]
  have hgate : ∀ j : Fin (dt.nOf vi), dt.arOf vi ≤ (j : ℕ) →
      IsEnc dt.ly zero one
        (ixBlk (argIn dt.ko) (ixAddr elt stV.val)
          ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩) := by
    intro j hj
    have hℓlt : (j : ℕ) - dt.arOf vi < dt.nIn vi := by
      have h1 := j.isLt
      simp only [nIn]
      omega
    have hIE := (hpassEnc vi stV
      ⟨(j : ℕ) - dt.arOf vi, hℓlt⟩).mp (hp _)
    have hblk : (PfpTag.arg (toLex (dt.igBlk vi
        ⟨(j : ℕ) - dt.arOf vi, hℓlt⟩)) : PfpTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      refine congrArg PfpTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext ?_)))
      change dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ)
      omega
    rw [show (ixBlk (argIn dt.ko) (ixAddr elt stV.val)
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk (ixAddr elt stV.val)
        (argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩)
      from rfl, ← hblk]
    exact hIE
  have hval : (fun j => Function.invFun (encMap dt.ly zero one)
      (dt.levelVal vi mb (ixBlk (argIn dt.ko) (ixAddr elt stV.val)) j)) =
      dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
        (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
        (hp := hp) (mbW := mbW) := by
    funext j
    rw [ixLevelVal_encMap (dt := dt) (F := F) (hpassEnc := hpassEnc) vi stV hp mb
      mbW hmb j]
    exact Function.leftInverse_invFun (encMap_injective dt.ly hzo) _
  constructor
  · rintro ⟨-, hM⟩
    have hMM := hM (fun j hj _ => hgate j hj)
    rw [hval] at hMM
    exact (realize_iff_qfValue_holds (dt.matOf_isQF vi) σ _).mp hMM
  · intro hq
    refine ⟨fun j hj _ => hgate j hj, fun _ => ?_⟩
    rw [show (fun j => Function.invFun (encMap dt.ly zero one)
        (dt.levelVal vi mb (ixBlk (argIn dt.ko) (ixAddr elt stV.val)) j)) =
      dt.ixPassW (elt := elt) (F := F) (zero := zero) (one := one)
        (hpassEnc := hpassEnc) (vi := vi) (stV := stV)
        (hp := hp) (mbW := mbW) from hval]
    exact (realize_iff_qfValue_holds (dt.matOf_isQF vi) σ _).mpr hq

omit [Fintype dt.SlotIx] [Finite R] [Finite P] [Finite I] [L.IsRelational] in
variable {zero one} in
include hpassEnc in
/-- **The leaf at a failing round is the ∃-clause alone** — the capstone's
`hPsFail`: the ∀-clause's implication is vacuous when the two readings do
not both hold. -/
theorem ixLeafP_fail_iff (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (hEA : ¬((∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
        dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) ∧
      (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
        dt.ixIGPassP (elt := elt) F zero one vi stV ℓ))) :
    (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
        dt.ixIGPassP (elt := elt) F zero one vi stV ℓ) ↔
      dt.leafP zero one vi σ mb (ixBlk (argIn dt.ko) (ixAddr elt stV.val)) := by
  have houter : ∀ k : Fin dt.ko, (k : ℕ) < dt.arOf vi →
      IsEnc dt.ly zero one (mb k) := by
    intro k hk
    exact ⟨mbW ⟨(k : ℕ), hk⟩, hmb ⟨(k : ℕ), hk⟩⟩
  rw [leafP_iff_split vi σ mb _ houter]
  have hExIff := ixRoundPass_iff_split_gen (dt := dt) (F := F) (hpassEnc := hpassEnc) vi stV
    (q := dt.existGateC) (bpol := true) (dt.igFlag_eq_existGateC_iff vi)
  have hAlIff := ixRoundPass_iff_split_gen (dt := dt) (F := F) (hpassEnc := hpassEnc) vi stV
    (q := dt.allGateC) (bpol := false) (dt.igFlag_eq_allGateC_iff vi)
  constructor
  · intro hEx
    refine ⟨hExIff.mp hEx, fun hA' => ?_⟩
    exact absurd ⟨hEx, hAlIff.mpr hA'⟩ hEA
  · rintro ⟨hE', -⟩
    exact hExIff.mpr hE'

end LeafSem

end PfpData

end Pfp

end DescriptiveComplexity
