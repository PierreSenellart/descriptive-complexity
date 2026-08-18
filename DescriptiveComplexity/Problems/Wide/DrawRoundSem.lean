/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstVar
import DescriptiveComplexity.Problems.Wide.DrawGateFacts
import DescriptiveComplexity.Problems.Wide.DrawLeaf

/-!
# The round flags, read semantically, and the pack built from the pass

The two inputs the capstone
`DescriptiveComplexity.Draw.DrawData.accVerdict_varFM_qfValue` still
abstracts — the flags' readings `hEx`/`hAll` and the conditional semantic
pack `semOf` — discharged at the concrete threads:

* **`ctlBit_roundFX_pass_iff`** — a round flag at the round's exit reads
  as the per-polarity pass: every quantified level of that polarity holds
  an encoding-shaped, one-hot, domain-satisfying block. For a variable
  with quantified levels this is the two-flag characterization through
  the exit's flag ride; for one without, the flags are the constant
  `True` the VAL loop's entry seeded, riding every fold update
  (`ctlBit_flag_varFM_of_nIn_zero`).
* **`roundPass_of_polarities`** — the two readings jointly deliver the
  full pass, level by level — the capstone's `hPass`.
* **`passW` / `passW_hENC` / `passSem`** — the valuation, its master
  encoding fact and the semantic pack **constructed from the pass**: the
  free levels are the gated address's points, the quantified ones are
  chosen from `DescriptiveComplexity.Draw.DrawData.igPassP_iff_isEnc` —
  so the capstone's `hsem` is `rfl`.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace DrawData

variable {L : Language.{0, 0}} (dt : DrawData L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section RoundSem

variable (vi : dt.VarIx) (st : TapeStD dt A R P)
variable {v : Univ A R P dt.KIx dt.dd → Prop}
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi (dt.roundSt st (mV a)) (dt.kindOf vi b))

/-! ### The flags along the VAL loop, without quantified levels -/

variable {vi st mV semOf} in
omit [Finite R] [Finite P] in
/-- **Without quantified levels the two flags are constant along the VAL
loop**: the entry seeded them `True`, the inner-gates thread is empty, and
no fold update writes a flag. -/
theorem ctlBit_flag_varFM_of_nIn_zero (hzo : PR.zero ≠ PR.one)
    (hn0 : dt.nIn vi = 0) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (v : Univ A R P dt.KIx dt.dd → Prop) (fG : dt.CtlIx → A) (a : ιV) :
    dt.ctlBit PR.one (dt.varFM RF hord vi st v mV semOf fG a) q := by
  classical
  have hleaf : q ≠ dt.leafC := by
    rcases hq with rfl | rfl <;>
      exact fun h => by injection h with h'; exact absurd h' (by decide)
  induction a using order_induction with
  | hmin z hz =>
    rw [show dt.varFM RF hord vi st v mV semOf fG z =
      (dt.varArgsOf PR.zero PR.one vi).initSt fG
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v) from iterOrd_bot hz]
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
        (dt.back RF.cell PR.zero PR.one dt.dd0Le
          (dt.roundSt st (fun _ => False)) v))
      (step := fun a q' =>
        (dt.varArgsOf PR.zero PR.one vi).storeCarry
          (tagBlk (dt.valCarry (mV a)).1)
          ((dt.varArgsOf PR.zero PR.one vi).postFold
            (dt.roundFX RF hord vi st v mV semOf q' a)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV a)) v))
      hwz hnb
    rw [show dt.varFM RF hord vi st v mV semOf fG z = _ from hcov]
    have hne : ∀ j : Fin dt.naDim, q ≠ dt.accC j := fun j => by
      rcases hq with rfl | rfl <;> exact fun h => nomatch h
    -- the store rides
    have hstore : ∀ (b : dt.CarryB) (f : dt.CtlIx → A)
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
            (dt.roundFX RF hord vi st v mV semOf f w)
            (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV w)) v))
          q ↔
        dt.ctlBit PR.one (dt.roundFX RF hord vi st v mV semOf f w) q := by
      intro f
      change dt.ctlBit PR.one (dt.setLeaf PR.zero PR.one _ _) q ↔ _
      rw [setLeaf]
      exact ctlBit_setCtl_of_ne hleaf _ _
    rw [hfold]
    -- the round's exit reads the flags off the (empty) inner gates
    have hround : ∀ f : dt.CtlIx → A,
        dt.ctlBit PR.one (dt.roundFX RF hord vi st v mV semOf f w) q ↔
        dt.ctlBit PR.one f q := by
      intro f
      have h0 : dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV w)) v f
          (dt.nIn vi) = f := by
        rw [hn0]
        rfl
      rw [show dt.roundFX RF hord vi st v mV semOf f w =
        dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV w)) v (semOf w)
          f from rfl,
        ctlBit, ctlBit,
        dt.roundCtl_apply_roundFlag RF hord hq vi (dt.roundSt st (mV w)) v
          (semOf w) f, h0]
    rw [hround]
    exact ih

variable {vi st mV semOf} in
omit [Finite R] [Finite P] in
/-- **A round flag at the round's exit reads as the per-polarity pass**:
every quantified level of the flag's polarity holds an encoding-shaped,
one-hot, domain-satisfying block value. The capstone's `hEx`/`hAll`. -/
theorem ctlBit_roundFX_pass_iff (hzo : PR.zero ≠ PR.one) {q : dt.CtlIx}
    (hq : q = dt.existGateC ∨ q = dt.allGateC)
    (v : Univ A R P dt.KIx dt.dd → Prop) (fG : dt.CtlIx → A) (a : ιV) :
    dt.ctlBit PR.one
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
        q ↔
      ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = q →
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ := by
  classical
  have hIG : dt.ctlBit PR.one
      (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
      q ↔
      dt.ctlBit PR.one
        (dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
          (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi)) q := by
    rw [show dt.roundFX RF hord vi st v mV semOf
        (dt.varFM RF hord vi st v mV semOf fG a) a =
      dt.roundCtl RF hord PR.zero_ne_one vi (dt.roundSt st (mV a)) v (semOf a)
        (dt.varFM RF hord vi st v mV semOf fG a) from rfl,
      ctlBit, ctlBit,
      dt.roundCtl_apply_roundFlag RF hord hq vi (dt.roundSt st (mV a)) v
        (semOf a) (dt.varFM RF hord vi st v mV semOf fG a)]
  rcases Nat.eq_zero_or_pos (dt.nIn vi) with hn0 | hpos
  · have hL : dt.ctlBit PR.one
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG a) a)
        q := by
      rw [hIG]
      have h0 : dt.igFs RF PR.zero PR.one vi (dt.roundSt st (mV a)) v
          (dt.varFM RF hord vi st v mV semOf fG a) (dt.nIn vi) =
          dt.varFM RF hord vi st v mV semOf fG a := by
        rw [hn0]
        rfl
      rw [h0]
      exact dt.ctlBit_flag_varFM_of_nIn_zero RF hord hzo hn0 hq v fG a
    exact iff_of_true hL (fun ℓ => absurd ℓ.isLt (by omega))
  · rw [hIG, dt.ctlBit_flag_igFs RF hzo hq vi (dt.roundSt st (mV a)) v
      (dt.varFM RF hord vi st v mV semOf fG a) hpos (le_refl _)]
    exact ⟨fun h ℓ => h ℓ ℓ.isLt, fun h ℓ _ => h ℓ⟩

variable {vi} in
omit [Fintype dt.SlotIx] [Finite R] [Finite P] [L.IsRelational] in
/-- **The two polarity readings deliver the full pass**: every level's
flag is one of the two. The capstone's `hPass`. -/
theorem roundPass_of_polarities {zero one : A} {stV : TapeStD dt A R P}
    (hEx : ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
      dt.igPassP RF zero one vi stV ℓ)
    (hAl : ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
      dt.igPassP RF zero one vi stV ℓ) :
    ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ := by
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

open Classical in
/-- **The valuation a passing round holds**: the gated address's points at
the free levels, the points the pass's encodings choose at the quantified
ones. -/
noncomputable def passW (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A) (j : Fin (dt.nOf vi)) :
    dt.X.Map A :=
  if h : (j : ℕ) < dt.arOf vi then mbW ⟨(j : ℕ), h⟩
  else ((dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV
    ⟨(j : ℕ) - dt.arOf vi, by
      have h1 := j.isLt
      simp only [nIn]
      omega⟩).mp (hp _)).choose

variable {zero one}

omit [Fintype dt.SlotIx] [L.IsRelational] [Finite R] [Finite P] in
/-- **The master encoding fact of a passing round**: every level's block —
the working address's at the free levels, the round register's at the
quantified ones — encodes the valuation's point. The capstone's `hENC`,
and `DescriptiveComplexity.Draw.DrawData.mkKindSem`'s input. -/
theorem passW_hENC (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk stV.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : DrawTag R P dt.KIx) =
        encMap dt.ly zero one (mbW ℓ))
    (j : Fin (dt.nOf vi)) :
    wmBlk (dt.lvSet stV vi j)
        (DrawTag.arg (toLex (dt.lvBlk vi j)) : DrawTag R P dt.KIx) =
      encMap dt.ly zero one (dt.passW RF zero one hzo hlin vi stV hp mbW j) := by
  rw [lvSet, lvBlk, passW]
  by_cases h : (j : ℕ) < dt.arOf vi
  · rw [if_pos h, dif_pos h, dif_pos h]
    exact hmb ⟨(j : ℕ), h⟩
  · rw [if_neg h, dif_neg h, dif_neg h]
    have hspec := ((dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV
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
noncomputable def passSem (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      wmBlk stV.mir
        (DrawTag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko vi) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : DrawTag R P dt.KIx) =
        encMap dt.ly zero one (mbW ℓ)) :
    ∀ b : Fin (dt.natOf vi), dt.KindSem zero one vi stV (dt.kindOf vi b) :=
  fun b => dt.mkKindSem zero one vi stV
    (dt.passW RF zero one hzo hlin vi stV hp mbW)
    (dt.passW_hENC RF hzo hlin vi stV hp mbW hmb) (dt.kindOf vi b)

end PassPack

/-! ### The stage tracks at the composed target -/

section StageDict

variable (zero one : A)

variable {zero one} in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] [L.IsRelational] in
/-- **The composed TARGET's argument blocks are the sources'**: after all
copy loops, block `ℓ` of TARGET is the position's source block — the copy
is faithful on the padded cells, and an encoding holds no others. -/
theorem wmBlk_stageTgtD_eq_encMap
    (vi : dt.VarIx) (iv : dt.d.B.ι)
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    (stV : TapeStD dt A R P) (v : Univ A R P dt.KIx dt.dd → Prop)
    {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (dt.lvSet stV vi (ts ℓ))
        (DrawTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : DrawTag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ))
    (ℓ : Fin (dt.d.B.arity iv)) :
    wmBlk (dt.stageTgtD zero vi iv ts stV v (dt.d.B.arity iv))
        (DrawTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : DrawTag R P dt.KIx) =
      encMap dt.ly zero one (p ℓ) := by
  classical
  funext w
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨ℓ', u, -, hy, hsrcbit⟩ :=
      (dt.stageTgtD_iff (zero := zero) (vi := vi) (iv := iv) (ts := ts)
        (st := stV) (v := v) (dt.d.B.arity iv)
        ((DrawTag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) : DrawTag R P dt.KIx), w)).mp h
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
    have hbit : wmBlk (dt.lvSet stV vi (ts ℓ'))
        (DrawTag.arg (toLex (dt.lvBlk vi (ts ℓ'))) : DrawTag R P dt.KIx)
        (pad (dd := dt.dd) zero (ofLex u)) := hsrcbit
    rw [hsrc ℓ'] at hbit
    exact hbit
  · have hpadded : w = pad (dd := dt.dd) zero (unpad dt.dd0Le w) :=
      (pad_unpad dt.dd0Le fun j hj => isPad_of_encMap h j hj).symm
    refine (dt.stageTgtD_iff (zero := zero) (vi := vi) (iv := iv)
      (ts := ts) (st := stV) (v := v) (dt.d.B.arity iv)
      ((DrawTag.arg (toLex ((Sum.inl
        (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) : DrawTag R P dt.KIx), w)).mpr
      ⟨ℓ, toLex (unpad dt.dd0Le w), ℓ.isLt, ?_, ?_⟩
    · refine Prod.ext rfl ?_
      exact hpadded
    · change wmBlk (dt.lvSet stV vi (ts ℓ))
        (DrawTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : DrawTag R P dt.KIx)
        (pad (dd := dt.dd) zero (unpad dt.dd0Le w))
      rw [hsrc ℓ, ← hpadded]
      exact h

variable {zero one} in
omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] [L.IsRelational] in
/-- **A stage track reads the dictionary at the composed target**: with the
track holding the stage dictionary and the sources encoding the points, the
random access's bit is the stage at those points — the capstone's
`hOld`. -/
theorem old_trackOf_stageTgtD (hzo : zero ≠ one)
    (vi : dt.VarIx) (iv : dt.d.B.ι) (ha : dt.d.B.arity iv ≤ dt.ko)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (stV : TapeStD dt A R P) (v : Univ A R P dt.KIx dt.dd → Prop)
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ s, Below s →
      (stV.old iv s ↔ trackOf dt.ly zero one ha σ s))
    (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
    {p : Fin (dt.d.B.arity iv) → dt.X.Map A}
    (hsrc : ∀ ℓ : Fin (dt.d.B.arity iv),
      wmBlk (dt.lvSet stV vi (ts ℓ))
        (DrawTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : DrawTag R P dt.KIx) =
        encMap dt.ly zero one (p ℓ))
    (hbelow : Below (dt.stageTgtD zero vi iv ts stV v (dt.d.B.arity iv))) :
    stV.old iv (dt.stageTgtD zero vi iv ts stV v (dt.d.B.arity iv)) ↔
      σ iv p :=
  (hdict _ hbelow).trans (trackOf_of_blocks hzo ha σ
    (fun ℓ => dt.wmBlk_stageTgtD_eq_encMap vi iv ts stV v hsrc ℓ))

end StageDict

/-! ### The leaf, read at the round's register -/

section LeafSem

variable (zero one : A)

variable {zero one} in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A level's polarity flag is the ∃-flag exactly by its polarity. -/
theorem igFlag_eq_existGateC_iff (vi : dt.VarIx) (ℓ : Fin (dt.nIn vi)) :
    dt.igFlag vi ℓ = dt.existGateC ↔
      dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = true := by
  rw [igFlag]
  by_cases hb : dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = true
  · rw [if_pos hb]
    exact iff_of_true rfl hb
  · rw [if_neg hb]
    refine iff_of_false (fun h => ?_) hb
    injection h with h'
    exact absurd h' (by decide)

variable {zero one} in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- A level's polarity flag is the ∀-flag exactly by its polarity. -/
theorem igFlag_eq_allGateC_iff (vi : dt.VarIx) (ℓ : Fin (dt.nIn vi)) :
    dt.igFlag vi ℓ = dt.allGateC ↔
      dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = false := by
  rw [igFlag]
  by_cases hb : dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = true
  · rw [if_pos hb]
    refine iff_of_false (fun h => ?_) (by rw [hb]; exact fun h => nomatch h)
    injection h with h'
    exact absurd h' (by decide)
  · rw [if_neg hb]
    exact iff_of_true rfl (Bool.eq_false_iff.mpr hb)

variable {zero one} in
omit [Fintype dt.SlotIx] [L.IsRelational] [Finite R] [Finite P] in
/-- **A per-polarity pass is the split's gate clause**, reindexed from the
quantified levels to the pack's indices. -/
theorem roundPass_iff_split_gen (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P) {q : dt.CtlIx} {bpol : Bool}
    (hqiff : ∀ ℓ : Fin (dt.nIn vi),
      dt.igFlag vi ℓ = q ↔ dt.polOf vi (dt.arOf vi + (ℓ : ℕ)) = bpol) :
    (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = q →
        dt.igPassP RF zero one vi stV ℓ) ↔
      ∀ j : Fin (dt.nOf vi), dt.arOf vi ≤ (j : ℕ) →
        dt.polOf vi (j : ℕ) = bpol →
        IsEnc dt.ly zero one
          (ixBlk (argIn dt.ko) stV.val
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
    have hIE := (dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV ℓj).mp
      (h ℓj hflag)
    have hblk : (DrawTag.arg (toLex (dt.igBlk vi ℓj)) : DrawTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      exact congrArg DrawTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext hnat)))
    rw [show (ixBlk (argIn dt.ko) stV.val
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk stV.val
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
    refine (dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV ℓ).mpr ?_
    have hblk : (DrawTag.arg (toLex (dt.igBlk vi ℓ)) : DrawTag R P dt.KIx) =
        argIn dt.ko
          ⟨dt.arOf vi + (ℓ : ℕ),
            lt_of_lt_of_le hjlt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      exact congrArg DrawTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext rfl)))
    rw [show (wmBlk stV.val
        (DrawTag.arg (toLex (dt.igBlk vi ℓ)) : DrawTag R P dt.KIx) :
          (Fin dt.dd → A) → Prop) =
      ixBlk (argIn dt.ko) stV.val
        ⟨dt.arOf vi + (ℓ : ℕ), lt_of_lt_of_le hjlt (dt.nOf_le_ki vi)⟩
      from by rw [hblk]; rfl]
    exact hIE

variable [LinearOrder (dt.X.Map A)]

variable {zero one} in
omit [Fintype dt.SlotIx] [L.IsRelational] [LinearOrder (dt.X.Map A)] [Finite R] [Finite P] in
/-- **The valuation the leaf decodes is the pass's**: every level's block
of the leaf's reading encodes `passW`'s point. -/
theorem levelVal_encMap (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ)
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (j : Fin (dt.nOf vi)) :
    dt.levelVal vi mb (ixBlk (argIn dt.ko) stV.val) j =
      encMap dt.ly zero one
        (dt.passW RF zero one hzo hlin vi stV hp mbW j) := by
  rw [levelVal, passW]
  by_cases h : (j : ℕ) < dt.arOf vi
  · rw [dif_pos h, dif_pos h]
    exact hmb ⟨(j : ℕ), h⟩
  · rw [dif_neg h, dif_neg h]
    have hspec := ((dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV
      ⟨(j : ℕ) - dt.arOf vi, by
        have h1 := j.isLt
        simp only [nIn]
        omega⟩).mp (hp _)).choose_spec
    have hblk : (DrawTag.arg (toLex (dt.igBlk vi
        ⟨(j : ℕ) - dt.arOf vi, by
          have h1 := j.isLt
          simp only [nIn]
          omega⟩)) : DrawTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      refine congrArg DrawTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext ?_)))
      change dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ)
      omega
    rw [show (ixBlk (argIn dt.ko) stV.val
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk stV.val
        (argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩)
      from rfl, ← hblk]
    exact hspec

variable {zero one} in
omit [Fintype dt.SlotIx] [L.IsRelational] [Finite R] [Finite P] in
/-- **The leaf at a passing round is the matrix's value at the pass's
points** — the capstone's `hPsPass`, with `Ps` the gated matrix
`DescriptiveComplexity.Draw.DrawData.leafP`. -/
theorem leafP_pass_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (hp : ∀ ℓ : Fin (dt.nIn vi), dt.igPassP RF zero one vi stV ℓ) :
    dt.leafP zero one vi σ mb (ixBlk (argIn dt.ko) stV.val) ↔
      qfValue (dt.matOf vi)
        (fun atm => (matAtom? atm).elim False
          (MatAtom.holds σ
            (dt.passW RF zero one hzo hlin vi stV hp mbW))) := by
  have houter : ∀ k : Fin dt.ko, (k : ℕ) < dt.arOf vi →
      IsEnc dt.ly zero one (mb k) := by
    intro k hk
    exact ⟨mbW ⟨(k : ℕ), hk⟩, hmb ⟨(k : ℕ), hk⟩⟩
  rw [leafP_iff_split vi σ mb _ houter]
  have hgate : ∀ j : Fin (dt.nOf vi), dt.arOf vi ≤ (j : ℕ) →
      IsEnc dt.ly zero one
        (ixBlk (argIn dt.ko) stV.val
          ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩) := by
    intro j hj
    have hℓlt : (j : ℕ) - dt.arOf vi < dt.nIn vi := by
      have h1 := j.isLt
      simp only [nIn]
      omega
    have hIE := (dt.igPassP_iff_isEnc RF zero one hzo hlin vi stV
      ⟨(j : ℕ) - dt.arOf vi, hℓlt⟩).mp (hp _)
    have hblk : (DrawTag.arg (toLex (dt.igBlk vi
        ⟨(j : ℕ) - dt.arOf vi, hℓlt⟩)) : DrawTag R P dt.KIx) =
        argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ := by
      rw [igBlk]
      refine congrArg DrawTag.arg (congrArg toLex
        (congrArg Sum.inr (Fin.ext ?_)))
      change dt.arOf vi + ((j : ℕ) - dt.arOf vi) = (j : ℕ)
      omega
    rw [show (ixBlk (argIn dt.ko) stV.val
        ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩ :
          (Fin dt.dd → A) → Prop) =
      wmBlk stV.val
        (argIn dt.ko ⟨(j : ℕ), lt_of_lt_of_le j.isLt (dt.nOf_le_ki vi)⟩)
      from rfl, ← hblk]
    exact hIE
  have hval : (fun j => Function.invFun (encMap dt.ly zero one)
      (dt.levelVal vi mb (ixBlk (argIn dt.ko) stV.val) j)) =
      dt.passW RF zero one hzo hlin vi stV hp mbW := by
    funext j
    rw [dt.levelVal_encMap RF hzo hlin vi stV hp mb mbW hmb j]
    exact Function.leftInverse_invFun (encMap_injective dt.ly hzo) _
  constructor
  · rintro ⟨-, hM⟩
    have hMM := hM (fun j hj _ => hgate j hj)
    rw [hval] at hMM
    exact (realize_iff_qfValue_holds (dt.matOf_isQF vi) σ _).mp hMM
  · intro hq
    refine ⟨fun j hj _ => hgate j hj, fun _ => ?_⟩
    rw [show (fun j => Function.invFun (encMap dt.ly zero one)
        (dt.levelVal vi mb (ixBlk (argIn dt.ko) stV.val) j)) =
      dt.passW RF zero one hzo hlin vi stV hp mbW from hval]
    exact (realize_iff_qfValue_holds (dt.matOf_isQF vi) σ _).mpr hq

variable {zero one} in
omit [Fintype dt.SlotIx] [L.IsRelational] [Finite R] [Finite P] in
/-- **The leaf at a failing round is the ∃-clause alone** — the capstone's
`hPsFail`: the ∀-clause's implication is vacuous when the two readings do
not both hold. -/
theorem leafP_fail_iff (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (vi : dt.VarIx) (stV : TapeStD dt A R P)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mb : Fin dt.ko → (Fin dt.dd → A) → Prop)
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      mb (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly zero one (mbW ℓ))
    (hEA : ¬((∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
        dt.igPassP RF zero one vi stV ℓ) ∧
      (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
        dt.igPassP RF zero one vi stV ℓ))) :
    (∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
        dt.igPassP RF zero one vi stV ℓ) ↔
      dt.leafP zero one vi σ mb (ixBlk (argIn dt.ko) stV.val) := by
  have houter : ∀ k : Fin dt.ko, (k : ℕ) < dt.arOf vi →
      IsEnc dt.ly zero one (mb k) := by
    intro k hk
    exact ⟨mbW ⟨(k : ℕ), hk⟩, hmb ⟨(k : ℕ), hk⟩⟩
  rw [leafP_iff_split vi σ mb _ houter]
  have hExIff := dt.roundPass_iff_split_gen RF hzo hlin vi stV
    (q := dt.existGateC) (bpol := true) (dt.igFlag_eq_existGateC_iff vi)
  have hAlIff := dt.roundPass_iff_split_gen RF hzo hlin vi stV
    (q := dt.allGateC) (bpol := false) (dt.igFlag_eq_allGateC_iff vi)
  constructor
  · intro hEx
    refine ⟨hExIff.mp hEx, fun hA' => ?_⟩
    exact absurd ⟨hEx, hAlIff.mpr hA'⟩ hEA
  · rintro ⟨hE', -⟩
    exact hExIff.mpr hE'

end LeafSem

end DrawData

end Draw

end DescriptiveComplexity
