/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpInstCmp

/-!
# The stage atoms, instantiated: the copy loops

The second semantic instantiation: the tuple loops of a stage atom's
machinery, at the pack `DescriptiveComplexity.Pfp.PfpData.stageArgs`. Each
argument position runs one copy loop – a read at the source block's cell, the
bit through the control's copy flag, a write at the TARGET block's cell – and
this file proves its three invariants and its run:

* `DescriptiveComplexity.Pfp.PfpData.readLv_stageIter0`/`_stageIter1` – the
  loop element is the round's tuple, before and after the store;
* `DescriptiveComplexity.Pfp.PfpData.stageIterD_iff` – the **closed form of
  the destination track**: a cell holds a bit exactly when some round already
  wrote it – the round's source bit – or it held one from the start and no
  round has touched it;
* `DescriptiveComplexity.Pfp.PfpData.stageTuple_run` – the copy loop's run at
  the generated families, by
  `DescriptiveComplexity.Pfp.tuple_run_iter` with the name guards discharged
  through `DescriptiveComplexity.Pfp.PfpData.nameG_iff`.

The chaining of the `k` loops and the whole stage atom's run assemble on
top, with `DescriptiveComplexity.Pfp.PfpData.stage_run`.
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

section StageLoop

variable [Nonempty A]
variable (zero one : A)
variable (vi : dt.VarIx) (iv : dt.d.B.ι)
variable (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi))
variable (av : Fin dt.natMax) (ℓ : Fin (dt.d.B.arity iv))
variable (st : TapeSt dt A R P)

/-- **The source cell of a copy round**: the padded cell of the round's tuple
in the position's source block. -/
noncomputable def stageXS (b : Lex (Fin dt.dd0 → A)) :
    Univ A R P dt.KIx dt.dd :=
  dt.blkElt (dt.lvBlk vi (ts ℓ)) (pad zero (ofLex b))

/-- **The destination cell of a copy round**: the padded cell of the round's
tuple in the TARGET block of the position. -/
noncomputable def stageXD (b : Lex (Fin dt.dd0 → A)) :
    Univ A R P dt.KIx dt.dd :=
  dt.blkElt (Sum.inl (Fin.castLE (dt.arOf_le_ko (some iv)) ℓ))
    (pad zero (ofLex b))

/-- **The background of a copy loop, as a function of the destination
content**: the state with the TARGET register at the given track. -/
noncomputable def stageRestF (m' : Univ A R P dt.KIx dt.dd → Prop) :
    (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A :=
  dt.back zero one dt.dd0Le { st with tgt := m' }

variable {dt zero one vi iv ts av ℓ st}

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- The destination-dependent background moves only at the TARGET slot. -/
theorem stageRestF_off (m₁ m₂ : Univ A R P dt.KIx dt.dd → Prop)
    (r : Univ A R P dt.KIx dt.dd → Prop) (s : dt.SlotIx)
    (hs : s ≠ Slot.tgt) :
    dt.stageRestF zero one st m₁ r s = dt.stageRestF zero one st m₂ r s := by
  match s with
  | .tgt => exact absurd rfl hs
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl

/-! ### The loop element through the copy's operations -/

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- The loop element rides along the copied bit's store. -/
theorem readLv_setCtl_bitFlagC {zero one : A} (b : Prop) (f : dt.CtlIx → A) :
    dt.readLv (dt.setCtl zero one dt.bitFlagC b f) = dt.readLv f := by
  funext j
  rw [readLv, readLv, setCtl_of_ne (lvC_ne_bitFlagC (dt := dt) j)]

section Iter

variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}
variable {mD₀ : Univ A R P dt.KIx dt.dd → Prop} {f₀ : dt.CtlIx → A}
variable {zero one : A}

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- The copy loop's generated round tuples: the pre-store control's loop
element is the round's tuple. -/
theorem readLv_stageIter0 (b : Lex (Fin dt.dd0 → A)) :
    dt.readLv (tupleIter0
      (dt.stageArgs zero one vi iv ts av).setBit
      (dt.stageArgs zero one vi iv ts av).initLv
      (dt.stageArgs zero one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
      (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ b) =
      ofLex b := by
  induction b using order_induction with
  | hmin z hz =>
    have hz0 : tupleIter0
        (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
        (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ z =
        (dt.stageArgs zero one vi iv ts av).initLv f₀
          (dt.stageRestF zero one st mD₀ vAdr) :=
      iterOrd_bot hz
    rw [hz0]
    have hinit : dt.readLv ((dt.stageArgs zero one vi iv ts av).initLv f₀
        (dt.stageRestF zero one st mD₀ vAdr)) = botTup := by
      change dt.readLv (dt.initLvN f₀) = botTup
      rw [initLvN, readLv_putLv]
    rw [hinit, ofLex_eq_botTup_of_bot hz]
  | hstep w z hwz hnb ih =>
    classical
    have hz2 : tupleIter0
        (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
        (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ z =
        (dt.stageArgs zero one vi iv ts av).advLv
          (if dt.lvSet st vi (ts ℓ) (dt.stageXS zero vi iv ts ℓ w) then
            (dt.stageArgs zero one vi iv ts av).setBit true
              (tupleIter0 (dt.stageArgs zero one vi iv ts av).setBit
                (dt.stageArgs zero one vi iv ts av).initLv
                (dt.stageArgs zero one vi iv ts av).advLv
                (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
                (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ w)
              (dt.stageRestF zero one st
                (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS zero vi iv ts ℓ)
                  (dt.stageXD zero iv ℓ) mD₀ w) vAdr)
          else
            (dt.stageArgs zero one vi iv ts av).setBit false
              (tupleIter0 (dt.stageArgs zero one vi iv ts av).setBit
                (dt.stageArgs zero one vi iv ts av).initLv
                (dt.stageArgs zero one vi iv ts av).advLv
                (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
                (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ w)
              (dt.stageRestF zero one st
                (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS zero vi iv ts ℓ)
                  (dt.stageXD zero iv ℓ) mD₀ w) vAdr))
          (dt.stageRestF zero one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS zero vi iv ts ℓ)
              (dt.stageXD zero iv ℓ) mD₀ w) vAdr) :=
      iterOrd_covers hwz hnb
    rw [hz2]
    have hadv : ∀ (q : dt.CtlIx → A) (g : dt.SlotIx → A),
        dt.readLv ((dt.stageArgs zero one vi iv ts av).advLv q g) =
          tupNext (dt.readLv q) := by
      intro q g
      change dt.readLv (dt.advLvN q) = _
      rw [advLvN, readLv_putLv]
    have hset : ∀ (bb : Bool) (q : dt.CtlIx → A) (g : dt.SlotIx → A),
        dt.readLv ((dt.stageArgs zero one vi iv ts av).setBit bb q g) =
          dt.readLv q := by
      intro bb q g
      change dt.readLv (dt.setCtl zero one dt.bitFlagC (bb = true) q) = _
      rw [readLv_setCtl_bitFlagC]
    rw [hadv]
    by_cases hb : dt.lvSet st vi (ts ℓ) (dt.stageXS zero vi iv ts ℓ w)
    · rw [if_pos hb, hset, ih, ofLex_eq_tupNext_of_covers hwz hnb]
    · rw [if_neg hb, hset, ih, ofLex_eq_tupNext_of_covers hwz hnb]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- The post-store control's loop element is still the round's tuple. -/
theorem readLv_stageIter1 (b : Lex (Fin dt.dd0 → A)) :
    dt.readLv (tupleIter1
      (dt.stageArgs zero one vi iv ts av).setBit
      (dt.stageArgs zero one vi iv ts av).initLv
      (dt.stageArgs zero one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) vAdr (dt.stageRestF zero one st)
      (dt.stageXS zero vi iv ts ℓ) (dt.stageXD zero iv ℓ) mD₀ f₀ b) =
      ofLex b := by
  classical
  have hset : ∀ (bb : Bool) (q : dt.CtlIx → A) (g : dt.SlotIx → A),
      dt.readLv ((dt.stageArgs zero one vi iv ts av).setBit bb q g) =
        dt.readLv q := by
    intro bb q g
    change dt.readLv (dt.setCtl zero one dt.bitFlagC (bb = true) q) = _
    rw [readLv_setCtl_bitFlagC]
  rw [tupleIter1]
  by_cases hb : dt.lvSet st vi (ts ℓ) (dt.stageXS zero vi iv ts ℓ b)
  · rw [if_pos hb, hset]
    exact readLv_stageIter0 b
  · rw [if_neg hb, hset]
    exact readLv_stageIter0 b

end Iter

/-! ### The built TARGET, in closed form -/

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- **The destination cells are distinct**: the padded cell of a tuple
determines the tuple. -/
theorem stageXD_injective {zero : A} (b b' : Lex (Fin dt.dd0 → A))
    (h : dt.stageXD (R := R) (P := P) zero iv ℓ b =
      dt.stageXD zero iv ℓ b') : b = b' := by
  have hcoord : ∀ j : Fin dt.dd,
      (dt.stageXD (R := R) (P := P) zero iv ℓ b).2 j =
        (dt.stageXD (R := R) (P := P) zero iv ℓ b').2 j :=
    fun j => congrFun (congrArg Prod.snd h) j
  have hof : ofLex b = ofLex b' := by
    funext j
    have hj := hcoord (Fin.castLE dt.dd0Le j)
    rw [show (dt.stageXD (R := R) (P := P) zero iv ℓ b).2
        (Fin.castLE dt.dd0Le j) =
        pad zero (ofLex b) (Fin.castLE dt.dd0Le j) from rfl,
      show (dt.stageXD (R := R) (P := P) zero iv ℓ b').2
        (Fin.castLE dt.dd0Le j) =
        pad zero (ofLex b') (Fin.castLE dt.dd0Le j) from rfl,
      pad_of_lt (Fin.castLE dt.dd0Le j) j.isLt,
      pad_of_lt (Fin.castLE dt.dd0Le j) j.isLt] at hj
    exact hj
  exact congrArg toLex hof

section Iter2

variable {vAdr : Univ A R P dt.KIx dt.dd → Prop}
variable {mD₀ : Univ A R P dt.KIx dt.dd → Prop} {f₀ : dt.CtlIx → A}
variable {zero one : A}

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] [Nonempty A] in
/-- **The built TARGET block, in closed form**: a cell of the copy loop's
destination holds a bit exactly when it is the destination cell of some
tuple whose source bit is set – the loop having visited every tuple – or it
held one from the start, off the loop's cells. -/
theorem stageIterD_iff (b : Lex (Fin dt.dd0 → A))
    (y : Univ A R P dt.KIx dt.dd) :
    tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS zero vi iv ts ℓ)
        (dt.stageXD zero iv ℓ) mD₀ b y ↔
      ((∃ u < b, y = dt.stageXD zero iv ℓ u ∧
          dt.lvSet st vi (ts ℓ) (dt.stageXS zero vi iv ts ℓ u)) ∨
        ((∀ u < b, y ≠ dt.stageXD zero iv ℓ u) ∧ mD₀ y)) :=
  tupleIterD_iff (fun u u' h => stageXD_injective u u' h) b y

end Iter2

/-! ### The copy loop's run -/

section StageTupleRun

variable {emb : ChainPh 3 TuplePS → P} {exitPh : P}
variable {rEmb : ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
  PR.rules (rEmb i ρ) = tupleRule PR.zero PR.one Slot.wk Slot.reg emb
    ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ) Slot.tgt
    (dt.nameG PR.one ((dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk ℓ)
      dt.lvC)
    (dt.nameG PR.one ((dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk ℓ)
      dt.lvC)
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : Univ A R P dt.KIx dt.dd} (hbot : ∀ y, WMLe gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable (mD₀ : Univ A R P dt.KIx dt.dd → Prop) (f₀ : dt.CtlIx → A)

include hrules hR hlin hbot hv hvi hwkSt in
/-- **One copy loop's run**: from its entry checkpoint at the marker to the
exit phase one cell to its right, the TARGET block of the position holding
the source block's bits at every tuple's cell. -/
theorem stageTuple_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTape
          ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
          (dt.stageRestF PR.zero PR.one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
              (dt.stageXD PR.zero iv ℓ) mD₀ (toLex botTup)))
          (dt.lvSet st vi (ts ℓ))) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (tupleIter1 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
            (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
            (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
            (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀
            (toLex topTup))), Sum.inl v',
        wideTape (PR.trackTape Slot.tgt
          (dt.stageRestF PR.zero PR.one st
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
              (dt.stageXD PR.zero iv ℓ) mD₀ (toLex topTup)))
          (tuplePost (dt.lvSet st vi (ts ℓ))
            (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
              (dt.stageXD PR.zero iv ℓ) mD₀)
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
            (toLex topTup))) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hne_wk_tgt : (Slot.wk : dt.SlotIx) ≠ Slot.tgt := fun h => nomatch h
  have hne_reg_tgt : (Slot.reg : dt.SlotIx) ≠ Slot.tgt := fun h => nomatch h
  refine tuple_run_iter hrules hR hlin hbot hv hvi
    (tup_isBot_iff.mpr botTup_le)
    (tup_isTop_iff.mpr fun p a => le_topTup p a)
    (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀
    (fun m' r => by
      rw [show dt.stageRestF PR.zero PR.one st m' r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun m' r => rfl)
    (fun m' r => dt.back_lvTrack PR.zero PR.one { st with tgt := m' } vi
      (ts ℓ) r)
    (fun m' r => rfl)
    (fun m₁ m₂ r s hs => stageRestF_off m₁ m₂ r s hs)
    (dt.wk_ne_lvTrack vi (ts ℓ)) hne_wk_tgt
    (dt.reg_ne_lvTrack vi (ts ℓ)) hne_reg_tgt
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the source read's name guard
    intro a
    rw [passTracks_of_back
      (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
      (rest := dt.stageRestF PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
          (dt.stageXD PR.zero iv ℓ) mD₀ a))
      (m := dt.lvSet st vi (ts ℓ))
      (fun r => dt.back_lvTrack PR.zero PR.one _ vi (ts ℓ) r) _]
    have hrd : (fun j => tupleIter0
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
        (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a
        (dt.lvC j)) = ofLex a :=
      readLv_stageIter0 a
    refine (dt.nameG_iff hzo hlin _ dt.lvC _ (dt.stageXS PR.zero vi iv ts ℓ a)).mpr ?_
    rw [stageXS, hrd]
    rfl
  · -- the source guard identifies the cell
    intro a r hM
    rw [passTracks_of_back
      (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
      (rest := dt.stageRestF PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
          (dt.stageXD PR.zero iv ℓ) mD₀ a))
      (m := dt.lvSet st vi (ts ℓ))
      (fun r' => dt.back_lvTrack PR.zero PR.one _ vi (ts ℓ) r') _] at hM
    by_cases hreg : ∃ u : Univ A R P dt.KIx dt.dd, r = wmSeg u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.nameG_iff hzo hlin _ dt.lvC _ u).mp hM
      have hrd : (fun j => tupleIter0
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a
          (dt.lvC j)) = ofLex a :=
        readLv_stageIter0 a
      rw [hrd] at hu
      rw [hu]
      rfl
    · exact absurd hM (dt.not_nameG_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the destination write's name guard
    intro a
    rw [passTracks_of_back (t := Slot.tgt)
      (rest := dt.stageRestF PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
          (dt.stageXD PR.zero iv ℓ) mD₀ a))
      (m := tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
        (dt.stageXD PR.zero iv ℓ) mD₀ a)
      (fun r => rfl) _]
    have hrd : (fun j => tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
        (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a
        (dt.lvC j)) = ofLex a :=
      readLv_stageIter1 a
    refine (dt.nameG_iff hzo hlin _ dt.lvC _ (dt.stageXD PR.zero iv ℓ a)).mpr ?_
    rw [stageXD, hrd]
    rfl
  · -- the destination guard identifies the cell
    intro a r hM
    rw [passTracks_of_back (t := Slot.tgt)
      (rest := dt.stageRestF PR.zero PR.one st
        (tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
          (dt.stageXD PR.zero iv ℓ) mD₀ a))
      (m := tupleIterD (dt.lvSet st vi (ts ℓ)) (dt.stageXS PR.zero vi iv ts ℓ)
        (dt.stageXD PR.zero iv ℓ) mD₀ a)
      (fun r' => rfl) _] at hM
    by_cases hreg : ∃ u : Univ A R P dt.KIx dt.dd, r = wmSeg u
    · obtain ⟨u, rfl⟩ := hreg
      have hu := (dt.nameG_iff hzo hlin _ dt.lvC _ u).mp hM
      have hrd : (fun j => tupleIter1
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a
          (dt.lvC j)) = ofLex a :=
        readLv_stageIter1 a
      rw [hrd] at hu
      rw [hu]
      rfl
    · exact absurd hM (dt.not_nameG_of_not_reg hzo
        (fun u hc => hreg ⟨u, hc⟩))
  · -- the copied bit reads back
    intro a
    rw [tupleIter1]
    by_cases hb : dt.lvSet st vi (ts ℓ) (dt.stageXS PR.zero vi iv ts ℓ a)
    · rw [if_pos hb]
      change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.bitFlagC
        (true = true)
        (tupleIter0 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a))
        dt.bitFlagC ↔ _
      rw [ctlBit_setCtl_self hzo]
      exact ⟨fun _ => hb, fun _ => rfl⟩
    · rw [if_neg hb]
      change dt.ctlBit PR.one (dt.setCtl PR.zero PR.one dt.bitFlagC
        (false = true)
        (tupleIter0 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a))
        dt.bitFlagC ↔ _
      rw [ctlBit_setCtl_self hzo]
      exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc hb⟩
  · -- exhausted at the top
    change dt.IsMaxLvN _
    have hrd : dt.readLv (tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
        (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀
        (toLex topTup)) = ofLex (toLex topTup) :=
      readLv_stageIter1 (toLex topTup)
    change IsMaxTup (dt.readLv (tupleIter1
      (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
      (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
      (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
      (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
      (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀
      (toLex topTup)))
    rw [hrd]
    exact isMaxTup_topTup
  · -- not exhausted below the top
    intro a ha hc
    have hrd : dt.readLv (tupleIter1
        (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
        (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
        (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
        (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
        (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀ a) =
        ofLex a :=
      readLv_stageIter1 a
    have hmax : IsMaxTup (ofLex a) := by
      have hc2 : IsMaxTup (dt.readLv (tupleIter1
          (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet st vi (ts ℓ)) v (dt.stageRestF PR.zero PR.one st)
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ) mD₀ f₀
          a)) := hc
      rw [hrd] at hc2
      exact hc2
    exact absurd (tup_isTop_iff.mpr hmax (toLex topTup)) (not_le_of_gt ha)

end StageTupleRun

/-! ### The copy loops, chained: the TARGET built position by position

Position `ℓ`'s loop copies its source block over what the earlier positions
built. The composed content and the control each thread through by one
recursion, `DescriptiveComplexity.Pfp.PfpData.stage_loops_run` chains the
runs – every handover a backed-track equality – and
`DescriptiveComplexity.Pfp.PfpData.stage_run` closes the whole random
access over the chain. -/

section StageChain

variable {v : Univ A R P dt.KIx dt.dd → Prop}

variable (dt zero vi iv ts st v) in
/-- **The TARGET after the first `n` copy loops**: each position's loop
writes its source bits at its destination cells over what the earlier
positions built. -/
noncomputable def stageTgtD : ℕ → Univ A R P dt.KIx dt.dd → Prop
  | 0 => fun _ => False
  | n + 1 =>
    if h : n < dt.d.B.arity iv then
      tuplePost (dt.lvSet { st with sav := v } vi (ts ⟨n, h⟩))
        (tupleIterD (dt.lvSet { st with sav := v } vi (ts ⟨n, h⟩))
          (dt.stageXS zero vi iv ts ⟨n, h⟩) (dt.stageXD zero iv ⟨n, h⟩)
          (stageTgtD n))
        (dt.stageXS zero vi iv ts ⟨n, h⟩) (dt.stageXD zero iv ⟨n, h⟩)
        (toLex topTup)
    else stageTgtD n

variable (dt zero one vi iv ts av st v) in
/-- **The control after the first `n` copy loops.** -/
noncomputable def stageFAt (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 =>
    (dt.stageArgs zero one vi iv ts av).initLv f₀
      (dt.back zero one dt.dd0Le { st with sav := v, tgt := fun _ => False } v)
  | n + 1 =>
    if h : n < dt.d.B.arity iv then
      tupleIter1 (dt.stageArgs zero one vi iv ts av).setBit
        (dt.stageArgs zero one vi iv ts av).initLv
        (dt.stageArgs zero one vi iv ts av).advLv
        (dt.lvSet { st with sav := v } vi (ts ⟨n, h⟩)) v
        (dt.stageRestF zero one { st with sav := v })
        (dt.stageXS zero vi iv ts ⟨n, h⟩) (dt.stageXD zero iv ⟨n, h⟩)
        (dt.stageTgtD zero vi iv ts st v n) (stageFAt f₀ n) (toLex topTup)
    else stageFAt f₀ n

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- **Distinct positions write distinct blocks**: the cell of a copy round
names the position that wrote it. -/
theorem stageXD_pos_eq {ℓ ℓ' : Fin (dt.d.B.arity iv)}
    {u u' : Lex (Fin dt.dd0 → A)}
    (h : dt.stageXD (R := R) (P := P) zero iv ℓ u =
      dt.stageXD zero iv ℓ' u') : ℓ = ℓ' := by
  have hblk := congrArg (fun y : Univ A R P dt.KIx dt.dd => tagBlk y.1) h
  simp only [stageXD, tagBlk_blkElt, Option.some.injEq] at hblk
  exact Fin.castLE_injective _ (Sum.inl_injective hblk)

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite R] [Finite P] in
/-- **The composed TARGET, in closed form**: after the first `n` loops a
cell holds a bit exactly when some position below `n` copied it there – the
source block's bit at the same tuple. Distinct positions write distinct
blocks, so the loops never collide and the disjunction is honest. -/
theorem stageTgtD_iff (n : ℕ) (y : Univ A R P dt.KIx dt.dd) :
    dt.stageTgtD zero vi iv ts st v n y ↔
      ∃ (ℓ : Fin (dt.d.B.arity iv)) (u : Lex (Fin dt.dd0 → A)),
        (ℓ : ℕ) < n ∧ y = dt.stageXD zero iv ℓ u ∧
          dt.lvSet { st with sav := v } vi (ts ℓ)
            (dt.stageXS zero vi iv ts ℓ u) := by
  induction n with
  | zero =>
    exact ⟨fun h => h.elim,
      fun ⟨ℓ, u, hℓ, _⟩ => absurd hℓ (Nat.not_lt_zero _)⟩
  | succ n ih =>
    by_cases hlt : n < dt.d.B.arity iv
    · have hstep : dt.stageTgtD zero vi iv ts st v (n + 1) =
          tuplePost (dt.lvSet { st with sav := v } vi (ts ⟨n, hlt⟩))
            (tupleIterD (dt.lvSet { st with sav := v } vi (ts ⟨n, hlt⟩))
              (dt.stageXS zero vi iv ts ⟨n, hlt⟩)
              (dt.stageXD zero iv ⟨n, hlt⟩)
              (dt.stageTgtD zero vi iv ts st v n))
            (dt.stageXS zero vi iv ts ⟨n, hlt⟩)
            (dt.stageXD zero iv ⟨n, hlt⟩)
            (toLex topTup) := by
        simp only [stageTgtD]
        rw [dif_pos hlt]
      rw [hstep]
      constructor
      · rintro (⟨hy, hsrc⟩ | ⟨hne, hD⟩)
        · exact ⟨⟨n, hlt⟩, toLex topTup, Nat.lt_succ_self n, hy, hsrc⟩
        · rcases (tupleIterD_iff
              (fun u₁ u₂ hh => stageXD_injective u₁ u₂ hh) _ y).mp hD with
            ⟨u, -, hy, hsrc⟩ | ⟨-, hm⟩
          · exact ⟨⟨n, hlt⟩, u, Nat.lt_succ_self n, hy, hsrc⟩
          · obtain ⟨ℓ, u, hℓ, hy, hsrc⟩ := ih.mp hm
            exact ⟨ℓ, u, Nat.lt_succ_of_lt hℓ, hy, hsrc⟩
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hℓn | hℓn
        · -- an earlier position wrote the cell, and position `n` misses it
          have hne : ∀ u' : Lex (Fin dt.dd0 → A),
              y ≠ dt.stageXD zero iv ⟨n, hlt⟩ u' := by
            intro u' hc
            rw [hy] at hc
            exact absurd (congrArg Fin.val (dt.stageXD_pos_eq hc))
              (Nat.ne_of_lt hℓn)
          exact Or.inr ⟨hne _, (tupleIterD_iff
            (fun u₁ u₂ hh => stageXD_injective u₁ u₂ hh) _ y).mpr
            (Or.inr ⟨fun u' _ => hne u', ih.mpr ⟨ℓ, u, hℓn, hy, hsrc⟩⟩)⟩
        · -- position `n` itself wrote it
          have hℓeq : ℓ = ⟨n, hlt⟩ := Fin.ext hℓn
          subst hℓeq
          by_cases hu : u = toLex topTup
          · subst hu
            exact Or.inl ⟨hy, hsrc⟩
          · have hult : u < toLex topTup :=
              lt_of_le_of_ne
                (tup_isTop_iff.mpr (fun p a => le_topTup p a) u) hu
            refine Or.inr ⟨?_, (tupleIterD_iff
              (fun u₁ u₂ hh => stageXD_injective u₁ u₂ hh) _ y).mpr
              (Or.inl ⟨u, hult, hy, hsrc⟩)⟩
            intro hc
            rw [hy] at hc
            exact hu (stageXD_injective u (toLex topTup) hc)
    · have hstep : dt.stageTgtD zero vi iv ts st v (n + 1) =
          dt.stageTgtD zero vi iv ts st v n := by
        simp only [stageTgtD]
        rw [dif_neg hlt]
      rw [hstep, ih]
      constructor
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        exact ⟨ℓ, u, Nat.lt_succ_of_lt hℓ, hy, hsrc⟩
      · rintro ⟨ℓ, u, hℓ, hy, hsrc⟩
        exact ⟨ℓ, u, lt_of_lt_of_le ℓ.isLt (Nat.le_of_not_lt hlt), hy, hsrc⟩

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite R] [Finite P] in
/-- Every cell of the composed TARGET is some position's destination
cell. -/
theorem stageTgtD_mem {n : ℕ} {y : Univ A R P dt.KIx dt.dd}
    (h : dt.stageTgtD zero vi iv ts st v n y) :
    ∃ (ℓ : Fin (dt.d.B.arity iv)) (u : Lex (Fin dt.dd0 → A)),
      y = dt.stageXD zero iv ℓ u := by
  obtain ⟨ℓ, u, -, hy, -⟩ := (dt.stageTgtD_iff n y).mp h
  exact ⟨ℓ, u, hy⟩

section StageChainRun

variable {emb : StagePh (dt.d.B.arity iv) → P} {exitPh : P}
variable {rEmb : ∀ i : StageSite (dt.d.B.arity iv),
  StageSh (dt.d.B.arity iv) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : StageSite (dt.d.B.arity iv))
    (ρ : StageSh (dt.d.B.arity iv) i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).coord
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).oldSlot
    (dt.stageArgs PR.zero PR.one vi iv ts av).setAv
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gbot : Univ A R P dt.KIx dt.dd} (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = v)
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hbot hv hvi hwkSt hmirSt in
/-- **The copy loops of a stage atom, chained and instantiated**: from the
phase entering the first loop to the first reset's checkpoint, the TARGET
holding the composed content of every position – exactly the `hLoops` leg
of `DescriptiveComplexity.Pfp.PfpData.stage_run`. -/
theorem stageChain_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (stageFirstTup emb)
          ((dt.stageArgs PR.zero PR.one vi iv ts av).initLv f₀
            (dt.back PR.zero PR.one dt.dd0Le
              { st with sav := v, tgt := fun _ => False } v))), Sum.inl v',
        wideTape (PR.trackTape Slot.mir
          (dt.back PR.zero PR.one dt.dd0Le
            { st with sav := v, tgt := fun _ => False }) v)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR1)
          (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀
            (dt.d.B.arity iv))), Sum.inl v',
        wideTape (PR.trackTape Slot.mir
          (dt.back PR.zero PR.one dt.dd0Le
            { st with sav := v,
                      tgt := dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv) })
          v) (PR.syElt PR.blank)⟩ := by
  classical
  have hLoop : ∀ ℓ : Fin (dt.d.B.arity iv),
      Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
            (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀ (ℓ : ℕ))),
          Sum.inl v,
          wideTape (PR.trackTape Slot.mir
            (dt.back PR.zero PR.one dt.dd0Le
              { st with sav := v,
                        tgt := dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ) }) v)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (stageNextTup emb ℓ)
            (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀ ((ℓ : ℕ) + 1))),
          Sum.inl v',
          wideTape (PR.trackTape Slot.mir
            (dt.back PR.zero PR.one dt.dd0Le
              { st with sav := v,
                        tgt := dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) })
            v) (PR.syElt PR.blank)⟩ := by
    intro ℓ
    -- the content and the control after position `ℓ`, unfolded once
    have hD1 : dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) =
        tuplePost (dt.lvSet { st with sav := v } vi (ts ℓ))
          (tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
            (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)))
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
          (toLex topTup) := by
      simp only [stageTgtD]
      rw [dif_pos ℓ.isLt]
    have hFa1 : dt.stageFAt PR.zero PR.one vi iv ts av st v f₀
        ((ℓ : ℕ) + 1) =
        tupleIter1 (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
          (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
          (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
          (dt.lvSet { st with sav := v } vi (ts ℓ)) v
          (dt.stageRestF PR.zero PR.one { st with sav := v })
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
          (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ))
          (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀ (ℓ : ℕ))
          (toLex topTup) := by
      simp only [stageFAt]
      rw [dif_pos ℓ.isLt]
    -- the entry tape, re-walked at the source track
    have htin : PR.trackTape Slot.mir
        (dt.back PR.zero PR.one dt.dd0Le
          { st with sav := v,
                    tgt := dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ) }) v =
      PR.trackTape ((dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
        (dt.stageRestF PR.zero PR.one { st with sav := v }
          (tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
            (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)) (toLex botTup)))
        (dt.lvSet { st with sav := v } vi (ts ℓ)) := by
      have hb0 : tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
          (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)) (toLex botTup) =
          dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ) :=
        iterOrd_bot (fun b => tup_isBot_iff.mpr (fun p a => botTup_le p a) b)
      rw [hb0]
      refine (trackTape_of_back (t := Slot.mir) (m := v) ?_).trans
        (trackTape_of_back
          (t := (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack ℓ)
          (m := dt.lvSet { st with sav := v } vi (ts ℓ)) ?_).symm
      · intro r
        rw [show dt.back PR.zero PR.one dt.dd0Le
            { st with sav := v,
                      tgt := dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ) } r
            Slot.mir = bitVal PR.zero PR.one (regBit st.mir r) from rfl,
          hmirSt]
      · intro r
        exact dt.back_lvTrack PR.zero PR.one _ vi (ts ℓ) r
    -- the exit tape, walked back to the mirror
    have htout : PR.trackTape Slot.tgt
        (dt.stageRestF PR.zero PR.one { st with sav := v }
          (tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
            (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)) (toLex topTup)))
        (tuplePost (dt.lvSet { st with sav := v } vi (ts ℓ))
          (tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
            (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
            (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)))
          (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
          (toLex topTup)) =
      PR.trackTape Slot.mir
        (dt.back PR.zero PR.one dt.dd0Le
          { st with sav := v,
                    tgt := dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) }) v := by
      refine (dt.trackTape_back_gen
        (stA := { st with sav := v,
                          tgt := tupleIterD (dt.lvSet { st with sav := v } vi (ts ℓ))
                                   (dt.stageXS PR.zero vi iv ts ℓ) (dt.stageXD PR.zero iv ℓ)
                                   (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ)) (toLex topTup) })
        (stB := { st with sav := v,
                          tgt := dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) })
        ?_ ?_).trans
        (trackTape_of_back (t := Slot.mir) (m := v) ?_).symm
      · intro r s hs
        exact stageRestF_off (st := { st with sav := v }) _ _ r s hs
      · intro r
        rw [show dt.back PR.zero PR.one dt.dd0Le
            { st with sav := v,
                      tgt := dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) } r
            Slot.tgt = bitVal PR.zero PR.one
              (regBit (dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1)) r)
            from rfl, hD1]
      · intro r
        rw [show dt.back PR.zero PR.one dt.dd0Le
            { st with sav := v,
                      tgt := dt.stageTgtD PR.zero vi iv ts st v ((ℓ : ℕ) + 1) } r
            Slot.mir = bitVal PR.zero PR.one (regBit st.mir r) from rfl,
          hmirSt]
    rw [htin, hFa1, ← htout]
    exact dt.stageTuple_run (st := { st with sav := v })
      (emb := fun p => emb (.tupP ℓ p)) (exitPh := stageNextTup emb ℓ)
      (rEmb := fun i ρ => rEmb (.tup ℓ i) ρ)
      (fun i ρ => hrules (.tup ℓ i) ρ) hR hlin hbot hv hvi hwkSt
      (dt.stageTgtD PR.zero vi iv ts st v (ℓ : ℕ))
      (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀ (ℓ : ℕ))
  have hchain := dt.stage_loops_run hrules hR hlin hvi
    (fun _ => Slot.mir)
    (fun j => dt.back PR.zero PR.one dt.dd0Le
      { st with sav := v, tgt := dt.stageTgtD PR.zero vi iv ts st v (j : ℕ) })
    (fun _ => v)
    (fun j r => by
      rw [show dt.back PR.zero PR.one dt.dd0Le
          { st with sav := v,
                    tgt := dt.stageTgtD PR.zero vi iv ts st v (j : ℕ) } r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkSt])
    (fun _ h => nomatch h)
    (fun j => dt.stageFAt PR.zero PR.one vi iv ts av st v f₀ (j : ℕ))
    hLoop
  exact hchain

end StageChainRun

section StageAtomRun

variable {emb : StagePh (dt.d.B.arity iv) → P} {exitPh : P}
variable {rEmb : ∀ i : StageSite (dt.d.B.arity iv),
  StageSh (dt.d.B.arity iv) i → R}
variable [Finite dt.KIx]
variable (hrules : ∀ (i : StageSite (dt.d.B.arity iv))
    (ρ : StageSh (dt.d.B.arity iv) i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcTrack
    (dt.stageArgs PR.zero PR.one vi iv ts av).srcBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).dstBlk
    (dt.stageArgs PR.zero PR.one vi iv ts av).coord
    (dt.stageArgs PR.zero PR.one vi iv ts av).bitFlag
    (dt.stageArgs PR.zero PR.one vi iv ts av).setBit
    (dt.stageArgs PR.zero PR.one vi iv ts av).initLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).advLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).IsMaxLv
    (dt.stageArgs PR.zero PR.one vi iv ts av).oldSlot
    (dt.stageArgs PR.zero PR.one vi iv ts av).setAv
    exitPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (f₀ : dt.CtlIx → A)

include hrules hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt in
/-- **The stage atom's run, fully instantiated**: from its entry phase to
the exit phase, the verdict – the `old` track's bit at the cell the built
TARGET addresses – stored in the atom's control slot, the marker, mirror
and save restored at the home address. Every leg of the random access is
closed: the save, the clear, the copy loops with their composed content,
the seek out, the read under the head, the restore and the seek home. -/
theorem stageAtom_run (b : Bool)
    (hb : st.old iv (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)) ↔
      b = true) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTape Slot.mir (dt.back PR.zero PR.one dt.dd0Le st)
          st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          ((dt.stageArgs PR.zero PR.one vi iv ts av).setAv b
            (dt.stageFAt PR.zero PR.one vi iv ts av st v f₀
              (dt.d.B.arity iv))
            (dt.back PR.zero PR.one dt.dd0Le
              (dt.stageAtSt st v
                (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)))
              (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv))))),
        Sum.inl v',
        wideTape (PR.trackTape Slot.mir
          (dt.back PR.zero PR.one dt.dd0Le (dt.stageEndSt st v))
          (dt.stageEndSt st v).mir) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  -- the built TARGET misses the least element, hence sits in the working area
  have hmTb : ¬dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv) gbot := by
    intro hc
    obtain ⟨ℓ, u, hgb⟩ := dt.stageTgtD_mem hc
    have hblk := congrArg (fun y : Univ A R P dt.KIx dt.dd => tagBlk y.1) hgb
    rw [tagBlk_eq_none_of_least (fun y => (hord gbot y).mp (hbot y))] at hblk
    simp only [stageXD, tagBlk_blkElt] at hblk
    exact nomatch hblk
  have hT : WMSetLt WMLe
      (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv)) (wmSeg gbot) :=
    wmSetLt_wmSeg_of_not_bot hbot hmTb gbot
  obtain ⟨T', hTi⟩ := exists_wmIncr hlin ⟨gbot, hmTb⟩
  refine dt.stage_run hrules hR hlin hord htop hbot hv hvi hwkSt hmirSt
    hbotSt hT hTi ?_ ?_ ?_
  · exact dt.stageChain_run hrules hR hlin hbot hv hvi hwkSt hmirSt f₀
  · change bitVal PR.zero PR.one
      (st.old iv (dt.stageTgtD PR.zero vi iv ts st v (dt.d.B.arity iv))) =
      PR.one ↔ b = true
    exact (bitVal_iff hzo).trans hb
  · exact fun h => nomatch h

end StageAtomRun

end StageChain

end StageLoop

end PfpData

end Pfp

end DescriptiveComplexity

