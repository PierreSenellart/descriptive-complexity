/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawInstVar
import DescriptiveComplexity.Problems.Wide.DrawRunEval

/-!
# The spine, instantiated: one variable's machinery per position

`DescriptiveComplexity.Draw.Data.eval_run` chains one abstract machinery
run per spine position; this file discharges each leg at the program's own
rules. A leg is three pieces: the walk back into the variable's entry
checkpoint (`DescriptiveComplexity.Draw.Data.step_var_back`), the whole
machinery (`DescriptiveComplexity.Draw.Data.varMachine_run`), and the
written exit step (`DescriptiveComplexity.Draw.Data.step_var_exit`) —
whose write is the variable's stage bit, so the tape state after the leg is
`DescriptiveComplexity.Draw.Data.postVarSt`: the round state at the
exhausted VAL, the `new` track updated at the marker.

The enumeration of the VAL loop (`ιV`/`mV`) is shared by every position —
it enumerates the register contents, which do not depend on the variable —
and stays abstract here, with the per-position semantic data
(`DescriptiveComplexity.Draw.Data.KindSem`, the gates' domain facts), to
be supplied by the encoding layer.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (OuterPh (EvalPh dt.nv dt.PMF))]
variable [Language.wide.Structure
  (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
variable {PR : Prog A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable (RF : RegFile (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd))
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

section PostSt

variable (v : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)

open Classical in
/-- **The tape state after one spine position**: the round state at the
final VAL content, the variable's `new` track set at the marker to the
machinery's verdict. -/
noncomputable def postVarSt
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (m : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (i : dt.d.B.ι) (b : Prop) :
    TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  { st with
    val := m
    new := fun i' r => if i' = i ∧ r = v then b else st.new i' r }

variable {zero one : A}
variable {st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))}
variable {m : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {i : dt.d.B.ι} {b : Prop}

omit [Fintype dt.SlotIx]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- Off the marker, the post state's background is the round state's. -/
theorem back_postVarSt_off
    (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hr : r ≠ v) :
    dt.back RF.cell zero one dt.dd0Le (dt.postVarSt v st m i b) r =
      dt.back RF.cell zero one dt.dd0Le (dt.roundSt st m) r := by
  classical
  funext s
  match s with
  | .new i' =>
    change bitVal zero one (if i' = i ∧ r = v then b else st.new i' r) = _
    rw [if_neg (fun h => hr h.2)]
    rfl
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .tgt | .val | .wk | .bot | .ltp | .old _ => rfl

omit [Fintype dt.SlotIx]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
/-- At the marker, the post state's background is the round state's with
the variable's stage slot updated to the verdict bit. -/
theorem back_postVarSt_v :
    dt.back RF.cell zero one dt.dd0Le (dt.postVarSt v st m i b) v =
      Function.update (dt.back RF.cell zero one dt.dd0Le (dt.roundSt st m) v)
        (Slot.new i) (bitVal zero one b) := by
  classical
  funext s
  match s with
  | .new i' =>
    by_cases hi : i' = i
    · subst hi
      change bitVal zero one (if i' = i' ∧ v = v then b else st.new i' v) = _
      rw [if_pos ⟨rfl, rfl⟩, Function.update_self]
    · have hs : (Slot.new i' : dt.SlotIx) ≠ Slot.new i :=
        fun h => hi (by injection h)
      change bitVal zero one (if i' = i ∧ v = v then b else st.new i' v) = _
      rw [if_neg (fun h => hi h.1), Function.update_of_ne hs]
      rfl
  | .reg =>
    rw [Function.update_of_ne (show (Slot.reg : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .regFirst =>
    rw [Function.update_of_ne
      (show (Slot.regFirst : dt.SlotIx) ≠ Slot.new i from fun h => nomatch h)]
    rfl
  | .regLast =>
    rw [Function.update_of_ne
      (show (Slot.regLast : dt.SlotIx) ≠ Slot.new i from fun h => nomatch h)]
    rfl
  | .blk b' =>
    rw [Function.update_of_ne (show (Slot.blk b' : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .name j =>
    rw [Function.update_of_ne (show (Slot.name j : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .pdd =>
    rw [Function.update_of_ne (show (Slot.pdd : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .mir =>
    rw [Function.update_of_ne (show (Slot.mir : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .sav =>
    rw [Function.update_of_ne (show (Slot.sav : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .tgt =>
    rw [Function.update_of_ne (show (Slot.tgt : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .val =>
    rw [Function.update_of_ne (show (Slot.val : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .wk =>
    rw [Function.update_of_ne (show (Slot.wk : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .bot =>
    rw [Function.update_of_ne (show (Slot.bot : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .ltp =>
    rw [Function.update_of_ne (show (Slot.ltp : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .old i' =>
    rw [Function.update_of_ne (show (Slot.old i' : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl

end PostSt

/-! ### One position's leg -/

section Leg

variable {v v' : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}
variable {rEmb : ∀ i : dt.SEF, dt.SESh i → R}
variable (hrules : ∀ (i : dt.SEF) (ρ : dt.SESh i),
  PR.rules (rEmb i ρ) =
    dt.evalRuleF PR.zero PR.one (fun w => dt.varArgsOf PR.zero PR.one w) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)))
variable {gtop gbot : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop}, ¬r gbot →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV →
  Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr WMLe (mV a) (mV a'))
variable (hTestT : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u, ¬dt.InnerFull (fun u => tagBlk u.1) (mV a) u)

/-- **The control after one position's leg**: the machinery's exit fold —
`DescriptiveComplexity.Draw.Data.varMachine_run`'s final control, at the
position's variable. -/
noncomputable def legCtl (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
    (dt.roundFX RF hord (dt.varAt j) st v mV semOf
      (dt.varFM RF hord (dt.varAt j) st v mV semOf
        (dt.gatesFs RF PR.zero PR.one (dt.varAt j) st v
          (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
          dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag =>
              (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim)
          tOf (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt
          ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
          (dt.arOf (dt.varAt j))) aT) aT)
    (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)

/-- **The VAL-loop thread of one position's leg**, at the entry-wrapped
control — the `varFM` iteration the round hypothesis is stated over. -/
noncomputable def legFM (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : ιV → dt.CtlIx → A :=
  dt.varFM RF hord (dt.varAt j) st v mV semOf
    (dt.gatesFs RF PR.zero PR.one (dt.varAt j) st v
      (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag =>
          (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      tOf (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt
      ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
      (dt.arOf (dt.varAt j)))

/-- **The control after one position's leg, threaded** — the twin of
`DescriptiveComplexity.Draw.Data.legCtl`, with the VAL loop's rounds run
at the states the thread produces for them. -/
noncomputable def legCtlT (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
    (dt.varFXT RF hord (dt.varAt j) st v mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT)
    (dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.varStE RF hord (dt.varAt j) st v mV semT
        (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT) v)

/-- **The tape state after one position's leg, threaded**: the VAL loop's
exit state — the entry state's SAV and TARGET normalized if any of its
rounds ran a stage atom — with the variable's `new` track written at the
marker. -/
noncomputable def legStT (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.postVarSt v
    (dt.varStE RF hord (dt.varAt j) st v mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT)
    (mV aT) (dt.varList.get j)
    ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
      (dt.legCtlT (aT := aT) RF hord mV j st tOf semT f₀))

include hord in
omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [Finite ιV] in
/-- **What a leg leaves alone**: the machinery writes its own two scratch
registers and its stage bit, so the mirror, the marker, the bottom and end
marks and the stage dictionary all ride — which is what carries the next
position's pack and, one scale up, the sweep's own invariants. -/
theorem legStT_fields (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).mir = st.mir ∧
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).wk = st.wk ∧
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).bot = st.bot ∧
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).old = st.old ∧
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).ltp = st.ltp ∧
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀).val = mV aT := by
  obtain ⟨hwk, hmir, hbot, -, hold⟩ := dt.roundEndSt_fields
    (zero := PR.zero) (one := PR.one) RF (dt.varAt j)
    (dt.varStT RF hord (dt.varAt j) st v mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT) v
    (dt.varFMT RF hord (dt.varAt j) st v mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT)
  have hltp : (dt.varStE RF hord (dt.varAt j) st v mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT).ltp = st.ltp := by
    rw [varStE, dt.roundEndSt_eq (zero := PR.zero) (one := PR.one)]
    rfl
  exact ⟨hmir, hwk, hbot, hold, hltp, rfl⟩

include hord in
omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx] in
/-- **A position's threaded leg computes the unthreaded fold**: its VAL loop
is the unthreaded loop (`varFMT_eq_varFM`), its last round the unthreaded
round (`varFXT_eq_roundFX`), and the background it folds against is the
round state's, the loop's exit differing from it in SAV and TARGET alone.
This is what makes the branched leg's stage bit
(`DescriptiveComplexity.Draw.Data.legBitB`) the verdict
`DescriptiveComplexity.Draw.Data.accVerdict_next` reads. -/
theorem legCtlT_eq_legCtl
    (hreg : ¬∃ u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      v = RF.cell u)
    (j : Fin dt.nv) (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (sem₀ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    dt.legCtlT (v := v) (aT := aT) RF hord mV j st tOf
        (dt.semCastT RF (dt.varAt j) st v mV sem₀) f₀ =
      dt.legCtl (v := v) (aT := aT) RF hord mV j st tOf sem₀ f₀ := by
  have hSE : dt.ScratchEq
      (dt.varStE RF hord (dt.varAt j) st v mV (dt.semCastT RF (dt.varAt j) st v mV sem₀)
        (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT)
      (dt.roundSt st (mV aT)) :=
    (dt.scratchEq_roundEndSt RF (dt.varAt j) _ v _).trans
      (dt.scratchEq_varRdSt st _ (mV aT))
  rw [legCtlT, legCtl,
    dt.varFXT_eq_roundFX RF hord (dt.varAt j) st mV sem₀ hreg
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT,
    dt.varFMT_eq_varFM RF hord (dt.varAt j) st mV sem₀ hreg
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT, hSE.back hreg]
  rfl

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **One spine position's leg**: from the dispatch's landing one cell
right of the marker, back to it, through the variable's whole machinery,
and out through the written exit — the stage bit at the marker now the
machinery's verdict, the phase the next checkpoint. -/
theorem varLeg_run (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (t' : dt.X.Tag),
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
    (hsav : st.sav = v) (htgt : st.tgt = v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j) (dt.roundSt st (mV a))
          (dt.kindOf (dt.varAt j) b))
    (hDom : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ))
          (dt.legCtl (v := v) (aT := aT) RF hord mV j st tOf semOf f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.postVarSt v st (mV aT) (dt.varList.get j)
              ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
                (dt.legCtl (v := v) (aT := aT) RF hord mV j st tOf semOf f₀))))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  -- the phase embedding and rule-name injection of this position
  set embJ : dt.VarPhF (dt.varAt j) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  -- the rules, in the machinery's own form
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (.evalP (.chk j.succ)) i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  -- the rules, in the spine layer's form
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (.evalP (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  -- the walk back to the marker
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  -- the machinery
  have hmach := dt.varMachine_run RF hord (dt.varAt j) st hrulesJ hR hlin htop
    hbot hwork hv hvi hwkSt TestOf hcompatOf tOf hbotV htopV mV hmV0 hIncr
    hTestT hTestF hmir hbotSt hsav htgt semOf hDom hwitOf hTestOf f₀
  -- the written exit
  have hns : (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit (laidFile RF hord) hrulesV hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (f := dt.legCtl (v := v) (aT := aT) RF hord mV j st tOf semOf f₀)
    (dt.varBg_back RF hord hlin htop (dt.roundSt st (mV aT)) hwkSt) hns
    (fun r hr => dt.back_postVarSt_off RF v r hr)
    (dt.back_postVarSt_v RF v)
  exact (Relation.ReflTransGen.single hback).trans
    (hmach.trans (Relation.ReflTransGen.single hexit))

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **One spine position's leg — threaded**: as
`DescriptiveComplexity.Draw.Data.varLeg_run` without the boundary
hypotheses `hsav`/`htgt`, which the sweep cannot supply at more than one
address. The leg ends in
`DescriptiveComplexity.Draw.Data.legStT`, the machinery's own exit state
with the stage bit written at the marker. -/
theorem varLeg_run_thread (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (t' : dt.X.Tag),
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (hDom : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ))
          (dt.legCtlT (aT := aT) RF hord mV j st tOf semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (.evalP (.chk j.succ)) i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf :=
                (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt :=
                (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (.evalP (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  -- the walk back to the marker
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  -- the machinery, at the states its own thread produces
  have hmach := dt.varMachine_run_thread RF hord (dt.varAt j) st hrulesJ hR hlin
    htop hbot hwork hv hvi hwkSt TestOf hcompatOf tOf hbotV htopV mV hmV0 hIncr
    hTestT hTestF hmir hbotSt semT hDom hwitOf hTestOf f₀
  -- the loop's exit state, and the register it holds
  set stE := dt.varStE RF hord (dt.varAt j) st v mV semT
    (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT with hstE
  have hvalE : stE.val = mV aT := by
    rw [hstE]; exact dt.varStE_val RF hord (dt.varAt j) st mV semT _ aT
  have hwkE : stE.wk = fun r => r = v := by
    rw [hstE, varStE]
    refine ((dt.roundEndSt_fields RF (dt.varAt j) _ v _).1).trans ?_
    exact ((dt.varStT_fields RF hord (dt.varAt j) st mV semT
      (dt.varFG (PR := PR) RF (dt.varAt j) st v tOf f₀) aT).1).trans hwkSt
  have hround : dt.roundSt stE (mV aT) = stE := hvalE ▸ dt.roundSt_val stE
  -- the written exit
  have hns : (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit (laidFile RF hord) hrulesV hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (f := dt.legCtlT (aT := aT) RF hord mV j st tOf semT f₀)
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le stE)
    (rest' := dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.legStT (aT := aT) RF hord mV j st tOf semT f₀))
    (mval := mV aT)
    (hvalE ▸ dt.varBg_back RF hord hlin htop stE hwkE) hns
    (fun r hr => (dt.back_postVarSt_off RF v r hr).trans
      (congrArg (fun X => dt.back RF.cell PR.zero PR.one dt.dd0Le X r) hround))
    ((dt.back_postVarSt_v RF v).trans
      (congrArg (fun X => Function.update
        (dt.back RF.cell PR.zero PR.one dt.dd0Le X v) _ _) hround))
  exact (Relation.ReflTransGen.single hback).trans
    (hmach.trans (Relation.ReflTransGen.single hexit))

include hrules hR hlin htop hbot hv hvi hord in
/-- **One spine position's leg at a junk address**: the walk-back, the
machinery's failing gates, and the erased stage slot at the marker — the
verdict `False`, the VAL register untouched. -/
theorem varLegFail_run (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (htagOf : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.dspTagOf PR.zero PR.one
        (wmBlk st.mir
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)) = tOf ℓ)
    (ℓ₀ : Fin (dt.arOf (dt.varAt j)))
    (hTestLt : ∀ ℓ : Fin (dt.arOf (dt.varAt j)), (ℓ : ℕ) < (ℓ₀ : ℕ) →
      ∀ u, TestOf ℓ u)
    {u₀ : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd}
    (hfail : ¬TestOf ℓ₀ u₀) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ))
          (dt.failCtl (PR := PR) (v := v) RF (dt.varAt j) st tOf ℓ₀
            ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
              (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.postVarSt v st st.val (dt.varList.get j) False))
          st.val) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (.evalP (.chk j.succ)) i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (.evalP (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  have hupd : dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.postVarSt v st st.val (dt.varList.get j) False) v =
      Function.update (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)
        (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot PR.zero := by
    have h := dt.back_postVarSt_v (zero := PR.zero) (one := PR.one) RF v
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False)
    rw [bitVal_neg not_false] at h
    exact h
  have hmach := dt.varMachineFail_run RF hord (dt.varAt j) st hrulesJ hR hlin
    htop hbot hv hvi hwkSt TestOf hcompatOf tOf htagOf ℓ₀ hTestLt hfail f₀
    (rest' := dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.postVarSt v st st.val (dt.varList.get j) False))
    (fun r hr => dt.back_postVarSt_off RF v r hr) hupd
  exact (Relation.ReflTransGen.single hback).trans hmach

include hrules hR hlin htop hbot hv hvi hord in
/-- **One spine position's leg at a shaped but ungated address**: the
walk-back, the whole gate sequence — every file test passing, the total
dispatch carrying every block through — the clear flag at the verdict
checkpoint, and the erased stage slot at the marker: the verdict `False`,
the VAL register untouched. With
`DescriptiveComplexity.Draw.Data.varLeg_run` and
`DescriptiveComplexity.Draw.Data.varLegFail_run` this covers **every**
address the sweep visits. -/
theorem varLegUngated_run (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (htagOf : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.dspTagOf PR.zero PR.one
        (wmBlk st.mir
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)) = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (ℓ₀ : Fin (dt.arOf (dt.varAt j)))
    (hbad : ¬((∀ t' : dt.X.Tag,
        wmBlk st.mir
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ₀) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
          (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ₀) ∧
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ₀, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ₀) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)))))
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ))
          (dt.ungatedCtl (PR := PR) (v := v) RF (dt.varAt j) st tOf
            ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
              (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.postVarSt v st st.val (dt.varList.get j) False))
          st.val) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (.evalP (.chk j.succ)) i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmb (.sub (Sum.inl ⟨j, i⟩)) ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (.evalP (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inl ⟨j, i⟩)) ρ
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  have hupd : dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.postVarSt v st st.val (dt.varList.get j) False) v =
      Function.update (dt.back RF.cell PR.zero PR.one dt.dd0Le st v)
        (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot PR.zero := by
    have h := dt.back_postVarSt_v (zero := PR.zero) (one := PR.one) RF v
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False)
    rw [bitVal_neg not_false] at h
    exact h
  have hmach := dt.varMachineUngated_run RF hord (dt.varAt j) st hrulesJ hR hlin
    htop hbot hv hvi hwkSt TestOf hcompatOf tOf htagOf hTestOf ℓ₀ hbad
    f₀
    (rest' := dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.postVarSt v st st.val (dt.varList.get j) False))
    (fun r hr => dt.back_postVarSt_off RF v r hr) hupd
  exact (Relation.ReflTransGen.single hback).trans hmach

/-! ### The output's leg

The out machinery is the same shape at `vi := none`, entered by the walk
home after a passed convergence sweep, its exit the accepting phase. Its
stage slot is the working-cell marker itself, so an accepting verdict's
write is idempotent — the tape after the leg is the machinery's own end
tape. -/

/-- **The VAL-loop thread of the output's leg**, at the entry-wrapped
control. -/
noncomputable def outFM
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none (dt.roundSt st (mV a))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : ιV → dt.CtlIx → A :=
  dt.varFM RF hord none st v mV semOf
    (dt.gatesFs RF PR.zero PR.one none st v
      (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag =>
          (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      tOf (dt.varArgsOf PR.zero PR.one none).enterBlockSt
      ((dt.varArgsOf PR.zero PR.one none).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
      (dt.arOf (none : dt.VarIx)))

/-- **The control after the output's leg**: the out machinery's exit
fold. -/
noncomputable def outCtl
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none (dt.roundSt st (mV a))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one none).postFold
    (dt.roundFX RF hord none st v mV semOf
      (dt.varFM RF hord none st v mV semOf
        (dt.gatesFs RF PR.zero PR.one none st v
          (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
          dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag =>
              (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim)
          tOf (dt.varArgsOf PR.zero PR.one none).enterBlockSt
          ((dt.varArgsOf PR.zero PR.one none).enterSt f₀
            (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
          (dt.arOf (none : dt.VarIx))) aT) aT)
    (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The output's leg**: from the walk home's landing one cell right of
the marker, back to it, through the out machinery, and — the verdict
holding — out into the accepting phase, the marker rewritten with the
value it already carries. -/
theorem outLeg_run
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
    (hsav : st.sav = v) (htgt : st.tgt = v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none (dt.roundSt st (mV a))
          (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.outCtl (v := v) (aT := aT) RF hord mV st tOf semOf f₀)) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntryOut))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt .acceptP
          (dt.outCtl (v := v) (aT := aT) RF hord mV st tOf semOf f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  set embO : dt.VarPhF (none : dt.VarIx) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inr p)) with hembO
  have hrulesJ : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmb (.sub (Sum.inr i)) ρ) =
        dt.varRuleF PR.zero PR.one none
          (dt.varArgsOf PR.zero PR.one none) embO .acceptP i ρ :=
    fun i ρ => hrules (.sub (Sum.inr i)) ρ
  have hrulesV : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmb (.sub (Sum.inr i)) ρ) =
        dt.varRule PR.zero PR.one embO
          (dt.gatesRule (one := PR.one) (v := (none : dt.VarIx))
            (emb := fun p => embO (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one none).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one none).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one none).enterBlockSt)
            (failPh := embO .vchk1) (exitPh := embO .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embO (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one none).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one none).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterIGSt)
              (exitPh := embO (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one none).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterAtomSt)
              (exitPh := embO .mchk1))
            (pxEntry := embO (.matrixP (.matP (.chk 0))))
            (exitPh := embO .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one none).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one none).allFlag))
          (embO (.gatesP (.chk 0))) (embO (.matrixP (.igP (.chk 0)))) .acceptP
          (dt.varArgsOf PR.zero PR.one none).newSlot
          (dt.varArgsOf PR.zero PR.one none).gateFlag
          (dt.varArgsOf PR.zero PR.one none).accBit
          (dt.varArgsOf PR.zero PR.one none).enterSt
          (dt.varArgsOf PR.zero PR.one none).initSt
          (dt.varArgsOf PR.zero PR.one none).postFold
          (dt.varArgsOf PR.zero PR.one none).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inr i)) ρ
  -- the walk back to the marker
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  -- the machinery
  have hmach := dt.varMachine_run RF hord none st hrulesJ hR hlin htop
    hbot hwork hv hvi hwkSt TestOf hcompatOf tOf hbotV htopV mV hmV0 hIncr
    hTestT hTestF hmir hbotSt hsav htgt semOf hDom hwitOf hTestOf f₀
  -- the accepting exit: the marker rewritten with its own value
  have hupd : dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v =
      Function.update
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)
        ((dt.varArgsOf PR.zero PR.one none).newSlot)
        (bitVal PR.zero PR.one
          ((dt.varArgsOf PR.zero PR.one none).accBit
            (dt.outCtl (v := v) (aT := aT) RF hord mV st tOf semOf f₀))) := by
    funext sl
    by_cases hs : sl = (dt.varArgsOf PR.zero PR.one none).newSlot
    · subst hs
      rw [Function.update_self]
      change dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v
        Slot.wk = _
      rw [back_wk]
      change bitVal PR.zero PR.one (st.wk v) = _
      rw [hwkSt, bitVal_pos rfl, bitVal_pos hacc]
    · rw [Function.update_of_ne hs]
  have hns : (dt.varArgsOf PR.zero PR.one (none : dt.VarIx)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit (laidFile RF hord) hrulesV hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (f := dt.outCtl (v := v) (aT := aT) RF hord mV st tOf semOf f₀)
    (dt.varBg_back RF hord hlin htop (dt.roundSt st (mV aT)) hwkSt) hns
    (fun _ _ => rfl) hupd
  exact (Relation.ReflTransGen.single hback).trans
    (hmach.trans (Relation.ReflTransGen.single hexit))

/-- **The state the output's leg ends at — threaded**: the machinery's own
exit state, the accepting write at the marker being idempotent. -/
noncomputable def outStE
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none
          (dt.matSt none (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  dt.varStE RF hord none st v mV semT (dt.varFG (PR := PR) RF none st v tOf f₀) aT

/-- **The control after the output's leg — threaded**: the out machinery's
exit fold, at the states its own thread produces. -/
noncomputable def outCtlT
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none
          (dt.matSt none (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one none).postFold
    (dt.varFXT RF hord none st v mV semT (dt.varFG (PR := PR) RF none st v tOf f₀) aT)
    (dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀) v)

include hord in
omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx] in
/-- **The output's threaded leg computes the unthreaded fold**: as
`DescriptiveComplexity.Draw.Data.legCtlT_eq_legCtl` at the output
variable — the VAL loop is the unthreaded loop, its last round the
unthreaded round, and the exit state differs from the round state in SAV and
TARGET alone, which the background does not see off the register file. This
is what makes `outLeg_run_thread`'s `hacc` the verdict
`DescriptiveComplexity.Draw.Data.accVerdict_out` reads. -/
theorem outCtlT_eq_outCtl
    (hreg : ¬∃ u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd,
      v = RF.cell u)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (sem₀ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none (dt.roundSt st (mV a))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) :
    dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf
        (dt.semCastT RF none st v mV sem₀) f₀ =
      dt.outCtl (v := v) (aT := aT) RF hord mV st tOf sem₀ f₀ := by
  have hSE : dt.ScratchEq
      (dt.varStE RF hord none st v mV (dt.semCastT RF none st v mV sem₀)
        (dt.varFG (PR := PR) RF none st v tOf f₀) aT)
      (dt.roundSt st (mV aT)) :=
    (dt.scratchEq_roundEndSt RF none _ v _).trans
      (dt.scratchEq_varRdSt st _ (mV aT))
  rw [outCtlT, outStE, outCtl,
    dt.varFXT_eq_roundFX RF hord none st mV sem₀ hreg
      (dt.varFG (PR := PR) RF none st v tOf f₀) aT,
    dt.varFMT_eq_varFM RF hord none st mV sem₀ hreg
      (dt.varFG (PR := PR) RF none st v tOf f₀) aT, hSE.back hreg]
  rfl

open Classical in
/-- **The state the output's leg leaves, whatever its verdict**: the
machinery's exit state with the marker rewritten by the accepting bit — so
the marker survives a *true* verdict and is cleared by a false one, which is
what makes a false output halt and reject. -/
noncomputable def outStA
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none
          (dt.matSt none (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  { dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀ with
    wk := (fun r => r = v ∧ (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)) }

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The output's leg — threaded, whatever the verdict**: as
`DescriptiveComplexity.Draw.Data.outLeg_run` without the boundary
hypotheses `hsav`/`htgt`, which nothing supplies at the end of a sweep — the
advance refreshes the marker and the mirror, not the two scratch registers —
and without any assumption on the verdict. The leg ends in the accepting
phase either way; what the verdict decides is the *bit* the exit writes at
the marker (`DescriptiveComplexity.Draw.Data.outStA`), and with it whether
the machine's accepting predicate holds of the state it stops in. -/
theorem outLeg_run_verdict
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none
          (dt.matSt none (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntryOut))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt .acceptP
          (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  set embO : dt.VarPhF (none : dt.VarIx) → OuterPh (EvalPh dt.nv dt.PMF) :=
    fun p => .evalP (.sub (Sum.inr p)) with hembO
  have hrulesJ : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmb (.sub (Sum.inr i)) ρ) =
        dt.varRuleF PR.zero PR.one none
          (dt.varArgsOf PR.zero PR.one none) embO .acceptP i ρ :=
    fun i ρ => hrules (.sub (Sum.inr i)) ρ
  have hrulesV : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmb (.sub (Sum.inr i)) ρ) =
        dt.varRule PR.zero PR.one embO
          (dt.gatesRule (one := PR.one) (v := (none : dt.VarIx))
            (emb := fun p => embO (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one none).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one none).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one none).enterBlockSt)
            (failPh := embO .vchk1) (exitPh := embO .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embO (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one none).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one none).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterIGSt)
              (exitPh := embO (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one none).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterAtomSt)
              (exitPh := embO .mchk1))
            (pxEntry := embO (.matrixP (.matP (.chk 0))))
            (exitPh := embO .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one none).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one none).allFlag))
          (embO (.gatesP (.chk 0))) (embO (.matrixP (.igP (.chk 0)))) .acceptP
          (dt.varArgsOf PR.zero PR.one none).newSlot
          (dt.varArgsOf PR.zero PR.one none).gateFlag
          (dt.varArgsOf PR.zero PR.one none).accBit
          (dt.varArgsOf PR.zero PR.one none).enterSt
          (dt.varArgsOf PR.zero PR.one none).initSt
          (dt.varArgsOf PR.zero PR.one none).postFold
          (dt.varArgsOf PR.zero PR.one none).storeCarry i ρ :=
    fun i ρ => hrules (.sub (Sum.inr i)) ρ
  -- the walk back to the marker
  have hback := dt.step_var_back (laidFile RF hord) hrulesV hR hlin hvi
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [back_wk, hwkSt])
  -- the machinery, at the states its own thread produces
  have hmach := dt.varMachine_run_thread RF hord none st hrulesJ hR hlin htop
    hbot hwork hv hvi hwkSt TestOf hcompatOf tOf hbotV htopV mV hmV0 hIncr
    hTestT hTestF hmir hbotSt semT hDom hwitOf hTestOf f₀
  -- the loop's exit state, and the register it holds
  set stE := dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀ with hstE
  have hvalE : stE.val = mV aT := by
    rw [hstE]; exact dt.varStE_val RF hord none st mV semT _ aT
  have hwkE : stE.wk = fun r => r = v := by
    rw [hstE, outStE, varStE]
    refine ((dt.roundEndSt_fields RF none _ v _).1).trans ?_
    exact ((dt.varStT_fields RF hord none st mV semT
      (dt.varFG (PR := PR) RF none st v tOf f₀) aT).1).trans hwkSt
  have hround : dt.roundSt stE (mV aT) = stE := hvalE ▸ dt.roundSt_val stE
  -- the exit state: the same tape with the marker rewritten by the verdict
  have hA : dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀ =
      { stE with wk := (fun r => r = v ∧
        (dt.varArgsOf PR.zero PR.one none).accBit
          (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)) } := by
    rw [hstE]; rfl
  have hslot : ∀ (X : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
      (w : (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) →
        Prop)
      (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
      (sl : dt.SlotIx), sl ≠ Slot.wk →
      dt.back RF.cell PR.zero PR.one dt.dd0Le { X with wk := w } r sl =
        dt.back RF.cell PR.zero PR.one dt.dd0Le X r sl := by
    intro X w r sl hsl
    cases sl <;> first
      | exact absurd rfl hsl
      | rfl
  have hoff : ∀ r, r ≠ v →
      dt.back RF.cell PR.zero PR.one dt.dd0Le
        (dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀) r =
      dt.back RF.cell PR.zero PR.one dt.dd0Le stE r := by
    intro r hr
    rw [hA]
    funext sl
    by_cases hsl : sl = Slot.wk
    · subst hsl
      rw [back_wk, back_wk, hwkE]
      exact bitVal_congr (iff_of_false (fun hc => hr hc.1) hr)
    · exact hslot _ _ r sl hsl
  have hupd : dt.back RF.cell PR.zero PR.one dt.dd0Le
        (dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀) v =
      Function.update (dt.back RF.cell PR.zero PR.one dt.dd0Le stE v)
        ((dt.varArgsOf PR.zero PR.one none).newSlot)
        (bitVal PR.zero PR.one
          ((dt.varArgsOf PR.zero PR.one none).accBit
            (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀))) := by
    rw [hA]
    funext sl
    by_cases hs : sl = (dt.varArgsOf PR.zero PR.one none).newSlot
    · subst hs
      rw [Function.update_self]
      exact bitVal_congr (and_iff_right rfl)
    · rw [Function.update_of_ne hs]
      exact hslot _ _ v sl (fun hc => hs hc)
  have hns : (dt.varArgsOf PR.zero PR.one (none : dt.VarIx)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit (laidFile RF hord) hrulesV hR hlin
    (isLinOrd_laidFile_le hlin) (fun y => (hord _ y).mp (hbot y)) hv hvi
    (f := dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)
    (rest := dt.back RF.cell PR.zero PR.one dt.dd0Le stE)
    (rest' := dt.back RF.cell PR.zero PR.one dt.dd0Le
      (dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀))
    (mval := mV aT)
    (hvalE ▸ dt.varBg_back RF hord hlin htop stE hwkE) hns
    hoff hupd
  exact (Relation.ReflTransGen.single hback).trans
    (hmach.trans (Relation.ReflTransGen.single hexit))

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The output's leg — threaded, the verdict holding**: the special case of
`DescriptiveComplexity.Draw.Data.outLeg_run_verdict` in which the accepting
write at the marker is *idempotent*, so the leg ends at the machinery's own
exit state and nothing of the tape moves. -/
theorem outLeg_run_thread
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st)
          st.mir (RF.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = v) (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.KindSem PR.zero PR.one none
          (dt.matSt none (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk st.mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntryOut))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt .acceptP
          (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  have hwkE : (dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀).wk =
      fun r => r = v := by
    rw [outStE, varStE]
    refine ((dt.roundEndSt_fields RF none _ v _).1).trans ?_
    exact ((dt.varStT_fields RF hord none st mV semT
      (dt.varFG (PR := PR) RF none st v tOf f₀) aT).1).trans hwkSt
  have heq : dt.outStA (v := v) (aT := aT) RF hord mV st tOf semT f₀ =
      dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀ := by
    have hw : (fun r => r = v ∧ (dt.varArgsOf PR.zero PR.one none).accBit
        (dt.outCtlT (v := v) (aT := aT) RF hord mV st tOf semT f₀)) =
        (dt.outStE (v := v) (aT := aT) RF hord mV st tOf semT f₀).wk := by
      rw [hwkE]
      exact funext fun r => propext (and_iff_left hacc)
    simp only [outStA, hw]
  exact heq ▸ dt.outLeg_run_verdict RF hord hrules hR hlin htop hbot hwork hv hvi
    hbotV htopV mV hmV0 hIncr hTestT hTestF st hwkSt TestOf hcompatOf tOf
    hwitOf hmir hbotSt semT hDom hTestOf f₀

/-! ### Which leg a position takes

A position's machinery has three runs, by what its gates do:
`DescriptiveComplexity.Draw.Data.varLeg_run_thread` when every block is
well shaped *and* the tags and the domain sentence agree,
`DescriptiveComplexity.Draw.Data.varLegUngated_run` when the blocks are
well shaped but the verdict flag is cleared, and
`DescriptiveComplexity.Draw.Data.varLegFail_run` when a block fails the
shape test — which is the one that needs a witness, and a *least* one, so
that the blocks before it have run. -/

/-- **The least failing index, with a witness**: from a family that is not
everywhere true, the first index at which it fails, together with a value
at which it does and the fact that every earlier index is everywhere
true. This is `DescriptiveComplexity.Draw.Data.varLegFail_run`'s
`ℓ₀`/`hTestLt`/`hfail` produced from the plain negation, which is all a
per-address case split has. -/
theorem exists_least_fail {n : ℕ} {α : Sort _} {T : Fin n → α → Prop}
    (h : ¬∀ (ℓ : Fin n) (u : α), T ℓ u) :
    ∃ (ℓ₀ : Fin n) (u₀ : α), ¬T ℓ₀ u₀ ∧
      ∀ ℓ : Fin n, (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, T ℓ u := by
  classical
  have hex : ∃ k : ℕ, ∃ hk : k < n, ∃ u : α, ¬T ⟨k, hk⟩ u := by
    by_contra hc
    exact h fun ℓ u => by
      by_contra hu
      exact hc ⟨(ℓ : ℕ), ℓ.isLt, u, by rwa [Fin.eta]⟩
  obtain ⟨hk, u₀, hfail⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hk⟩, u₀, hfail, fun ℓ hlt u => ?_⟩
  by_contra hu
  exact Nat.not_lt.mpr (Nat.find_le ⟨ℓ.isLt, u, by rwa [Fin.eta]⟩) hlt

/-- **The shape test the gates run**, at a position and a state: the
per-cell question a block's `TestKit` asks, which is what tells the third
leg from the other two. -/
def shapeAt (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (ℓ : Fin (dt.arOf (dt.varAt j)))
    (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd) : Prop :=
  dt.wellShapedG PR.zero PR.one
    (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
    (PR.passTracksAt RF.cell Slot.mir (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.mir
      (RF.cell u))

/-- **The tag a block's witness cells name**, as the machine reads it —
so `htagOf` is `rfl` at this choice. -/
noncomputable def tagAt (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (ℓ : Fin (dt.arOf (dt.varAt j))) : dt.X.Tag :=
  dt.dspTagOf PR.zero PR.one
    (wmBlk st.mir
      (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) :
        Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))

/-- **The other half of a block's gate**: its tag witnesses are one-hot at
the tag they name, and the expansion's domain sentence holds of the point
the block decodes. Together with
`DescriptiveComplexity.Draw.Data.shapeAt` this is the gates' verdict. -/
def tagDomAt (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (ℓ : Fin (dt.arOf (dt.varAt j))) : Prop :=
  (∀ t' : dt.X.Tag,
      wmBlk st.mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = dt.tagAt (PR := PR) j st ℓ) ∧
    ExpExpansion.DomHolds (X := dt.X)
      (dt.tagAt (PR := PR) j st ℓ, decRho dt.ly PR.zero PR.one
        (wmBlk st.mir
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)))

/-- **A position is gated** when every block passes both halves. -/
def gatedAt (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF))) : Prop :=
  (∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u, dt.shapeAt (PR := PR) RF j st ℓ u) ∧
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)), dt.tagDomAt (PR := PR) j st ℓ

open Classical in
/-- **The state one position's leg leaves, whichever leg it takes**: the
machinery's own exit at a gated position, and the entry state with the
stage bit erased at the two ungated ones — which agree on the tape and
differ only in their control. -/
noncomputable def legStB (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)) :=
  if hg : dt.gatedAt (PR := PR) RF j st then
    dt.legStT (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st) (semT hg) f₀
  else dt.postVarSt v st st.val (dt.varList.get j) False

open Classical in
/-- **The control one position's leg leaves**: the machinery's fold at a
gated position, the ungated exit when the blocks are well shaped but a tag
or the domain fails, and the failing gates' exit — at the *least* badly
shaped block — otherwise. -/
noncomputable def legCtlB (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  if hg : dt.gatedAt (PR := PR) RF j st then
    dt.legCtlT (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st) (semT hg) f₀
  else if hs : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      dt.shapeAt (PR := PR) RF j st ℓ u then
    dt.ungatedCtl (PR := PR) (v := v) RF (dt.varAt j) st (dt.tagAt (PR := PR) j st)
      ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))
  else
    dt.failCtl (PR := PR) (v := v) RF (dt.varAt j) st (dt.tagAt (PR := PR) j st)
      (exists_least_fail (T := dt.shapeAt (PR := PR) RF j st) hs).choose
      ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
        (dt.back RF.cell PR.zero PR.one dt.dd0Le st v))

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [Finite ιV] in
/-- **What a leg leaves alone, whichever leg it takes**: the ungated legs
never enter the VAL loop, so they touch nothing but the stage bit, and the
gated one is `DescriptiveComplexity.Draw.Data.legStT_fields`. The `val`
register is left out on purpose — it is the loop's top at a gated
position and the entry state's at the other two. -/
theorem legStB_fields (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    (dt.legStB (aT := aT) RF hord mV j st semT f₀).mir = st.mir ∧
      (dt.legStB (aT := aT) RF hord mV j st semT f₀).wk = st.wk ∧
      (dt.legStB (aT := aT) RF hord mV j st semT f₀).bot = st.bot ∧
      (dt.legStB (aT := aT) RF hord mV j st semT f₀).old = st.old ∧
      (dt.legStB (aT := aT) RF hord mV j st semT f₀).ltp = st.ltp := by
  classical
  by_cases hg : dt.gatedAt (PR := PR) RF j st
  · rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_pos hg]
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := dt.legStT_fields (aT := aT) RF hord mV j st
      (dt.tagAt (PR := PR) j st) (semT hg) f₀
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_neg hg]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

open Classical in
/-- **The stage bit one position writes**, whichever leg it takes: the
machinery's verdict at a gated position, `False` at the two ungated ones,
which is what the stage dictionary holds where the blocks encode no
point. -/
noncomputable def legBitB (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : Prop :=
  if hg : dt.gatedAt (PR := PR) RF j st then
    (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
      (dt.legCtlT (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st) (semT hg) f₀)
  else False

omit [Finite R] [Finite (OuterPh (EvalPh dt.nv dt.PMF))] [Finite dt.KIx]
  [Finite ιV] in
open Classical in
/-- **What a leg writes**: its variable's cell at the marker, and nothing
else — the same equation whichever leg it takes, since the VAL loop
threads the two scratch registers alone
(`DescriptiveComplexity.Draw.Data.varStE_new`) and the ungated legs
write the stage bit directly. This is the branched twin of
`DescriptiveComplexity.Draw.Data.new_postVarSt`, and the only thing the
spine's dictionary lemmas need of a leg. -/
theorem legStB_new (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) (i' : dt.d.B.ι)
    (r : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) :
    (dt.legStB (aT := aT) RF hord mV j st semT f₀).new i' r =
      (if i' = dt.varList.get j ∧ r = v then
        dt.legBitB (aT := aT) RF hord mV j st semT f₀ else st.new i' r) := by
  classical
  by_cases hg : dt.gatedAt (PR := PR) RF j st
  · rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_pos hg,
      show dt.legBitB (aT := aT) RF hord mV j st semT f₀ = _ from dif_pos hg, legStT]
    exact congrArg
      (fun N : dt.d.B.ι →
          (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop) →
          Prop =>
        if i' = dt.varList.get j ∧ r = v then
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
            (dt.legCtlT (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st)
              (semT hg) f₀)
        else N i' r)
      (dt.varStE_new RF hord (dt.varAt j) st mV (semT hg)
        (dt.varFG (PR := PR) RF (dt.varAt j) st v (dt.tagAt (PR := PR) j st) f₀)
        aT)
  · rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_neg hg,
      show dt.legBitB (aT := aT) RF hord mV j st semT f₀ = _ from dif_neg hg]
    rfl

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **One spine position's leg, whichever leg it takes**: the three runs
of the machinery under one statement, the case split on the gates made
once and for all. This is what a sweep needs, since it visits junk
addresses and gated ones alike. -/
theorem varLegB_run (j : Fin dt.nv)
    (st : TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (hwkSt : st.wk = fun r => r = v) (hmir : st.mir = v)
    (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : dt.gatedAt (PR := PR) RF j st →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j) (dt.varRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt st p (mV a)) v (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ))
          (dt.legCtlB (aT := aT) RF hord mV j st semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le
            (dt.legStB (aT := aT) RF hord mV j st semT f₀))
          (dt.legStB (aT := aT) RF hord mV j st semT f₀).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  by_cases hg : dt.gatedAt (PR := PR) RF j st
  · -- gated: the whole machinery, threaded
    have hval : (dt.legStT (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st)
        (semT hg) f₀).val = mV aT :=
      (dt.legStT_fields (aT := aT) RF hord mV j st (dt.tagAt (PR := PR) j st)
        (semT hg) f₀).2.2.2.2.2
    rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_pos hg,
      show dt.legCtlB (aT := aT) RF hord mV j st semT f₀ = _ from dif_pos hg, hval]
    exact dt.varLeg_run_thread RF hord hrules hR hlin htop hbot hwork hv hvi hbotV
      htopV mV hmV0 hIncr hTestT hTestF j st hwkSt (dt.shapeAt (PR := PR) RF j st)
      (fun _ _ => Iff.rfl) (dt.tagAt (PR := PR) j st) (fun ℓ => (hg.2 ℓ).1) hmir hbotSt
      (semT hg) (fun ℓ => (hg.2 ℓ).2) hg.1 f₀
  · rw [show dt.legStB (aT := aT) RF hord mV j st semT f₀ = _ from dif_neg hg]
    by_cases hs : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u,
        dt.shapeAt (PR := PR) RF j st ℓ u
    · -- well shaped, but a tag or the domain fails: the ungated exit
      have hbad : ∃ ℓ₀, ¬dt.tagDomAt (PR := PR) j st ℓ₀ := by
        by_contra hc
        exact hg ⟨hs, fun ℓ => not_not.mp (fun h => hc ⟨ℓ, h⟩)⟩
      obtain ⟨ℓ₀, hℓ₀⟩ := hbad
      rw [show dt.legCtlB (aT := aT) RF hord mV j st semT f₀ = _ from
        (dif_neg hg).trans (dif_pos hs)]
      exact dt.varLegUngated_run RF hord hrules hR hlin htop hbot hv hvi j st
        hwkSt (dt.shapeAt (PR := PR) RF j st) (fun _ _ => Iff.rfl)
        (dt.tagAt (PR := PR) j st) (fun _ => rfl) hs ℓ₀ hℓ₀ f₀
    · -- a block is badly shaped: the failing gates, at the least one
      obtain ⟨u₀, hfail, hlt⟩ :=
        (exists_least_fail (T := dt.shapeAt (PR := PR) RF j st) hs).choose_spec
      rw [show dt.legCtlB (aT := aT) RF hord mV j st semT f₀ = _ from
        (dif_neg hg).trans (dif_neg hs)]
      exact dt.varLegFail_run RF hord hrules hR hlin htop hbot hv hvi j st hwkSt
        (dt.shapeAt (PR := PR) RF j st) (fun _ _ => Iff.rfl) (dt.tagAt (PR := PR) j st)
        (fun _ => rfl) _ hlt hfail f₀

/-! ### The spine -/

omit [Finite dt.KIx] in
include hrules hR hlin hbot hv hvi in
/-- **The spine over given legs**: `eval_run` at the concrete tape
presentation, each position's machinery an arbitrary run — the caller
plugs in `DescriptiveComplexity.Draw.Data.varLeg_run` at a gated address
and `DescriptiveComplexity.Draw.Data.varLegFail_run` at a junk one. -/
theorem evalSpineLegs_run
    (stOf : Fin (dt.nv + 1) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hVar : ∀ j : Fin dt.nv, Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx
        dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.sub (dt.smEntry j)))
          (fsOf j.castSucc)), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ)) (fsOf j.succ)),
        Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf j.succ))
          (stOf j.succ).val) (PR.syElt PR.blank)⟩) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  exact dt.eval_run RF.toIx (fun i ρ => hrules i ρ) hR hlin hlin hbot hv hvi
    (restOf := fun k => dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [back_wk, hwkOf k]) (fun k r => rfl) fsOf hVar

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine, fully instantiated**: from the checkpoint
before the first variable to the checkpoint after the last, one whole
machinery per position — each leg
`DescriptiveComplexity.Draw.Data.varLeg_run`, the tape and control
threads given as families with one cover equation per position. -/
theorem evalSpine_run
    (stOf : Fin (dt.nv + 1) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (TestOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).mir (RF.cell u)) ↔ TestOfJ j ℓ u)
    (tOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (t' : dt.X.Tag),
      wmBlk (stOf j.castSucc).mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOfJ j ℓ)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (hsavOf : ∀ j : Fin dt.nv, (stOf j.castSucc).sav = v)
    (htgtOf : ∀ j : Fin dt.nv, (stOf j.castSucc).tgt = v)
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.roundSt (stOf j.castSucc) (mV a)) (dt.kindOf (dt.varAt j) b))
    (hDomJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))),
      ExpExpansion.DomHolds (X := dt.X)
        (tOfJ j ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (stOf j.castSucc).mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      TestOfJ j ℓ u)
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.postVarSt v (stOf j.castSucc) (mV aT) (dt.varList.get j)
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.legCtl (v := v) (aT := aT) RF hord mV j (stOf j.castSucc) (tOfJ j)
            (semOfJ j) (fsOf j.castSucc))))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.legCtl (v := v) (aT := aT) RF hord mV j (stOf j.castSucc) (tOfJ j)
        (semOfJ j) (fsOf j.castSucc)) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_run RF.toIx (fun i ρ => hrules i ρ) hR hlin hlin hbot hv hvi
    (restOf := fun k => dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [back_wk, hwkOf k]) (fun k r => rfl) fsOf ?_
  intro k
  have hleg := dt.varLeg_run RF hord hrules hR hlin htop hbot hwork hv hvi hbotV
    htopV mV hmV0 hIncr hTestT hTestF k (stOf k.castSucc) (hwkOf _)
    (TestOfJ k) (hcompatOfJ k) (tOfJ k) (hwitOfJ k) (hmirOf k) (hbotOf k)
    (hsavOf k) (htgtOf k) (semOfJ k) (hDomJ k) (hTestOfJ k)
    (fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine, fully instantiated — threaded**: as
`DescriptiveComplexity.Draw.Data.evalSpine_run` with `hsavOf` and
`htgtOf` **gone**. That is the point of the whole threading: the advance
refreshes the marker and the mirror but not SAV and TARGET, so a sweep can
meet those two hypotheses at one address at most, while every other
hypothesis here is about the marker, the mirror and the tracks, which do
ride. -/
theorem evalSpine_run_thread
    (stOf : Fin (dt.nv + 1) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (TestOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) →
      Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd → Prop)
    (hcompatOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (u : Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt RF.cell Slot.mir
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf j.castSucc))
          (stOf j.castSucc).mir (RF.cell u)) ↔ TestOfJ j ℓ u)
    (tOfJ : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j)))
      (t' : dt.X.Tag),
      wmBlk (stOf j.castSucc).mir
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOfJ j ℓ)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv)
      (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.varRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (hDomJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))),
      ExpExpansion.DomHolds (X := dt.X)
        (tOfJ j ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (stOf j.castSucc).mir
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx))))
    (hTestOfJ : ∀ (j : Fin dt.nv) (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      TestOfJ j ℓ u)
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.legStT (aT := aT) RF hord mV j (stOf j.castSucc) (tOfJ j) (semTJ j)
        (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.legCtlT (aT := aT) RF hord mV j (stOf j.castSucc) (tOfJ j) (semTJ j)
        (fsOf j.castSucc)) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_run RF.toIx (fun i ρ => hrules i ρ) hR hlin hlin hbot hv hvi
    (restOf := fun k => dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [back_wk, hwkOf k]) (fun k r => rfl) fsOf ?_
  intro k
  have hleg := dt.varLeg_run_thread RF hord hrules hR hlin htop hbot hwork hv hvi
    hbotV htopV mV hmV0 hIncr hTestT hTestF k (stOf k.castSucc) (hwkOf _)
    (TestOfJ k) (hcompatOfJ k) (tOfJ k) (hwitOfJ k) (hmirOf k) (hbotOf k)
    (semTJ k) (hDomJ k) (hTestOfJ k) (fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

include hrules hR hlin htop hbot hwork hv hvi hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The evaluation's spine at an arbitrary address**: as
`DescriptiveComplexity.Draw.Data.evalSpine_run_thread` with the gates no
longer assumed to pass. Each position takes whichever of the three legs
its own gates call for, and what the caller owes is only the marker, the
mirror and the bottom mark — all of which the advance sets and every leg
leaves alone. This is the form a sweep can use, since it visits junk
addresses and gated ones alike. -/
theorem evalSpineB_run
    (stOf : Fin (dt.nv + 1) → TapeStD dt A R (OuterPh (EvalPh dt.nv dt.PMF)))
    (fsOf : Fin (dt.nv + 1) → dt.CtlIx → A)
    (hwkOf : ∀ k, (stOf k).wk = fun r => r = v)
    (hmirOf : ∀ j : Fin dt.nv, (stOf j.castSucc).mir = v)
    (hbotOf : ∀ j : Fin dt.nv,
      (stOf j.castSucc).bot = fun r => r = (fun _ => False))
    (semTJ : ∀ (j : Fin dt.nv), dt.gatedAt (PR := PR) RF j (stOf j.castSucc) →
      ∀ (p : Scratch dt A R (OuterPh (EvalPh dt.nv dt.PMF))) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.igPassP RF PR.zero PR.one (dt.varAt j)
          (dt.varRdSt (stOf j.castSucc) p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.KindSem PR.zero PR.one (dt.varAt j)
          (dt.matSt (dt.varAt j) (dt.varRdSt (stOf j.castSucc) p (mV a)) v
            (b : ℕ))
          (dt.kindOf (dt.varAt j) b))
    (hst : ∀ j : Fin dt.nv, stOf j.succ =
      dt.legStB (aT := aT) RF hord mV j (stOf j.castSucc) (semTJ j) (fsOf j.castSucc))
    (hfs : ∀ j : Fin dt.nv, fsOf j.succ =
      dt.legCtlB (aT := aT) RF hord mV j (stOf j.castSucc) (semTJ j)
        (fsOf j.castSucc)) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh dt.nv dt.PMF)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fsOf 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf 0)) (stOf 0).val)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last dt.nv)))
          (fsOf (Fin.last dt.nv))), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val
          (dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf (Fin.last dt.nv)))
          (stOf (Fin.last dt.nv)).val) (PR.syElt PR.blank)⟩ := by
  classical
  refine dt.eval_run RF.toIx (fun i ρ => hrules i ρ) hR hlin hlin hbot hv hvi
    (restOf := fun k => dt.back RF.cell PR.zero PR.one dt.dd0Le (stOf k))
    (mvOf := fun k => (stOf k).val)
    (fun k r => by rw [back_wk, hwkOf k]) (fun k r => rfl) fsOf ?_
  intro k
  have hleg := dt.varLegB_run RF hord hrules hR hlin htop hbot hwork hv hvi hbotV
    htopV mV hmV0 hIncr hTestT hTestF k (stOf k.castSucc) (hwkOf _)
    (hmirOf k) (hbotOf k) (semTJ k) (fsOf k.castSucc)
  rw [hst k, hfs k]
  exact hleg

end Leg

end Data

end Draw

end DescriptiveComplexity
