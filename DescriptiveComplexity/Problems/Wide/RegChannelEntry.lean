/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelEval
import DescriptiveComplexity.Problems.Wide.TrackWrites
import DescriptiveComplexity.Problems.Wide.RegChannelProg

/-!
# The tape the register channel hands over is the state the run reads

A program that lays its own file arrives at its evaluation with a background
built by the sweep; a program that is *handed* its file has that background from
time zero. This file says the two agree: the marks the register channel writes
are, slot for slot, what `DescriptiveComplexity.Draw.Data.ixBack` reads off the
entry state at the handed file.

Only two slots need an argument, and both are about the file's ends:

* `regFirst` – at this channel the first register is **not** the least element of
  the universe but the greatest carrying no argument block, which is why the mark
  is `DescriptiveComplexity.Draw.regSlotMark` and not
  `DescriptiveComplexity.Draw.slotMark` (`isTopNonArg_iff_least_marked`);
* `regLast` – the last register *is* the last element, the argument tags being
  the greatest (`isGreatest_iff_greatest_marked`).

Everything else is a tag decision the layout repeats (the block one-hots, the
name slots, the padding flag) or a track that starts clear.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section Entry

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [Nonempty A]
variable (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)

/-! ### The two ends of the handed file -/

omit [Fintype dt.SlotIx] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite dt.KIx] in
/-- **The element below the argument tags exists**: the elements carrying no
argument block are finitely many and not none, so one of them is greatest. -/
theorem exists_isTopNonArg : ∃ z : Univ A R' P' dt.KIx dt.dd, IsTopNonArg z := by
  obtain ⟨z, hz, hmax⟩ := exists_greatest
    (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx) (A := A) (d := dt.dd))
    (P := fun x : Univ A R' P' dt.KIx dt.dd => ∀ i, x.1 ≠ Tag.arg i)
    ⟨(Tag.sym, fun _ => Classical.arbitrary A), fun i => fun h => nomatch h⟩
  exact ⟨z, hz, hmax⟩

omit [Fintype dt.SlotIx] [Nonempty A]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **The greatest element carries an argument block**, provided there is one:
the argument tags come last (`DescriptiveComplexity.Draw.lt_arg`). -/
theorem arg_of_isGreatest [Nonempty dt.KIx] {x : Univ A R' P' dt.KIx dt.dd}
    (hx : ∀ y : Univ A R' P' dt.KIx dt.dd, tagTupleLe y x) :
    ∃ i, x.1 = Tag.arg i := by
  by_contra hc
  push Not at hc
  have hlt : x.1 < Tag.arg (Classical.arbitrary dt.KIx) := lt_arg x.1 _ hc
  rcases hx (Tag.arg (Classical.arbitrary dt.KIx), x.2) with hb | ⟨hb, -⟩
  · exact absurd hb (asymm hlt)
  · exact absurd hb (ne_of_gt hlt)

omit [Fintype dt.SlotIx] [Nonempty A]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **The first register of the handed file is the element below the argument
tags**: the channel marks the argument elements and that one, and it is the
least of them. This is the `regFirst` slot's whole content, and the reason the
mark had to change. -/
theorem isTopNonArg_iff_least_marked {Marked : Univ A R' P' dt.KIx dt.dd → Prop}
    (hmk : ∀ x, Marked x ↔ (∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)
    (hex : ∃ z : Univ A R' P' dt.KIx dt.dd, IsTopNonArg z)
    {x : Univ A R' P' dt.KIx dt.dd} (hx : Marked x) :
    IsTopNonArg x ↔ ∀ y, Marked y → tagTupleLe x y := by
  constructor
  · rintro ⟨hna, hall⟩ y hy
    rcases (hmk y).mp hy with ⟨k, hk⟩ | ⟨hyna, hyall⟩
    · refine Or.inl ?_
      rw [hk]
      exact lt_arg x.1 k hna
    · exact hyall x hna
  · intro hle
    rcases (hmk x).mp hx with ⟨k, hk⟩ | htop
    · exfalso
      obtain ⟨z, hz⟩ := hex
      have hzm : Marked z := (hmk z).mpr (Or.inr hz)
      have hlt : z.1 < x.1 := by rw [hk]; exact lt_arg z.1 k hz.1
      rcases hle z hzm with hb | ⟨hb, -⟩
      · exact absurd hb (asymm hlt)
      · exact absurd hb.symm (ne_of_lt hlt)
    · exact htop

omit [Fintype dt.SlotIx] [Nonempty A]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The last register of the handed file is the last element**: the argument
tags being the greatest, the greatest element is one of the marked ones, so
being greatest among them is being greatest. The `regLast` slot therefore needs
no change. -/
theorem isGreatest_iff_greatest_marked [Nonempty dt.KIx]
    {Marked : Univ A R' P' dt.KIx dt.dd → Prop}
    (hmk : ∀ x, Marked x ↔ (∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)
    {x : Univ A R' P' dt.KIx dt.dd} :
    (∀ y : Univ A R' P' dt.KIx dt.dd, tagTupleLe y x) ↔ ∀ y, Marked y → tagTupleLe y x := by
  refine ⟨fun h y _ => h y, fun h y => ?_⟩
  obtain ⟨g, -, hmax⟩ := exists_greatest
    (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx) (A := A) (d := dt.dd))
    (P := fun _ : Univ A R' P' dt.KIx dt.dd => True) ⟨x, trivial⟩
  have hgall : ∀ z : Univ A R' P' dt.KIx dt.dd, tagTupleLe z g := fun z => hmax z trivial
  have hgm : Marked g := (hmk g).mpr (Or.inl (arg_of_isGreatest hgall))
  exact (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx) (A := A) (d := dt.dd)).2.1
    y g x (hgall y) (h g hgm)

end Entry

/-! ### The tape at time zero is the entry state's background -/

section Back

variable {L : Language.{0, 0}} {dt : Data L} {A R' PE : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R']
variable [LinearOrder (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite (NexPh (Option dt.KIx) PE)]
variable [Finite dt.KIx] [Nonempty A] [Nonempty dt.KIx]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)

/-- **The channel's tape, after the start step, is the entry state's
background**: what a program that lays its own file arrives at its evaluation
with, a program handed its file has from the start. Slot for slot: the register
flag and the block one-hots repeat the layout's, the name slots the element's own
coordinates, the two end slots the file's ends
(`isTopNonArg_iff_least_marked`, `isGreatest_iff_greatest_marked`), and every
track is clear – except at the marker, where the start step sets `wk` and `bot`,
and the entry state says the same. -/
theorem startBack_initBackReg (hR : PR.table.Reads)
    (hmark : ∀ x, PR.mark x = regSlotMark PR.zero PR.one dt.dd0Le x)
    (hmk : ∀ x, PR.marked x ↔ (∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)
    (hblank : ∀ s, PR.blank s = PR.zero)
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hv : ∀ x, PR.marked x → v ≠ wmRegSeg x) :
    dt.startBack PR.initBackReg PR.one v =
      dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
        (dt.nexEntrySt v) := by
  classical
  have hinp : ∀ x : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd,
      WMHasInp x ↔ PR.marked x := fun x => Table.wmHasInp_iff_marked hR x
  funext r
  by_cases hc : ∃ x, PR.marked x ∧ r = wmRegSeg x
  · obtain ⟨x, hx, rfl⟩ := hc
    have hcell : ((dt.regLaid hlin hord).cell ⟨x, (hinp x).mpr hx⟩) = wmRegSeg x := rfl
    have huniq : ∀ u : dt.RegIx (A := A) (R' := R')
        (P' := NexPh (Option dt.KIx) PE),
        wmRegSeg x = (dt.regLaid hlin hord).cell u → u.1 = x := by
      rintro ⟨y, hy⟩ hyx
      exact (wmRegSeg_injOn hlin ((hinp x).mpr hx) hy hyx).symm
    rw [startBack_frame (fun hcv => hv x hx hcv.symm),
      Prog.initBackReg_wmRegSeg hlin hR hx]
    funext s
    rw [hmark x]
    match s with
    | .reg =>
      exact (bitVal_pos ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm⟩).symm
    | .regFirst =>
      refine bitVal_congr ?_
      rw [isTopNonArg_iff_least_marked hmk (exists_isTopNonArg) hx]
      constructor
      · intro hle
        refine ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm, fun y => ?_⟩
        exact (hord _ _).mp ((hord _ _).mpr (hle y.1 ((hinp y.1).mp y.2)))
      · rintro ⟨u, hu, hmin⟩ y hy
        have hux : u.1 = x := huniq u hu
        exact hux ▸ hmin ⟨y, (hinp y).mpr hy⟩
    | .regLast =>
      refine bitVal_congr ?_
      rw [isGreatest_iff_greatest_marked (A := A) hmk]
      constructor
      · intro hle
        refine ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm, fun y => ?_⟩
        exact hle y.1 ((hinp y.1).mp y.2)
      · rintro ⟨u, hu, hmax⟩ y hy
        have hux : u.1 = x := huniq u hu
        exact hux ▸ hmax ⟨y, (hinp y).mpr hy⟩
    | .blk b =>
      refine bitVal_congr ?_
      constructor
      · intro hb
        exact ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm, hb⟩
      · rintro ⟨u, hu, hb⟩
        rw [← huniq u hu]
        exact hb
    | .name j =>
      rw [show dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
          (dt.nexEntrySt v) (wmRegSeg x) (Slot.name j) =
        (if h : ∃ u : dt.RegIx (A := A) (R' := R') (P' := NexPh (Option dt.KIx) PE),
            wmRegSeg x = (dt.regLaid hlin hord).cell u then
          (dt.regLaid hlin hord).arg h.choose (Fin.castLE dt.dd0Le j) else PR.zero) from rfl,
        dif_pos ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm⟩]
      have hch : ((⟨⟨x, (hinp x).mpr hx⟩, hcell.symm⟩ :
          ∃ u : dt.RegIx (A := A) (R' := R') (P' := NexPh (Option dt.KIx) PE),
            wmRegSeg x = (dt.regLaid hlin hord).cell u).choose).1 = x :=
        huniq _ (⟨⟨x, (hinp x).mpr hx⟩, hcell.symm⟩ :
          ∃ u : dt.RegIx (A := A) (R' := R') (P' := NexPh (Option dt.KIx) PE),
            wmRegSeg x = (dt.regLaid hlin hord).cell u).choose_spec
      change x.2 (Fin.castLE dt.dd0Le j) =
        (((⟨⟨x, (hinp x).mpr hx⟩, hcell.symm⟩ :
          ∃ u : dt.RegIx (A := A) (R' := R') (P' := NexPh (Option dt.KIx) PE),
            wmRegSeg x = (dt.regLaid hlin hord).cell u).choose).1).2 (Fin.castLE dt.dd0Le j)
      rw [hch]
    | .pdd =>
      refine bitVal_congr ?_
      constructor
      · intro hp
        exact ⟨⟨x, (hinp x).mpr hx⟩, hcell.symm, hp⟩
      · rintro ⟨u, hu, hp⟩
        rw [← huniq u hu]
        exact hp
    | .mir => exact (bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)).symm
    | .tgt => exact (bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)).symm
    | .sav => exact (bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)).symm
    | .val => exact (bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)).symm
    | .wk => exact (bitVal_neg (fun hcv => hv x hx hcv.symm)).symm
    | .bot => exact (bitVal_neg (fun hcv => hv x hx hcv.symm)).symm
    | .ltp => exact (bitVal_neg (fun hc => hc)).symm
    | .old i => exact (bitVal_neg (fun hc => hc)).symm
    | .new i => exact (bitVal_neg (fun hc => hc)).symm
  · have hnc : ∀ u : dt.RegIx (A := A) (R' := R') (P' := NexPh (Option dt.KIx) PE),
        r ≠ (dt.regLaid hlin hord).cell u := by
      rintro ⟨y, hy⟩ hru
      exact hc ⟨y, (hinp y).mp hy, hru⟩
    have hzero : ∀ s : dt.SlotIx,
        dt.ixBack (dt.regLaid hlin hord).toLayout PR.zero PR.one dt.dd0Le
          (dt.nexEntrySt v) r s =
          if s = Slot.wk ∨ s = Slot.bot then bitVal PR.zero PR.one (r = v) else PR.zero := by
      intro s
      match s with
      | .reg => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu⟩; exact hnc u hu)
      | .regFirst => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                     exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .regLast => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                    exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .blk b => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .name j => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                   exact dif_neg (by rintro ⟨u, hu⟩; exact hnc u hu)
      | .pdd => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .mir => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .tgt => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .sav => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .val => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (by rintro ⟨u, hu, -⟩; exact hnc u hu)
      | .wk => rw [if_pos (Or.inl rfl)]; exact rfl
      | .bot => rw [if_pos (Or.inr rfl)]; exact rfl
      | .ltp => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                exact bitVal_neg (fun hc' => hc')
      | .old i => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  exact bitVal_neg (fun hc' => hc')
      | .new i => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  exact bitVal_neg (fun hc' => hc')
    by_cases hrv : r = v
    · subst hrv
      rw [show dt.startBack PR.initBackReg PR.one r r =
        Function.update (Function.update (PR.initBackReg r) Slot.wk PR.one)
          Slot.bot PR.one from if_pos rfl]
      funext s
      rw [hzero s, Prog.initBackReg_of_not_reg
        (fun x hx hcx => hc ⟨x, hx, hcx⟩)]
      match s with
      | .wk => rw [if_pos (Or.inl rfl), bitVal_pos rfl,
          Function.update_of_ne (by rintro hc'; exact nomatch hc'),
          Function.update_self]
      | .bot => rw [if_pos (Or.inr rfl), bitVal_pos rfl, Function.update_self]
      | .reg => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .regFirst => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                     rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                       Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .regLast => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                    rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                      Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .blk b => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                    Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .name j => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                   rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                     Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .pdd => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .mir => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .tgt => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .sav => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .val => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .ltp => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                  Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .old i => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                    Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
      | .new i => rw [if_neg (by rintro (hc' | hc') <;> exact nomatch hc')]
                  rw [Function.update_of_ne (by rintro hc'; exact nomatch hc'),
                    Function.update_of_ne (by rintro hc'; exact nomatch hc'), hblank]
    · rw [startBack_frame hrv, Prog.initBackReg_of_not_reg
        (fun x hx hcx => hc ⟨x, hx, hcx⟩)]
      funext s
      rw [hzero s, hblank]
      by_cases hs : s = Slot.wk ∨ s = Slot.bot
      · rw [if_pos hs, bitVal_neg hrv]
      · rw [if_neg hs]

omit [Nonempty A] [Nonempty dt.KIx] in
omit [DecidableEq dt.SlotIx] in
set_option linter.unusedDecidableInType false in
open Classical in
/-- **Every track of the channel's tape is clear**: a mark is a
`regSlotMark`, whose tracks are all `zero`, and every other cell is blank. This
is what the semantic half of a backward reading starts from – the tracks hold
nothing until the machine writes them. -/
theorem initBackReg_track_zero
    (hlin : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    (hR : PR.table.Reads)
    (hmark : ∀ x, PR.mark x = regSlotMark PR.zero PR.one dt.dd0Le x)
    (hblank : ∀ s, PR.blank s = PR.zero)
    (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop)
    (s : dt.SlotIx) (hs : ¬Slot.IsFile s) : PR.initBackReg r s = PR.zero := by
  classical
  by_cases hr : ∃ x, PR.marked x ∧ r = wmRegSeg x
  · obtain ⟨x, hx, rfl⟩ := hr
    rw [Prog.initBackReg_wmRegSeg hlin hR hx, hmark]
    match s with
    | .reg => exact absurd trivial hs
    | .regFirst => exact absurd trivial hs
    | .regLast => exact absurd trivial hs
    | .blk b => exact absurd trivial hs
    | .name j => exact absurd trivial hs
    | .pdd => exact absurd trivial hs
    | .mir => rfl
    | .tgt => rfl
    | .sav => rfl
    | .val => rfl
    | .wk => rfl
    | .bot => rfl
    | .ltp => rfl
    | .old i => rfl
    | .new i => rfl
  · rw [Prog.initBackReg_of_not_reg (fun x hx hc => hr ⟨x, hx, hc⟩), hblank]

-- `Function.update` in the start step is what needs the instance.
set_option linter.unusedDecidableInType false in
open Classical in
/-- **The tape the channel hands over is recognisable**: the file's slots are the
layout's (that is `startBack_initBackReg`, read at those slots alone, the start
step touching only tracks), the four addressed tracks are clear, and every other
track is a bit – the marks are `regSlotMark`s and the rest is blank. This is the
base of an opening's reading. -/
theorem tapeShape_initBackReg (hR : PR.table.Reads)
    (hmark : ∀ x, PR.mark x = regSlotMark PR.zero PR.one dt.dd0Le x)
    (hmk : ∀ x, PR.marked x ↔ (∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)
    (hblank : ∀ s, PR.blank s = PR.zero)
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hv : ∀ x, PR.marked x → v ≠ wmRegSeg x) :
    TapeShape (dt := dt) (dt.regLaid hlin hord).toLayout PR.zero PR.one
      (dt.nexEntrySt v) PR.initBackReg := by
  classical
  have hback := startBack_initBackReg hlin hord hR hmark hmk hblank hv
  refine ⟨?_, ?_, ?_⟩
  · -- the file's slots: the start step writes only tracks, so they already agree
    intro r s hs
    by_cases hrv : r = v
    · subst hrv
      have h := congrFun hback r
      have hne₁ : s ≠ (Slot.bot : dt.SlotIx) := by rintro rfl; exact hs
      have hne₂ : s ≠ (Slot.wk : dt.SlotIx) := by rintro rfl; exact hs
      have h2 : dt.startBack PR.initBackReg PR.one r r s = PR.initBackReg r s := by
        rw [show dt.startBack PR.initBackReg PR.one r r =
          Function.update (Function.update (PR.initBackReg r) Slot.wk PR.one)
            Slot.bot PR.one from if_pos rfl,
          Function.update_of_ne hne₁, Function.update_of_ne hne₂]
      rw [← h2, h]
    · rw [← dt.startBack_frame (bg := PR.initBackReg) (one := PR.one) (v := v) hrv,
        congrFun hback r]
  · -- the four addressed tracks are clear
    intro r s hs
    refine initBackReg_track_zero hlin hR hmark hblank r s ?_
    rcases hs with rfl | rfl | rfl | rfl <;> exact fun hc => hc
  · -- and every other track is a bit
    intro r s hs
    by_cases hr : ∃ x, PR.marked x ∧ r = wmRegSeg x
    · obtain ⟨x, hx, rfl⟩ := hr
      rw [Prog.initBackReg_wmRegSeg hlin hR hx, hmark]
      match s with
      | .reg => exact absurd trivial hs
      | .regFirst => exact absurd trivial hs
      | .regLast => exact absurd trivial hs
      | .blk b => exact absurd trivial hs
      | .name j => exact absurd trivial hs
      | .pdd => exact absurd trivial hs
      | .mir => exact Or.inl rfl
      | .tgt => exact Or.inl rfl
      | .sav => exact Or.inl rfl
      | .val => exact Or.inl rfl
      | .wk => exact Or.inl rfl
      | .bot => exact Or.inl rfl
      | .ltp => exact Or.inl rfl
      | .old i => exact Or.inl rfl
      | .new i => exact Or.inl rfl
    · rw [Prog.initBackReg_of_not_reg (fun x hx hc => hr ⟨x, hx, hc⟩), hblank]
      exact Or.inl rfl

end Back

/-! ### What the marking gives the run -/

section Marks

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [Nonempty A]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable (hR : PR.table.Reads)
variable (hmk : ∀ x : Univ A R' P' dt.KIx dt.dd,
  PR.marked x ↔ (∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x)
variable (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)

omit [Nonempty A] [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
include hR hmk in
/-- **The channel writes for an element exactly when the program marks it.** -/
theorem hasInp_iff_regMarked (x : Univ A R' P' dt.KIx dt.dd) :
    WMHasInp x ↔ ((∃ k, x.1 = Tag.arg k) ∨ IsTopNonArg x) :=
  (Table.wmHasInp_iff_marked hR x).trans (hmk x)

omit [Nonempty A] [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
include hR hmk in
/-- **Every argument element carries input**: the `hargall` the run asks for. -/
theorem hasInp_of_arg {x : Univ A R' P' dt.KIx dt.dd}
    (hx : ∃ k : dt.KIx, x.1 = Tag.arg k) : WMHasInp x :=
  (hasInp_iff_regMarked hR hmk x).mpr (Or.inl hx)

omit [Nonempty A] [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
include hR hmk in
/-- **Every named register carries input**: the `harg` the file's `HasName`
asks for. -/
theorem hasInp_blkElt (zero : A) (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
      Univ A R' P' dt.KIx dt.dd) :=
  hasInp_of_arg hR hmk ⟨toLex b, rfl⟩

omit [Nonempty A] [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
include hR hmk hord in
/-- **The elements the channel writes for are upward closed**: above an argument
element everything is an argument element, and above the one element below them
everything is marked. This is the `hup` the file's bound
(`DescriptiveComplexity.wideRank_wmRegSeg_lt`) asks for, and what puts the file
under `2 ^` the number of marks. -/
theorem hasInp_up (x y : Univ A R' P' dt.KIx dt.dd) (hxy : WMLe x y)
    (hx : WMHasInp x) : WMHasInp y := by
  rcases (hasInp_iff_regMarked hR hmk x).mp hx with ⟨k, hk⟩ | htop
  · refine (hasInp_iff_regMarked hR hmk y).mpr (Or.inl ?_)
    by_contra hc
    push Not at hc
    have hlt : y.1 < Tag.arg k := lt_arg y.1 k hc
    rcases (hord _ _).mp hxy with hb | ⟨hb, -⟩
    · rw [hk] at hb; exact absurd hb (asymm hlt)
    · rw [hk] at hb; exact absurd hb.symm (ne_of_lt hlt)
  · rcases em (∃ k : dt.KIx, y.1 = Tag.arg k) with harg | hnarg
    · exact (hasInp_iff_regMarked hR hmk y).mpr (Or.inl harg)
    · push Not at hnarg
      refine (hasInp_iff_regMarked hR hmk y).mpr (Or.inr ⟨hnarg, fun z hz => ?_⟩)
      exact (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx) (A := A)
        (d := dt.dd)).2.1 z x y (htop.2 z hz) ((hord _ _).mp hxy)

omit [Finite dt.KIx] in
include hR hmk hord in
/-- **The element below the argument tags is marked and least among the marked
ones**: the `bot` the working area is measured against
(`DescriptiveComplexity.Draw.Data.work_regLaid`). -/
theorem exists_regBotElt :
    ∃ z : Univ A R' P' dt.KIx dt.dd, WMHasInp z ∧
      (∀ y : Univ A R' P' dt.KIx dt.dd, WMHasInp y → WMLe z y) ∧
      ∀ i : dt.KIx, z.1 ≠ Tag.arg i := by
  obtain ⟨z, hz⟩ := exists_isTopNonArg (A := A) (R' := R') (P' := P') (dt := dt)
  refine ⟨z, (hasInp_iff_regMarked hR hmk z).mpr (Or.inr hz), fun y hy => ?_, hz.1⟩
  rcases (hasInp_iff_regMarked hR hmk y).mp hy with ⟨k, hk⟩ | htop
  · exact (hord _ _).mpr (Or.inl (hk ▸ lt_arg z.1 k hz.1))
  · exact (hord _ _).mpr (htop.2 z hz.1)

end Marks

end Data

end Draw

end DescriptiveComplexity
