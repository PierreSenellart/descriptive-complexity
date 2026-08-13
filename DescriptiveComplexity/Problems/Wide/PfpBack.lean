/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSites

/-!
# The background: the machine's mutable state, presented as a tape

Every kit discharge takes a family of **slot equations** – the register mark
is set exactly at the register cells, the marker at one working-area
address, and so on. They are all facts about one object: the machine's
mutable state – its registers, its stage tracks, its markers – laid over the
permanent marks of `DescriptiveComplexity.Pfp.slotMark`. This file is that
object, `DescriptiveComplexity.Pfp.TapeSt`, its presentation
`DescriptiveComplexity.Pfp.PfpData.back` as the `rest` family the pass layer
walks, and the slot equations, proved once: the discharges of
`PfpRun` will cite them instead of re-deriving per call site.

The split of a track's home: the four machine registers (`mir`, `tgt`,
`sav`, `val`) hold bits **per element** – their digit at a cell is
`DescriptiveComplexity.regBit`, set only at register cells – while the stage
tracks (`old i`, `new i`) and the working-area markers (`wk`, `bot`, `ltp`)
hold bits **per cell**, anywhere on the tape. The permanent mark slots
(`reg`, the ends, `blk`, `name`, `pdd`) read
`DescriptiveComplexity.Pfp.slotMark` at register cells and are clear
elsewhere, which is what their read-back equations say.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **The machine's mutable state**: the four registers (bits per element),
the stage tracks and markers (bits per cell). The permanent marks are not
here – they never change. -/
structure TapeSt (dt : PfpData L) (A R' P' : Type) : Type 1 where
  /-- The MIRROR register. -/
  mir : Univ A R' P' dt.KIx dt.dd → Prop
  /-- The TARGET register. -/
  tgt : Univ A R' P' dt.KIx dt.dd → Prop
  /-- The SAV register. -/
  sav : Univ A R' P' dt.KIx dt.dd → Prop
  /-- The VAL register. -/
  val : Univ A R' P' dt.KIx dt.dd → Prop
  /-- The current stage of each variable, a bit per cell. -/
  old : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The next stage of each variable, a bit per cell. -/
  new : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The working-cell marker, a bit per cell. -/
  wk : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The bottom marker, a bit per cell. -/
  bot : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The end marker of the logical interval, a bit per cell. -/
  ltp : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop

namespace PfpData

variable (dt : PfpData L) {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

open Classical in
/-- **The state, presented as a background**: the value of each slot at each
cell. The walked track of a pass is carved out of this by
`DescriptiveComplexity.Pfp.Prog.trackTape`; everything else rides along. -/
noncomputable def back (zero one : A) (hdd : dt.dd0 ≤ dt.dd)
    (st : TapeSt dt A R' P') (r : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.SlotIx → A
  | .reg => bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u)
  | .regFirst =>
    bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u ∧
      ∀ y : Univ A R' P' dt.KIx dt.dd, tagTupleLe u y)
  | .regLast =>
    bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u ∧
      ∀ y : Univ A R' P' dt.KIx dt.dd, tagTupleLe y u)
  | .blk b =>
    bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u ∧ tagBlk u.1 = b)
  | .name j =>
    if h : ∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u then
      h.choose.2 (Fin.castLE hdd j)
    else zero
  | .pdd =>
    bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u ∧
      ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero)
  | .mir => bitVal zero one (regBit st.mir r)
  | .tgt => bitVal zero one (regBit st.tgt r)
  | .sav => bitVal zero one (regBit st.sav r)
  | .val => bitVal zero one (regBit st.val r)
  | .wk => bitVal zero one (st.wk r)
  | .bot => bitVal zero one (st.bot r)
  | .ltp => bitVal zero one (st.ltp r)
  | .old i => bitVal zero one (st.old i r)
  | .new i => bitVal zero one (st.new i r)

variable {zero one : A} {hdd : dt.dd0 ≤ dt.dd} {st : TapeSt dt A R' P'}

/-! ### The slot equations, once -/

/-- The register mark: set exactly at the register cells – the equation
every discharge's `hrg` is. -/
theorem back_reg :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r .reg =
        bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u) :=
  fun _ => rfl

/-- The marker slot, read back. -/
theorem back_wk :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r .wk = bitVal zero one (st.wk r) :=
  fun _ => rfl

/-- The bottom mark, read back. -/
theorem back_bot :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r .bot = bitVal zero one (st.bot r) :=
  fun _ => rfl

/-- The end mark, read back. -/
theorem back_ltp :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r .ltp = bitVal zero one (st.ltp r) :=
  fun _ => rfl

/-- A stage track, read back. -/
theorem back_old (i : dt.d.B.ι) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r (.old i) = bitVal zero one (st.old i r) :=
  fun _ => rfl

/-- The next-stage track, read back. -/
theorem back_new (i : dt.d.B.ι) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r (.new i) = bitVal zero one (st.new i r) :=
  fun _ => rfl

/-- A machine register's slot carries its track's register digits – the
source-slot condition of the copy kits. -/
theorem back_mir_bit (u : Univ A R' P' dt.KIx dt.dd) :
    dt.back zero one hdd st (wmSeg u) .mir =
      bitVal zero one (regBit st.mir (wmSeg u)) :=
  rfl

/-! ### What a state's scratch registers do not decide

The VAL loop threads SAV and TARGET and nothing else
(`DescriptiveComplexity.Pfp.PfpData.roundEndSt_eq`), so its rounds run at
states that differ from the machinery's entry state in those two registers
alone. `ScratchEq` names that relation, and the lemmas below say what it
buys: every per-cell mark and track is shared, hence so is the background
at every cell of the working area — the four register slots being
`DescriptiveComplexity.regBit`s, set at a register cell only. -/

/-- **Two states differing in the two scratch registers alone**: every mark
and every track is shared, the saved mirror and the target need not be. -/
def ScratchEq (st st' : TapeSt dt A R' P') : Prop :=
  st.wk = st'.wk ∧ st.mir = st'.mir ∧ st.val = st'.val ∧ st.old = st'.old ∧
    st.new = st'.new ∧ st.bot = st'.bot ∧ st.ltp = st'.ltp

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- Rewriting the two scratch registers is a `ScratchEq`. -/
theorem scratchEq_scratch (st : TapeSt dt A R' P')
    (X Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with sav := X, tgt := Y } st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- Rewriting the target alone is a `ScratchEq`. -/
theorem scratchEq_tgt (st : TapeSt dt A R' P')
    (Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with tgt := Y } st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- `ScratchEq` is reflexive. -/
theorem scratchEq_refl (st : TapeSt dt A R' P') : dt.ScratchEq st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` is symmetric. -/
theorem ScratchEq.symm {st st' : TapeSt dt A R' P'}
    (h : dt.ScratchEq st st') : dt.ScratchEq st' st :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm,
    h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` is transitive. -/
theorem ScratchEq.trans {st st' st'' : TapeSt dt A R' P'}
    (h : dt.ScratchEq st st') (h' : dt.ScratchEq st' st'') :
    dt.ScratchEq st st'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.1.trans h'.2.2.2.2.1,
    h.2.2.2.2.2.1.trans h'.2.2.2.2.2.1,
    h.2.2.2.2.2.2.trans h'.2.2.2.2.2.2⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same scratch registers on both
sides. -/
theorem ScratchEq.scratch {st st' : TapeSt dt A R' P'}
    (h : dt.ScratchEq st st') (X Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with sav := X, tgt := Y }
      { st' with sav := X, tgt := Y } :=
  h

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same target on both sides. -/
theorem ScratchEq.tgt {st st' : TapeSt dt A R' P'}
    (h : dt.ScratchEq st st') (Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with tgt := Y } { st' with tgt := Y } :=
  h

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same VAL register on both sides. -/
theorem ScratchEq.val {st st' : TapeSt dt A R' P'}
    (h : dt.ScratchEq st st') (m : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with val := m } { st' with val := m } :=
  ⟨h.1, h.2.1, rfl, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **Off the register file the background is blind to every register**: the
four register slots read `DescriptiveComplexity.regBit`, which is set at a
register cell only, so at a cell of the working area two states agree as
soon as their per-cell marks and tracks do — whatever their mirror, their
target, their saved mirror or their VAL content is. This is what lets the
control of the VAL loop's *threaded* states be the control of the
unthreaded ones: threading rewrites the two scratch registers, and the
rounds read their background at the working cell. -/
theorem back_congr_off_reg {st st' : TapeSt dt A R' P'}
    (hwk : st.wk = st'.wk) (hbot : st.bot = st'.bot) (hltp : st.ltp = st'.ltp)
    (hold : st.old = st'.old) (hnew : st.new = st'.new)
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ¬∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u) :
    dt.back zero one hdd st r = dt.back zero one hdd st' r := by
  have hreg : ∀ m : Univ A R' P' dt.KIx dt.dd → Prop, ¬regBit m r :=
    fun m hc => hr ⟨hc.choose, hc.choose_spec.1⟩
  funext s
  cases s with
  | mir => exact bitVal_congr (iff_of_false (hreg st.mir) (hreg st'.mir))
  | tgt => exact bitVal_congr (iff_of_false (hreg st.tgt) (hreg st'.tgt))
  | sav => exact bitVal_congr (iff_of_false (hreg st.sav) (hreg st'.sav))
  | val => exact bitVal_congr (iff_of_false (hreg st.val) (hreg st'.val))
  | wk => exact congrArg (bitVal zero one) (congrFun hwk r)
  | bot => exact congrArg (bitVal zero one) (congrFun hbot r)
  | ltp => exact congrArg (bitVal zero one) (congrFun hltp r)
  | old i =>
    exact congrArg (bitVal zero one) (congrFun (congrFun hold i) r)
  | new i =>
    exact congrArg (bitVal zero one) (congrFun (congrFun hnew i) r)
  | _ => rfl

variable {dt} in
/-- The background at a working cell, off a `ScratchEq`. -/
theorem ScratchEq.back {st st' : TapeSt dt A R' P'} (h : dt.ScratchEq st st')
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ¬∃ u : Univ A R' P' dt.KIx dt.dd, r = wmSeg u) :
    dt.back zero one hdd st r = dt.back zero one hdd st' r :=
  dt.back_congr_off_reg h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 h.2.2.2.1
    h.2.2.2.2.1 hr

section Name

variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

/-! ### The permanent marks at a register cell, and the navigation by name

The mark slots are stated existentially – "some element's cell, whose tag's
block is `b`" – because the background is a function of the *address*. At a
register cell the existential collapses, by injectivity of
`DescriptiveComplexity.wmSeg`, and what is left is the mark of the element
itself. Those three equations are what the navigation-by-name scans read:
`DescriptiveComplexity.Pfp.PfpData.nameG` holds at exactly one cell, the
canonically padded cell of the element whose coordinates the control holds
(`DescriptiveComplexity.Pfp.PfpData.nameG_unique`), and nowhere off the
register file. -/

/-- The block one-hot, at a register cell. -/
theorem back_blk_wmSeg (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (u : Univ A R' P' dt.KIx dt.dd) (b : Option (Fin dt.ko ⊕ Fin dt.ki)) :
    dt.back zero one hdd st (wmSeg u) (.blk b) =
      bitVal zero one (tagBlk u.1 = b) := by
  refine bitVal_congr ⟨?_, fun h => ⟨u, rfl, h⟩⟩
  rintro ⟨v, hv, hvb⟩
  rw [wmSeg_injective hlin hv]
  exact hvb

/-- The padding mark, at a register cell. -/
theorem back_pdd_wmSeg (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (u : Univ A R' P' dt.KIx dt.dd) :
    dt.back zero one hdd st (wmSeg u) .pdd =
      bitVal zero one (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) := by
  refine bitVal_congr ⟨?_, fun h => ⟨u, rfl, h⟩⟩
  rintro ⟨v, hv, hvb⟩
  rw [wmSeg_injective hlin hv]
  exact hvb

/-- A name slot, at a register cell: the element's own coordinate. -/
theorem back_name_wmSeg (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (u : Univ A R' P' dt.KIx dt.dd) (j : Fin dt.dd0) :
    dt.back zero one hdd st (wmSeg u) (.name j) = u.2 (Fin.castLE hdd j) := by
  classical
  change (if h : ∃ v : Univ A R' P' dt.KIx dt.dd, wmSeg u = wmSeg v then
    h.choose.2 (Fin.castLE hdd j) else zero) = _
  rw [dif_pos ⟨u, rfl⟩]
  have hspec := (⟨u, rfl⟩ : ∃ v : Univ A R' P' dt.KIx dt.dd,
    wmSeg u = wmSeg v).choose_spec
  rw [show (⟨u, rfl⟩ : ∃ v : Univ A R' P' dt.KIx dt.dd,
    wmSeg u = wmSeg v).choose = u from (wmSeg_injective hlin hspec).symm]

/-- **The name guard, at a register cell**: the cell's element is in the
named block, canonically padded, and carries the coordinates the control
computes. -/
theorem nameGF_wmSeg (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A)
    (fc : Q → A) (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameGF one b cf fc (dt.back zero one hdd st (wmSeg u)) ↔
      (tagBlk u.1 = some b ∧
        (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) ∧
        ∀ j : Fin dt.dd0, u.2 (Fin.castLE hdd j) = cf fc j) := by
  rw [PfpData.nameGF, dt.back_blk_wmSeg hlin, dt.back_pdd_wmSeg hlin]
  refine and_congr (bitVal_iff hzo) (and_congr (bitVal_iff hzo) ?_)
  exact forall_congr' fun j => iff_of_eq (congrArg (· = cf fc j)
    (dt.back_name_wmSeg hlin u j))

/-- **The name guard identifies one cell**: two register cells it holds at
are the same. This is what a navigation-by-name scan needs of its stopping
condition (`DescriptiveComplexity.Pfp.Prog.reaches_toCell`). -/
theorem nameGF_unique (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {u u' : Univ A R' P' dt.KIx dt.dd}
    (h : dt.nameGF one b cf fc (dt.back zero one hdd st (wmSeg u)))
    (h' : dt.nameGF one b cf fc (dt.back zero one hdd st (wmSeg u'))) :
    u = u' := by
  obtain ⟨hb, hp, hn⟩ := (dt.nameGF_wmSeg hzo hlin b cf fc u).mp h
  obtain ⟨hb', hp', hn'⟩ := (dt.nameGF_wmSeg hzo hlin b cf fc u').mp h'
  exact eq_of_slotMark_name (hdd := hdd) (hb.trans hb'.symm) hb
    (fun j => (hn j).trans (hn' j).symm) hp hp'

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **Off the register file the name guard fails**: the block one-hot is
clear there, so no scan stops in the working area. -/
theorem not_nameGF_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : Univ A R' P' dt.KIx dt.dd, r ≠ wmSeg u) :
    ¬dt.nameGF one b cf fc (dt.back zero one hdd st r) := by
  rintro ⟨hb, -, -⟩
  obtain ⟨u, hu, -⟩ := (bitVal_iff hzo).mp hb
  exact hr u hu

/-- The coordinate-loop trips' guard, at a register cell. -/
theorem nameG_wmSeg (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q)
    (fc : Q → A) (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameG one b coord fc (dt.back zero one hdd st (wmSeg u)) ↔
      (tagBlk u.1 = some b ∧
        (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) ∧
        ∀ j : Fin dt.dd0, u.2 (Fin.castLE hdd j) = fc (coord j)) :=
  dt.nameGF_wmSeg hzo hlin b _ fc u

/-- The coordinate-loop trips' guard identifies one cell. -/
theorem nameG_unique (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {fc : Q → A} {u u' : Univ A R' P' dt.KIx dt.dd}
    (h : dt.nameG one b coord fc (dt.back zero one hdd st (wmSeg u)))
    (h' : dt.nameG one b coord fc (dt.back zero one hdd st (wmSeg u'))) :
    u = u' :=
  dt.nameGF_unique hzo hlin h h'

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- Off the register file the coordinate-loop trips' guard fails. -/
theorem not_nameG_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : Univ A R' P' dt.KIx dt.dd, r ≠ wmSeg u) :
    ¬dt.nameG one b coord fc (dt.back zero one hdd st r) :=
  dt.not_nameGF_of_not_reg hzo hr

end Name

/-- **The file-top mark is the greatest element's cell**: given that the
universe order is linear, the `regLast` slot is set exactly at the cell of
the top element – the equation every discharge's `hrl` is. -/
theorem back_regLast
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {gtop : Univ A R' P' dt.KIx dt.dd} (htop : ∀ y, WMLe y gtop)
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back zero one hdd st r .regLast = bitVal zero one (r = wmSeg gtop) := by
  intro r
  refine bitVal_congr ⟨?_, ?_⟩
  · rintro ⟨u, rfl, hu⟩
    have hut : u = gtop :=
      hlin.2.2.1 u gtop (htop u) ((hord gtop u).mpr (hu gtop))
    rw [hut]
  · rintro rfl
    exact ⟨gtop, rfl, fun y => (hord y gtop).mp (htop y)⟩

end PfpData

end Pfp

end DescriptiveComplexity
