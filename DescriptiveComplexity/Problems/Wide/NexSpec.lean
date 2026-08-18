/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.BlkLayout
import DescriptiveComplexity.Problems.Wide.NexOuter

/-!
# What the clocked program's file-laying sweep writes

`DescriptiveComplexity.Draw.SweepSpec` leaves the write to the caller, because
what a cell of the file holds is a fact about the layout and not about the shape
of the loop. This file is that fact at the layout a clocked program uses
(`DescriptiveComplexity.Draw.Data.blkLaid`): the sweep writes, at the register
the pointer names, the **mark** of that register – it is a register, whether it
is the first or the last of the file, its block one-hot, its coordinates, and
that it is canonically padded – and the blank in every track.

The one theorem is that this *is* the background the file's run installs
(`DescriptiveComplexity.Draw.Data.buildWr_eq_ixBack`): slot by slot, the mark
the pointer can compute agrees with
`DescriptiveComplexity.Draw.Data.ixBack` at the register's cell, given that
the state's own tracks are clear – which they are, the file being laid before
anything is written to it.

What makes the agreement possible at all is that a register's contents depend on
its block and its named tuple and on nothing else, which is the point the whole
index parameter was introduced for: the pointer holds exactly those, the block in
the phase and the tuple in the control.

The pointer's advance is here too: `DescriptiveComplexity.Draw.Data.ptrNext`
writes the next register's tuple into the control's coordinate slots and leaves
every other slot alone, and
`DescriptiveComplexity.Draw.Data.buildSpec` is the whole
`DescriptiveComplexity.Draw.SweepSpec` the file-laying phase runs at. The
guessing phase's write is here as well
(`DescriptiveComplexity.Draw.Data.guessWr`): the cell it read with the stage
tracks holding the guessed value, and nothing else touched.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

section BuildSpec

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Finite A] [Nonempty A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite (Univ A R' P' dt.KIx dt.dd)]

/-- **The tuple the pointer holds**: the control's coordinates, at the slots the
caller reserved for them. -/
def ptrTup (coord : Fin dt.dd → dt.CtlIx) (f : dt.CtlIx → A) : Fin dt.dd → A :=
  fun j => f (coord j)

open Classical in
/-- **What the file-laying sweep writes**: the mark of the register the pointer
names, and the blank in every track. Every one of these is read off the block
the phase carries and the coordinates the control holds, which is what makes it
a legal `DescriptiveComplexity.Draw.SweepSpec.wr`. -/
noncomputable def buildWr (zero one : A) (coord : Fin dt.dd → dt.CtlIx)
    (b : Option dt.KIx) (f : dt.CtlIx → A) : dt.SlotIx → A
  | .reg => one
  | .regFirst =>
    bitVal zero one ((b, dt.ptrTup coord f) = blkBot A dt.KIx dt.dd)
  | .regLast =>
    bitVal zero one ((b, dt.ptrTup coord f) = blkTop A dt.KIx dt.dd)
  | .blk c => bitVal zero one (b = c)
  | .name j => f (coord (Fin.castLE dt.dd0Le j))
  | .pdd =>
    bitVal zero one (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → f (coord j) = zero)
  | .mir => zero
  | .tgt => zero
  | .sav => zero
  | .val => zero
  | .wk => zero
  | .bot => zero
  | .ltp => zero
  | .old _ => zero
  | .new _ => zero

variable {dt}

omit [Finite R'] [Finite P'] in
open Classical in
/-- **The sweep's write is the file's background**, at the register the pointer
names: every mark is a fact about the register's block and named tuple, and every
track is clear **at the registers** – the file is laid before anything is
written to it, and what the marker does below them is no business of a
register's mark. -/
theorem buildWr_eq_ixBack {zero one : A}
    (coord : Fin dt.dd → dt.CtlIx) (hdd : dt.dd0 ≤ dt.dd)
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' P' (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos hbase).cell v))
    (hbot : ∀ v, ¬st.bot ((dt.blkLaid h hpos hbase).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos hbase).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos hbase).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos hbase).cell v))
    (b : Option dt.KIx) (f : dt.CtlIx → A) :
    dt.buildWr zero one coord b f =
      dt.ixBack (dt.blkLaid h hpos hbase).toLayout zero one hdd st
        ((dt.blkLaid h hpos hbase).cell (b, dt.ptrTup coord f)) := by
  have hinj : Function.Injective (dt.blkLaid h hpos hbase).toLayout.cell :=
    (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).injective
      (Wide.isLinOrd_blkLe dt.KIx A dt.dd)
  funext sl
  cases sl with
  | reg => exact (bitVal_pos ⟨(b, dt.ptrTup coord f), rfl⟩).symm
  | regFirst =>
    refine (bitVal_congr ⟨?_, ?_⟩).symm
    · rintro ⟨v, hv, hmin⟩
      have hvu : v = (b, dt.ptrTup coord f) := hinj hv.symm
      subst hvu
      exact (Wide.isLinOrd_blkLe dt.KIx A dt.dd).2.2.1 _ _
        (hmin (blkBot A dt.KIx dt.dd)) (blkLe_blkBot A dt.KIx dt.dd _)
    · intro hb
      refine ⟨(b, dt.ptrTup coord f), rfl, fun y => ?_⟩
      rw [hb]
      exact blkLe_blkBot A dt.KIx dt.dd y
  | regLast =>
    refine (bitVal_congr ⟨?_, ?_⟩).symm
    · rintro ⟨v, hv, hmax⟩
      have hvu : v = (b, dt.ptrTup coord f) := hinj hv.symm
      subst hvu
      exact (Wide.isLinOrd_blkLe dt.KIx A dt.dd).2.2.1 _ _
        (blkLe_blkTop A dt.KIx dt.dd _) (hmax (blkTop A dt.KIx dt.dd))
    · intro hb
      refine ⟨(b, dt.ptrTup coord f), rfl, fun y => ?_⟩
      rw [hb]
      exact blkLe_blkTop A dt.KIx dt.dd y
  | blk c => exact (dt.ixBack_blk_cell hinj (b, dt.ptrTup coord f) c).symm
  | name j => exact (dt.ixBack_name_cell hinj (b, dt.ptrTup coord f) j).symm
  | pdd =>
    rw [dt.ixBack_pdd_cell hinj (b, dt.ptrTup coord f)]
    exact rfl
  | mir => exact (bitVal_neg fun hc => hmir hc.choose hc.choose_spec.2).symm
  | tgt => exact (bitVal_neg fun hc => htgt hc.choose hc.choose_spec.2).symm
  | sav => exact (bitVal_neg fun hc => hsav hc.choose hc.choose_spec.2).symm
  | val => exact (bitVal_neg fun hc => hval hc.choose hc.choose_spec.2).symm
  | wk => exact (bitVal_neg (hwk _)).symm
  | bot => exact (bitVal_neg (hbot _)).symm
  | ltp => exact (bitVal_neg (hltp _)).symm
  | old i => exact (bitVal_neg (hold i _)).symm
  | new i => exact (bitVal_neg (hnew i _)).symm

/-! ### The pointer's advance, and the specification it makes -/

open Classical in
variable (dt) in
/-- **The pointer's advance**: the control with its coordinate slots holding the
next register's tuple, every other slot left alone. -/
noncomputable def ptrNext (coord : Fin dt.dd → dt.CtlIx) (b : Option dt.KIx)
    (f : dt.CtlIx → A) : dt.CtlIx → A :=
  fun q => if h : ∃ j : Fin dt.dd, coord j = q then
    (blkNext A dt.KIx dt.dd (b, dt.ptrTup coord f)).2 h.choose else f q

omit [Nonempty A] [Finite R'] [Finite P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **The advance advances the tuple**: the pointer reads back the tuple of the
next register, which is what makes the sweep's step the file's next cell. -/
theorem ptrTup_ptrNext (coord : Fin dt.dd → dt.CtlIx)
    (hinj : Function.Injective coord) (b : Option dt.KIx) (f : dt.CtlIx → A) :
    dt.ptrTup coord (dt.ptrNext coord b f) =
      (blkNext A dt.KIx dt.dd (b, dt.ptrTup coord f)).2 := by
  classical
  funext j
  change (if h : ∃ i : Fin dt.dd, coord i = coord j then
    (blkNext A dt.KIx dt.dd (b, dt.ptrTup coord f)).2 h.choose else _) = _
  rw [dif_pos ⟨j, rfl⟩]
  exact congrArg _ (hinj (⟨j, rfl⟩ : ∃ i : Fin dt.dd, coord i = coord j).choose_spec)

open Classical in
variable (dt) in
/-- **The control holding a register's tuple**: the given control with its
coordinate slots carrying the tuple, and every other slot as it was. This is
what the pointer *is*, and the sweep's advance moves it from one register's to
the next's. -/
noncomputable def ctlOf (coord : Fin dt.dd → dt.CtlIx) (f₀ : dt.CtlIx → A)
    (t : Fin dt.dd → A) : dt.CtlIx → A :=
  fun q => if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else f₀ q

omit [LinearOrder A] [Finite A] [Nonempty A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- The pointer reads back the tuple it was set to. -/
theorem ptrTup_ctlOf {coord : Fin dt.dd → dt.CtlIx} (hcoord : Function.Injective coord)
    (f₀ : dt.CtlIx → A) (t : Fin dt.dd → A) :
    dt.ptrTup coord (dt.ctlOf coord f₀ t) = t := by
  classical
  funext j
  change (if h : ∃ i : Fin dt.dd, coord i = coord j then t h.choose else f₀ (coord j)) = t j
  rw [dif_pos ⟨j, rfl⟩]
  exact congrArg t (hcoord (⟨j, rfl⟩ : ∃ i : Fin dt.dd, coord i = coord j).choose_spec)

omit [LinearOrder A] [Finite A] [Nonempty A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **Setting the pointer forgets the pointer that was there**: the coordinate
slots are overwritten and every other slot rides along, so the exit's reset of
the pointer to the file's first register lands exactly where the next sweep
starts. -/
theorem ctlOf_ctlOf (coord : Fin dt.dd → dt.CtlIx) (f₀ : dt.CtlIx → A)
    (t t' : Fin dt.dd → A) :
    dt.ctlOf coord (dt.ctlOf coord f₀ t') t = dt.ctlOf coord f₀ t := by
  classical
  funext q
  by_cases hq : ∃ j : Fin dt.dd, coord j = q
  · change (if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else _) = _
    rw [dif_pos hq]
    change _ = (if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else f₀ q)
    rw [dif_pos hq]
  · change (if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else
      dt.ctlOf coord f₀ t' q) = _
    rw [dif_neg hq]
    change (if h : ∃ j : Fin dt.dd, coord j = q then t' h.choose else f₀ q) = _
    rw [dif_neg hq]
    change _ = (if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else f₀ q)
    rw [dif_neg hq]

omit [Nonempty A] [Finite R'] [Finite P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **The advance carries the pointer from one register to the next**: at a
control holding a register's tuple, the advance holds the next register's. -/
theorem ptrNext_ctlOf {coord : Fin dt.dd → dt.CtlIx} (hcoord : Function.Injective coord)
    (f₀ : dt.CtlIx → A) (b : Option dt.KIx) (t : Fin dt.dd → A) :
    dt.ptrNext coord b (dt.ctlOf coord f₀ t) =
      dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd (b, t)).2 := by
  classical
  funext q
  by_cases hq : ∃ j : Fin dt.dd, coord j = q
  · change (if h : ∃ j : Fin dt.dd, coord j = q then
      (blkNext A dt.KIx dt.dd (b, dt.ptrTup coord (dt.ctlOf coord f₀ t))).2 h.choose
      else _) = _
    rw [dif_pos hq, dt.ptrTup_ctlOf hcoord f₀ t]
    change _ = (if h : ∃ j : Fin dt.dd, coord j = q then
      (blkNext A dt.KIx dt.dd (b, t)).2 h.choose else f₀ q)
    rw [dif_pos hq]
  · change (if h : ∃ j : Fin dt.dd, coord j = q then _ else dt.ctlOf coord f₀ t q) = _
    rw [dif_neg hq]
    change (if h : ∃ j : Fin dt.dd, coord j = q then t h.choose else f₀ q) = _
    rw [dif_neg hq]
    change _ = (if h : ∃ j : Fin dt.dd, coord j = q then
      (blkNext A dt.KIx dt.dd (b, t)).2 h.choose else f₀ q)
    rw [dif_neg hq]

variable (dt) in
/-- **The sweep that does nothing**: it writes nothing, moves no pointer and is
over at once. A program that is *handed* its file – the register channel of
`DescriptiveComplexity.WideRegAccept` hands one over – has nothing to lay, and
this is what it puts where a file-laying program puts
`DescriptiveComplexity.Draw.Data.buildSpec`: the site's rules still exist, and
the one that fires is the one whose guard is «rolled over and done», so the
phase costs a single step.

Being trivial it is definable at once (`uSweepSpecDef_nullSpec`), and it needs
no coordinate map – which is the point, a pointer wide enough to name a register
being what no wide machine's control can hold
(`DescriptiveComplexity.Problems.Wide.Limits`). -/
noncomputable def nullSpec (B : Type) : SweepSpec A dt.CtlIx dt.SlotIx B where
  wr _ _ g := g
  st _ f _ := f
  st0 f _ := f
  stRoll _ f _ := f
  nx := id
  Roll _ _ := True
  Done _ _ := True

variable (dt) in
/-- **The file-laying sweep, specified**: write the register's mark, advance the
pointer, roll over at the last tuple of a block and stop at the last register of
the file. -/
noncomputable def buildSpec (zero one : A) (coord : Fin dt.dd → dt.CtlIx) :
    SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) where
  wr := fun b f _ => dt.buildWr zero one coord b f
  st := fun b f _ => dt.ptrNext coord b f
  stRoll := fun b f _ => dt.ptrNext coord b f
  st0 := fun f _ => dt.ctlOf coord f (blkBot A dt.KIx dt.dd).2
  nx := blkNextB A dt.KIx dt.dd
  Roll := fun _ f => dt.ptrTup coord f = tupTop A dt.dd
  Done := fun b f => (b, dt.ptrTup coord f) = blkTop A dt.KIx dt.dd

omit [Finite R'] [Finite P'] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite (Univ A R' P' dt.KIx dt.dd)] in
/-- **A roll-over lands in the next block's first register**, which is what
`DescriptiveComplexity.Draw.SweepSpec.nx` being a function of the block alone
buys: at the last tuple the advance's block is `blkNextB` of the current one. -/
theorem blkNext_fst_of_roll (zero one : A) (coord : Fin dt.dd → dt.CtlIx)
    {b : Option dt.KIx}
    {f : dt.CtlIx → A} (hroll : (dt.buildSpec zero one coord).Roll b f) :
    (blkNext A dt.KIx dt.dd (b, dt.ptrTup coord f)).1 =
      (dt.buildSpec zero one coord).nx b := by
  have hb : (dt.ptrTup coord f) = tupTop A dt.dd := hroll
  rw [hb]
  rfl

end BuildSpec

section GuessSpec

/-! ### What the guessing sweep writes

The guessing phase runs the same sweep over the same stretch with the background
on *both* sides (`DescriptiveComplexity.Draw.Prog.reachesIn_guessTracks`): what
changes at a cell is the stage tracks and nothing else, so the write is the cell
it read with those tracks set to the guessed value, and the value is a *shape* –
one rule per assignment of the tracks – which is the program's only
nondeterminism. -/

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' Q : Type}
variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Finite A] [Nonempty A] [Finite dt.KIx]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable {PR : Prog A R' P' Q dt.SlotIx dt.KIx dt.dd}
variable {I : Type}

variable (dt) in
/-- **What the guessing sweep writes**: the cell it read, with the stage tracks
holding the guessed value. -/
noncomputable def guessWr (zero one : A) (x : dt.d.B.ι → Bool) (g : dt.SlotIx → A) :
    dt.SlotIx → A
  | .old i => bitVal zero one (x i = true)
  | .reg => g .reg
  | .regFirst => g .regFirst
  | .regLast => g .regLast
  | .blk c => g (.blk c)
  | .name j => g (.name j)
  | .pdd => g .pdd
  | .mir => g .mir
  | .tgt => g .tgt
  | .sav => g .sav
  | .val => g .val
  | .wk => g .wk
  | .bot => g .bot
  | .ltp => g .ltp
  | .new i => g (.new i)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A] [Nonempty A]
  [Finite dt.KIx] [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The guess's write installs the guessed tracks**: at the cell under the
head, the background of the state with its stage tracks replaced – which is what
the guessing run asks of the rule, and all it asks. -/
theorem guessWr_eq_passTracks {zero one : A} {hdd : dt.dd0 ≤ dt.dd}
    {lay : Layout dt A R' P' I} {st : TapeSt dt A R' P' I}
    (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {t : dt.SlotIx} (hne : ∀ i : dt.d.B.ι, (Slot.old i : dt.SlotIx) ≠ t)
    {m : I → Prop} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (x : dt.d.B.ι → Bool) (hx : ∀ i, (σ i r ↔ x i = true)) :
    dt.guessWr zero one x
        (PR.passTracksAt lay.cell t (dt.ixBack lay zero one hdd st) m r) =
      PR.passTracksAt lay.cell t
        (dt.ixBack lay zero one hdd { st with old := σ }) m r := by
  funext sl
  cases sl with
  | old i =>
    rw [PR.passTracks_of_ne (hne i) m r]
    exact (bitVal_congr (hx i)).symm
  | _ => rfl

variable (dt) in
/-- **The guessing sweep, specified**: write the guessed stage tracks, advance
the pointer, roll over and stop exactly where the file-laying sweep does – it is
the same walk over the same registers, and only the write differs. -/
noncomputable def guessSpec (zero one : A) (coord : Fin dt.dd → dt.CtlIx) :
    GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool) where
  wr := fun _ x _ g => dt.guessWr zero one x g
  st := fun b _ f _ => dt.ptrNext coord b f
  stRoll := fun b _ f _ => dt.ptrNext coord b f
  nx := blkNextB A dt.KIx dt.dd
  Roll := fun _ f => dt.ptrTup coord f = tupTop A dt.dd
  Done := fun b f => (b, dt.ptrTup coord f) = blkTop A dt.KIx dt.dd

variable (dt) in
/-- **The region-wide guess, specified**: the same write as the file's, and a
pointer that never moves – a control holding `dd₀` coordinates cannot count the
region, so the walk carries no pointer at all. Every step is a *roll-over* that
stays in its own block phase, which is the one arm of the guess site whose guard
is then always true; the walk's end is the site's own stopping rule and not a
test on the control. -/
noncomputable def regionSpec (zero one : A) :
    GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool) where
  wr := fun _ x _ g => dt.guessWr zero one x g
  st := fun _ _ f _ => f
  stRoll := fun _ _ f _ => f
  nx := id
  Roll := fun _ _ => True
  Done := fun _ _ => False

end GuessSpec

end Data

end Draw

end DescriptiveComplexity
