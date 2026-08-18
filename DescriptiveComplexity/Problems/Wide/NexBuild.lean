/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexSpec
import DescriptiveComplexity.Problems.Wide.DrawBuild

/-!
# The clocked program lays its file out

The file-laying phase, assembled: the run
(`DescriptiveComplexity.Draw.Prog.reachesIn_buildFile`) at the layout of
`DescriptiveComplexity.Draw.Data.blkLaid`, the write and the pointer of
`DescriptiveComplexity.Draw.Data.buildSpec`, and the rules of
`DescriptiveComplexity.Draw.Data.nexRule`.

What ties them is that a sweep of the file's stretch **is** a walk of the file:
every address the sweep stops at is some register's cell
(`DescriptiveComplexity.exists_ixSegCell_eq`), and the address it moves to is
the cell of the register the pointer moves to
(`DescriptiveComplexity.wmIncr_ixSegCell`). So the phase and the control at an
address are read off the register that address is – the block into the phase,
the tuple into the control – and the step the sweep asks for is one of the
three rules at that phase, chosen by whether the pointer's tuple is the last of
its block.

What the run asks of the tape outside the stretch is that it be **what the
background says** there, not that it be blank: the marker is planted before the
file is laid, and the marker's cell lies below the file.

The run is `DescriptiveComplexity.Draw.Data.reachesIn_buildBlkFile`, and what
it costs is the stretch: one step per register, which is
`(|K| + 1) · |A| ^ dd₀` of them (`DescriptiveComplexity.card_blkFile`).

The **guessing** phase is the same walk over the same registers, writing at each
the value the certificate has there
(`DescriptiveComplexity.Draw.Data.reachesIn_guessBlkTracks`); it exists for
every certificate, which is what makes it a guess. Only the write differs, so
the two share the pointer, the phase family and the step's case analysis.

After either sweep the machine stands one cell past the file: it steps back onto
the last register (`DescriptiveComplexity.Draw.Data.step_doneBack`) and walks
down to the marker (`reachesIn_homeAfterBuild`), which is
`DescriptiveComplexity.Draw.HomeKit`'s walk at the file's own top.

The three chain into `DescriptiveComplexity.Draw.Data.reachesIn_buildPhase`,
whose budget is `2 · card + base`: the stretch out and back, the turn-around,
and the descent from the file's foot to the marker.
`DescriptiveComplexity.Draw.Data.reachesIn_guessPhase` is the guess's copy of
that, at the same number – it is the same walk.

The three single steps that join the phases are here as well:
`DescriptiveComplexity.Draw.Data.step_startBuild` plants the marker and enters
the file, `step_homeBuildExit` turns round at the marker and re-enters it for
the guess, and `step_homeGuessExit` enters the evaluation. The whole opening is
those five legs, and `DescriptiveComplexity.TMData.reachesIn_five` adds them up:
twice a phase and three steps.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section BuildRun

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

/-- **The register an address is**, where it is one: what the pointer holds when
the sweep stands there. -/
noncomputable def regAt {I : Type} (F : LaidFile dt A R' P' I) (dflt : I)
    (r : Univ A R' P' dt.KIx dt.dd → Prop) : I :=
  open Classical in
  if h : ∃ v : I, r = F.cell v then h.choose else dflt

/-- At a register's cell it is that register. -/
theorem regAt_cell {I : Type} {F : LaidFile dt A R' P' I}
    (hinj : Function.Injective F.cell) (dflt : I) (v : I) :
    regAt F dflt (F.cell v) = v := by
  classical
  have hex : ∃ w : I, F.cell v = F.cell w := ⟨v, rfl⟩
  rw [regAt, dif_pos hex]
  exact (hinj hex.choose_spec).symm

/-! ### The step the sweep asks for, at a register -/

section Step

variable {SE PE G : Type} {ShE : SE → Type} [Fintype dt.CtlIx] [Fintype dt.SlotIx]
variable [DecidableEq dt.SlotIx] [Nonempty A] [Finite A] [Finite dt.KIx]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {coord : Fin dt.dd → dt.CtlIx} {f₀ : dt.CtlIx → A}
variable {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}
variable {evalEntry : PE} {bot : Option dt.KIx}
variable {rEmb : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
variable (hrules : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
  PR.rules (rEmb i ρ) =
    dt.nexRule PR.one (dt.buildSpec PR.zero PR.one coord) γ ruleE evalEntry bot i ρ)

include hrules

omit [LinearOrder R'] in
/-- **The file-laying sweep's step at a register short of the last**: whichever
of the two rules the pointer's tuple selects – stay in the block, or roll over
into the next – it writes the register's mark, advances the pointer to the next
register and moves right. Which one fired is invisible from here, which is what
lets the run treat the sweep as one step per register. -/
theorem hasRight_buildAt (hcoord : Function.Injective coord)
    (v : Wide.BlkIx dt.KIx A dt.dd) (hv : v ≠ blkTop A dt.KIx dt.dd)
    (g : dt.SlotIx → A) :
    PR.HasRight (NexPh.buildP v.1) (dt.ctlOf coord f₀ v.2) g
      (NexPh.buildP (blkNext A dt.KIx dt.dd v).1)
      (dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd v).2)
      (dt.buildWr PR.zero PR.one coord v.1 (dt.ctlOf coord f₀ v.2)) := by
  have hst : dt.ptrNext coord v.1 (dt.ctlOf coord f₀ v.2) =
      dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd v).2 := by
    rw [dt.ptrNext_ctlOf hcoord f₀ v.1 v.2]
  by_cases hroll : dt.ptrTup coord (dt.ctlOf coord f₀ v.2) = tupTop A dt.dd
  · have hdone : ¬((v.1, dt.ptrTup coord (dt.ctlOf coord f₀ v.2)) =
        blkTop A dt.KIx dt.dd) := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2]
      exact fun hc => hv hc
    have hveta : ((v.1, dt.ptrTup coord (dt.ctlOf coord f₀ v.2)) :
        Wide.BlkIx dt.KIx A dt.dd) = v := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2]
    have hfst : (blkNext A dt.KIx dt.dd v).1 =
        (dt.buildSpec PR.zero PR.one coord).nx v.1 := by
      have h := dt.blkNext_fst_of_roll PR.zero PR.one coord
        (b := v.1) (f := dt.ctlOf coord f₀ v.2) hroll
      rwa [hveta] at h
    rw [hfst, ← hst]
    exact hasRight_buildRoll hrules v.1 _ g hroll hdone
  · have hne : v.2 ≠ tupTop A dt.dd := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2] at hroll
      exact hroll
    have hfst : (blkNext A dt.KIx dt.dd v).1 = v.1 :=
      blkNext_fst_of_ne_tupTop A dt.KIx dt.dd hne
    rw [hfst, ← hst]
    exact hasRight_build hrules v.1 _ g hroll

omit [LinearOrder R'] in
/-- **The step at the last register**: the same write and the same advance, into
the phase one cell past the file, where the machine turns round. -/
theorem hasRight_buildAtTop (hcoord : Function.Injective coord)
    (g : dt.SlotIx → A) :
    PR.HasRight (NexPh.buildP (blkTop A dt.KIx dt.dd).1)
      (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) g
      NexPh.buildDoneP
      (dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd (blkTop A dt.KIx dt.dd)).2)
      (dt.buildWr PR.zero PR.one coord (blkTop A dt.KIx dt.dd).1
        (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)) := by
  have hroll : dt.ptrTup coord (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) =
      tupTop A dt.dd := by
    rw [dt.ptrTup_ctlOf hcoord f₀ _]
    exact snd_blkTop A dt.KIx dt.dd
  have hdone : ((blkTop A dt.KIx dt.dd).1,
      dt.ptrTup coord (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)) =
      blkTop A dt.KIx dt.dd := by
    rw [dt.ptrTup_ctlOf hcoord f₀ _]
  have hst : dt.ptrNext coord (blkTop A dt.KIx dt.dd).1
      (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) =
      dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd (blkTop A dt.KIx dt.dd)).2 := by
    rw [dt.ptrNext_ctlOf hcoord f₀ _ _]
  rw [← hst]
  exact hasRight_buildLast hrules (blkTop A dt.KIx dt.dd).1 _ g hroll hdone

end Step

/-! ### The phase and the control at an address -/

section Families

variable {PE : Type} [LinearOrder (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable {I : Type}
variable (F : LaidFile dt A R' (NexPh (Option dt.KIx) PE) I) (dflt : I)
variable (coord : Fin dt.dd → dt.CtlIx) (f₀ : dt.CtlIx → A)

/-- **The phase at an address**: the sweep's phase at the block of the register
it is, and the turn-around phase off the file – which is where the sweep's last
step lands. Both sweeps use it, at their own two phases. -/
noncomputable def phAt {J : Type}
    (G : LaidFile dt A R' (NexPh (Option dt.KIx) PE) J) (blk : J → Option dt.KIx)
    (inb : Option dt.KIx → NexPh (Option dt.KIx) PE)
    (done : NexPh (Option dt.KIx) PE)
    (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    NexPh (Option dt.KIx) PE :=
  open Classical in
  if h : ∃ v : J, r = G.cell v then inb (blk h.choose) else done

/-- **The control at an address**: the pointer holding the tuple of the register
it is. -/
noncomputable def fcAt (tup : I → Fin dt.dd → A)
    (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) : dt.CtlIx → A :=
  dt.ctlOf coord f₀ (tup (regAt F dflt r))

variable {F dflt coord f₀}

/-- At a register's cell the phase is that register's block. -/
theorem phAt_cell (hinj : Function.Injective F.cell) (blk : I → Option dt.KIx)
    (inb : Option dt.KIx → NexPh (Option dt.KIx) PE)
    (done : NexPh (Option dt.KIx) PE) (v : I) :
    phAt F blk inb done (F.cell v) = inb (blk v) := by
  classical
  have hex : ∃ w : I, F.cell v = F.cell w := ⟨v, rfl⟩
  rw [phAt, dif_pos hex]
  exact congrArg (fun w => inb (blk w)) (hinj hex.choose_spec).symm

/-- Off the file the phase is the turn-around one. -/
theorem phAt_not_cell {blk : I → Option dt.KIx}
    {inb : Option dt.KIx → NexPh (Option dt.KIx) PE}
    {done : NexPh (Option dt.KIx) PE}
    {r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : ∀ v : I, r ≠ F.cell v) : phAt F blk inb done r = done :=
  dif_neg fun hc => hr hc.choose hc.choose_spec

/-- At a register's cell the control holds that register's tuple. -/
theorem fcAt_cell (hinj : Function.Injective F.cell) (tup : I → Fin dt.dd → A)
    (v : I) : dt.fcAt F dflt coord f₀ tup (F.cell v) = dt.ctlOf coord f₀ (tup v) := by
  rw [fcAt, regAt_cell hinj]

/-- Off the file the control holds the default register's tuple. -/
theorem fcAt_not_cell {tup : I → Fin dt.dd → A}
    {r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : ∀ v : I, r ≠ F.cell v) :
    dt.fcAt F dflt coord f₀ tup r = dt.ctlOf coord f₀ (tup dflt) := by
  rw [fcAt, regAt, dif_neg fun hc => hr hc.choose hc.choose_spec]

end Families

/-! ### The written symbol -/

section Written

variable {PE : Type} [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]
variable [LinearOrder (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite (NexPh (Option dt.KIx) PE)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] in
/-- **The sweep's write is the symbol the run asks for**: the background of the
file at the register's cell, presented along the walked track. The track carries
no register digit – the file is being laid, nothing is marked yet – so what the
presentation adds is the blank the mark already has there. -/
theorem buildWr_eq_passTracks {coord : Fin dt.dd → dt.CtlIx}
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos hbase).cell v))
    (hbot : ∀ v, ¬st.bot ((dt.blkLaid h hpos hbase).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos hbase).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos hbase).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos hbase).cell v))
    (v : Wide.BlkIx dt.KIx A dt.dd) (f : dt.CtlIx → A)
    (hf : dt.ptrTup coord f = v.2) :
    dt.buildWr PR.zero PR.one coord v.1 f =
      PR.passTracksAt (dt.blkLaid h hpos hbase).cell Slot.mir
        (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one dt.dd0Le st)
        (fun _ => False) ((dt.blkLaid h hpos hbase).cell v) := by
  have hveta : ((v.1, dt.ptrTup coord f) : Wide.BlkIx dt.KIx A dt.dd) = v := by
    rw [hf]
  have hbg := dt.buildWr_eq_ixBack (zero := PR.zero) (one := PR.one) coord dt.dd0Le
    h hpos hbase hmir htgt hsav hval hwk hbot hltp hold hnew v.1 f
  rw [hveta] at hbg
  funext sl
  rw [Prog.passTracksAt]
  by_cases hs : sl = Slot.mir
  · subst hs
    rw [if_pos rfl, bitVal_neg (fun hc => hc.choose_spec.2)]
    rfl
  · rw [if_neg hs, hbg]

end Written

/-! ### The run -/

section Run

variable {SE PE G : Type} {ShE : SE → Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]
variable [LinearOrder (NexPh (Option dt.KIx) PE)] [Finite (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {coord : Fin dt.dd → dt.CtlIx} {f₀ : dt.CtlIx → A}
variable {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}
variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}
variable {evalEntry : PE} {bot : Option dt.KIx}
variable {rEmb : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
variable (hrules : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
  PR.rules (rEmb i ρ) =
    dt.nexRule PR.one (dt.buildSpec PR.zero PR.one coord) γ ruleE evalEntry bot i ρ)

include hrules

omit [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] in
/-- **The step of the file-laying sweep, at an arbitrary address of the
stretch**: the address is some register's cell, and the rule at that register
writes its mark, advances the pointer and moves right – onto the next register's
cell, or, at the last, onto the address past the file. -/
theorem hasRight_buildSweep (hcoord : Function.Injective coord)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hbot : ∀ v, ¬st.bot ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    {bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (s u : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop)
    (hi : WMIncr WMLe s u)
    (hlb : WMSetLe WMLe
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) s)
    (hub : WMSetLe WMLe u
      (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base)) :
    PR.HasRight
      (phAt (dt.blkLaid h hpos (le_of_lt hbase)) Prod.fst NexPh.buildP
        NexPh.buildDoneP s)
      (dt.fcAt (dt.blkLaid h hpos (le_of_lt hbase)) (blkTop A dt.KIx dt.dd)
        coord f₀ Prod.snd s)
      (PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
        bg₀ (fun _ => False) s)
      (phAt (dt.blkLaid h hpos (le_of_lt hbase)) Prod.fst NexPh.buildP
        NexPh.buildDoneP u)
      (dt.fcAt (dt.blkLaid h hpos (le_of_lt hbase)) (blkTop A dt.KIx dt.dd)
        coord f₀ Prod.snd u)
      (PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
        (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
          dt.dd0Le st) (fun _ => False) s) := by
  classical
  set F := dt.blkLaid h hpos (le_of_lt hbase) with hF
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have hinj : Function.Injective F.cell :=
    (blkFile A dt.KIx (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) dt.dd h hpos
      (le_of_lt hbase)).injective hlin
  -- the address the sweep stands on is a register's cell
  have hrs : wideRank s < base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) := by
    have h1 : wideRank s < wideRank u := (wideRank_lt_iff h _ _).mpr
      ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩)
    have h2 : wideRank u ≤ wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) :=
      wideRank_mono h hub
    have h3 := wideRank_ixSegTop (I := Wide.BlkIx dt.KIx A dt.dd) h hbase
    omega
  have hls : base ≤ wideRank s := by
    have h1 : wideRank (F.cell (blkBot A dt.KIx dt.dd)) ≤ wideRank s :=
      wideRank_mono h hlb
    have h2 : wideRank (F.cell (blkBot A dt.KIx dt.dd)) =
        base + ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd) :=
      wideRank_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h (le_of_lt hbase) _
    rw [ixRank_of_bot hlin (blkLe_blkBot A dt.KIx dt.dd)] at h2
    omega
  obtain ⟨v, hv⟩ := exists_ixSegCell_eq (Wide.blkLe dt.KIx A dt.dd) h hlin
    (le_of_lt hbase) hls hrs
  have hvc : s = F.cell v := hv.symm
  subst hvc
  by_cases htop : v = blkTop A dt.KIx dt.dd
  · subst htop
    have hu : u = ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base :=
      wmIncr_functional h hi (wmIncr_ixSegCell_top (Wide.blkLe dt.KIx A dt.dd) h hlin
        hbase (blkLe_blkTop A dt.KIx dt.dd))
    subst hu
    have hnotcell : ∀ w : Wide.BlkIx dt.KIx A dt.dd,
        ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base ≠ F.cell w :=
      ixSegTop_ne_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase
    rw [phAt_cell hinj, fcAt_cell hinj, phAt_not_cell hnotcell,
      fcAt_not_cell hnotcell,
      dt.buildWr_eq_passTracks h hpos (le_of_lt hbase) hmir htgt hsav hval hwk hbot
        hltp hold hnew (blkTop A dt.KIx dt.dd) _ (dt.ptrTup_ctlOf hcoord f₀ _) |>.symm]
    have hlem := dt.hasRight_buildAtTop (f₀ := f₀) hrules hcoord
      (PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False)
        (F.cell (blkTop A dt.KIx dt.dd)))
    rw [blkNext_of_top A dt.KIx dt.dd (blkLe_blkTop A dt.KIx dt.dd)] at hlem
    exact hlem
  · have hu : u = F.cell (blkNext A dt.KIx dt.dd v) :=
      wmIncr_functional h hi (wmIncr_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hlin
        (le_of_lt hbase) (ixSucc_blkNext_of_ne A dt.KIx dt.dd htop))
    subst hu
    rw [phAt_cell hinj, fcAt_cell hinj, phAt_cell hinj, fcAt_cell hinj,
      dt.buildWr_eq_passTracks h hpos (le_of_lt hbase) hmir htgt hsav hval hwk hbot
        hltp hold hnew v _ (dt.ptrTup_ctlOf hcoord f₀ _) |>.symm]
    exact dt.hasRight_buildAt hrules hcoord v htop _

/-- **The clocked program lays its file out**: from the first register's cell to
the address one past the last, one step per register, turning the blank the tape
starts with into the background of the file it has built.

The run is `DescriptiveComplexity.Draw.Prog.reachesIn_buildFile`'s, at the layout
of a clocked program's file, with the write and the pointer of
`DescriptiveComplexity.Draw.Data.buildSpec` and the rules of
`DescriptiveComplexity.Draw.Data.nexRule`; what it costs is the stretch, one
step per register. -/
theorem reachesIn_buildBlkFile (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hbot : ∀ v, ¬st.bot ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    {bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hbelow : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      WMSetLt WMLe r
          ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r)
    (habove : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) -
        wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)))
      ⟨Sum.inr (PR.stElt (NexPh.buildP (blkBot A dt.KIx dt.dd).1)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir bg₀ (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.buildDoneP
          (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)),
        Sum.inl (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩ := by
  classical
  set F := dt.blkLaid h hpos (le_of_lt hbase) with hF
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have hinj : Function.Injective F.cell :=
    (blkFile A dt.KIx (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) dt.dd h hpos
      (le_of_lt hbase)).injective hlin
  have hnotcell : ∀ w : Wide.BlkIx dt.KIx A dt.dd,
      ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base ≠ F.cell w :=
    ixSegTop_ne_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase
  have hrun := Prog.reachesIn_installOut (cell := F.cell) hR h
    (ph := phAt F Prod.fst NexPh.buildP NexPh.buildDoneP)
    (fc := dt.fcAt F (blkTop A dt.KIx dt.dd) coord f₀ Prod.snd)
    (t := Slot.mir) (m := fun _ => False) (bg₀ := bg₀)
    (bg₁ := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (s₀ := F.cell (blkBot A dt.KIx dt.dd))
    (s₁ := ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base)
    (Or.inr (wmSetLt_ixSegTop (Wide.blkLe dt.KIx A dt.dd) h hbase _))
    hbelow habove
    (fun s u hi hlb hub => dt.hasRight_buildSweep hrules hcoord h hpos hbase hmir htgt
      hsav hval hwk hbot hltp hold hnew s u hi hlb hub)
  rwa [phAt_cell hinj, fcAt_cell hinj, phAt_not_cell hnotcell,
    fcAt_not_cell hnotcell] at hrun

/-! ### The guessing sweep

The same walk over the same registers, with `DescriptiveComplexity.Draw.Data.guessSpec`
in place of `buildSpec`: what changes at a cell is the stage tracks, and which
value is written there is a *shape* of the rule, so the sweep is the program's
one nondeterministic phase. The steps below are the build's with the guessed
value carried along. -/

section Guess

variable {γ' : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool)}
variable {β' : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
variable {rEmbG : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
variable (hrulesG : ∀ (i : NexSite SE)
    (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
  PR.rules (rEmbG i ρ) =
    dt.nexRule PR.one β' (dt.guessSpec PR.zero PR.one coord) ruleE evalEntry bot i ρ)

include hrulesG

omit hrules [LinearOrder R'] [LinearOrder (NexPh (Option dt.KIx) PE)]
  [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] in
/-- **The guessing sweep's step at a register short of the last**, at one
value. -/
theorem hasRight_guessAt (hcoord : Function.Injective coord)
    (v : Wide.BlkIx dt.KIx A dt.dd) (hv : v ≠ blkTop A dt.KIx dt.dd)
    (x : dt.d.B.ι → Bool) (g : dt.SlotIx → A) :
    PR.HasRight (NexPh.guessP v.1) (dt.ctlOf coord f₀ v.2) g
      (NexPh.guessP (blkNext A dt.KIx dt.dd v).1)
      (dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd v).2)
      (dt.guessWr PR.zero PR.one x g) := by
  have hst : dt.ptrNext coord v.1 (dt.ctlOf coord f₀ v.2) =
      dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd v).2 := by
    rw [dt.ptrNext_ctlOf hcoord f₀ v.1 v.2]
  by_cases hroll : dt.ptrTup coord (dt.ctlOf coord f₀ v.2) = tupTop A dt.dd
  · have hdone : ¬((v.1, dt.ptrTup coord (dt.ctlOf coord f₀ v.2)) =
        blkTop A dt.KIx dt.dd) := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2]
      exact fun hc => hv hc
    have hveta : ((v.1, dt.ptrTup coord (dt.ctlOf coord f₀ v.2)) :
        Wide.BlkIx dt.KIx A dt.dd) = v := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2]
    have hfst : (blkNext A dt.KIx dt.dd v).1 =
        (dt.guessSpec PR.zero PR.one coord).nx v.1 := by
      have hb := dt.blkNext_fst_of_roll PR.zero PR.one coord
        (b := v.1) (f := dt.ctlOf coord f₀ v.2) hroll
      rwa [hveta] at hb
    rw [hfst, ← hst]
    exact hasRight_guessRoll hrulesG v.1 x _ g hroll hdone
  · have hne : v.2 ≠ tupTop A dt.dd := by
      rw [dt.ptrTup_ctlOf hcoord f₀ v.2] at hroll
      exact hroll
    have hfst : (blkNext A dt.KIx dt.dd v).1 = v.1 :=
      blkNext_fst_of_ne_tupTop A dt.KIx dt.dd hne
    rw [hfst, ← hst]
    exact hasRight_guess hrulesG v.1 x _ g hroll

omit hrules [LinearOrder R'] [LinearOrder (NexPh (Option dt.KIx) PE)]
  [Language.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] in
/-- **The guessing sweep's step at the last register.** -/
theorem hasRight_guessAtTop (hcoord : Function.Injective coord)
    (x : dt.d.B.ι → Bool) (g : dt.SlotIx → A) :
    PR.HasRight (NexPh.guessP (blkTop A dt.KIx dt.dd).1)
      (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) g
      NexPh.guessDoneP
      (dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd (blkTop A dt.KIx dt.dd)).2)
      (dt.guessWr PR.zero PR.one x g) := by
  have hroll : dt.ptrTup coord (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) =
      tupTop A dt.dd := by
    rw [dt.ptrTup_ctlOf hcoord f₀ _]
    exact snd_blkTop A dt.KIx dt.dd
  have hdone : ((blkTop A dt.KIx dt.dd).1,
      dt.ptrTup coord (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)) =
      blkTop A dt.KIx dt.dd := by
    rw [dt.ptrTup_ctlOf hcoord f₀ _]
  have hst : dt.ptrNext coord (blkTop A dt.KIx dt.dd).1
      (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2) =
      dt.ctlOf coord f₀ (blkNext A dt.KIx dt.dd (blkTop A dt.KIx dt.dd)).2 := by
    rw [dt.ptrNext_ctlOf hcoord f₀ _ _]
  rw [← hst]
  exact hasRight_guessLast hrulesG (blkTop A dt.KIx dt.dd).1 x _ g hroll hdone

omit hrules [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] in
/-- **The step of the guessing sweep, at an arbitrary address of the stretch**:
the address is some register's cell, and the rule at that register writes the
value the certificate has there onto the stage tracks, advances the pointer and
moves right. Which value it is, is the shape – the program's one guess. -/
theorem hasRight_guessSweep (hcoord : Function.Injective coord)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (s u : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop)
    (hi : WMIncr WMLe s u)
    (hlb : WMSetLe WMLe
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) s)
    (hub : WMSetLe WMLe u (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base)) :
    PR.HasRight
      (phAt (dt.blkLaid h hpos (le_of_lt hbase)) Prod.fst NexPh.guessP
        NexPh.guessDoneP s)
      (dt.fcAt (dt.blkLaid h hpos (le_of_lt hbase)) (blkTop A dt.KIx dt.dd)
        coord f₀ Prod.snd s)
      (PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
        (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
          dt.dd0Le st) (fun _ => False) s)
      (phAt (dt.blkLaid h hpos (le_of_lt hbase)) Prod.fst NexPh.guessP
        NexPh.guessDoneP u)
      (dt.fcAt (dt.blkLaid h hpos (le_of_lt hbase)) (blkTop A dt.KIx dt.dd)
        coord f₀ Prod.snd u)
      (PR.passTracksAt (dt.blkLaid h hpos (le_of_lt hbase)).cell Slot.mir
        (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
          dt.dd0Le { st with old := σ }) (fun _ => False) s) := by
  classical
  set F := dt.blkLaid h hpos (le_of_lt hbase) with hF
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have hinj : Function.Injective F.cell :=
    (blkFile A dt.KIx (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) dt.dd h hpos
      (le_of_lt hbase)).injective hlin
  have hrs : wideRank s < base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) := by
    have h1 : wideRank s < wideRank u := (wideRank_lt_iff h _ _).mpr
      ((wmSetLt_iff _ _).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩)
    have h2 : wideRank u ≤ wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) :=
      wideRank_mono h hub
    have h3 := wideRank_ixSegTop (I := Wide.BlkIx dt.KIx A dt.dd) h hbase
    omega
  have hls : base ≤ wideRank s := by
    have h1 : wideRank (F.cell (blkBot A dt.KIx dt.dd)) ≤ wideRank s :=
      wideRank_mono h hlb
    have h2 : wideRank (F.cell (blkBot A dt.KIx dt.dd)) =
        base + ixRank (Wide.blkLe dt.KIx A dt.dd) (blkBot A dt.KIx dt.dd) :=
      wideRank_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h (le_of_lt hbase) _
    rw [ixRank_of_bot hlin (blkLe_blkBot A dt.KIx dt.dd)] at h2
    omega
  obtain ⟨v, hv⟩ := exists_ixSegCell_eq (Wide.blkLe dt.KIx A dt.dd) h hlin
    (le_of_lt hbase) hls hrs
  have hvc : s = F.cell v := hv.symm
  subst hvc
  -- the value the certificate has at this cell
  have hwr := dt.guessWr_eq_passTracks (PR := PR) (lay := F.toLayout) (st := st)
    (zero := PR.zero) (one := PR.one) (hdd := dt.dd0Le) σ
    (t := Slot.mir) (fun i hc => nomatch hc) (m := fun _ => False)
    (r := F.cell v) (fun i => decide (σ i (F.cell v))) (fun i => by simp)
  by_cases htop : v = blkTop A dt.KIx dt.dd
  · subst htop
    have hu : u = ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base :=
      wmIncr_functional h hi (wmIncr_ixSegCell_top (Wide.blkLe dt.KIx A dt.dd) h hlin
        hbase (blkLe_blkTop A dt.KIx dt.dd))
    subst hu
    have hnotcell : ∀ w : Wide.BlkIx dt.KIx A dt.dd,
        ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base ≠ F.cell w :=
      ixSegTop_ne_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase
    rw [phAt_cell hinj, fcAt_cell hinj, phAt_not_cell hnotcell,
      fcAt_not_cell hnotcell, ← hwr]
    have hlem := dt.hasRight_guessAtTop (f₀ := f₀) hrulesG hcoord
      (fun i => decide (σ i (F.cell (blkTop A dt.KIx dt.dd))))
      (PR.passTracksAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False)
        (F.cell (blkTop A dt.KIx dt.dd)))
    rw [blkNext_of_top A dt.KIx dt.dd (blkLe_blkTop A dt.KIx dt.dd)] at hlem
    exact hlem
  · have hu : u = F.cell (blkNext A dt.KIx dt.dd v) :=
      wmIncr_functional h hi (wmIncr_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hlin
        (le_of_lt hbase) (ixSucc_blkNext_of_ne A dt.KIx dt.dd htop))
    subst hu
    rw [phAt_cell hinj, fcAt_cell hinj, phAt_cell hinj, fcAt_cell hinj, ← hwr]
    exact dt.hasRight_guessAt hrulesG hcoord v htop _
      (PR.passTracksAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) (F.cell v))

omit hrules in
/-- **The clocked program guesses its certificate**: the same walk over the same
registers as the file-laying sweep, writing at each the value the certificate
has there. Which value that is, is the rule's shape, so the run exists for
*every* certificate – which is what makes the phase a guess and the program
nondeterministic exactly here. -/
theorem reachesIn_guessBlkTracks (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r
          ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) ∨
        ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) →
      (σ i r ↔ st.old i r)) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) -
        wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)))
      ⟨Sum.inr (PR.stElt (NexPh.guessP (blkBot A dt.KIx dt.dd).1)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.guessDoneP
          (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)),
        Sum.inl (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le { st with old := σ }) (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
  classical
  set F := dt.blkLaid h hpos (le_of_lt hbase) with hF
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have hinj : Function.Injective F.cell :=
    (blkFile A dt.KIx (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) dt.dd h hpos
      (le_of_lt hbase)).injective hlin
  have hnotcell : ∀ w : Wide.BlkIx dt.KIx A dt.dd,
      ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base ≠ F.cell w :=
    ixSegTop_ne_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase
  have hrun := Prog.reachesIn_guessTracks F hR h (hdd := dt.dd0Le) (st := st) σ
    (ph := phAt F Prod.fst NexPh.guessP NexPh.guessDoneP)
    (fc := dt.fcAt F (blkTop A dt.KIx dt.dd) coord f₀ Prod.snd)
    (t := Slot.mir) (m := fun _ => False)
    (s₀ := F.cell (blkBot A dt.KIx dt.dd))
    (s₁ := ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base)
    (Or.inr (wmSetLt_ixSegTop (Wide.blkLe dt.KIx A dt.dd) h hbase _))
    hout
    (fun s u hi hlb hub => dt.hasRight_guessSweep hrulesG hcoord h hpos hbase σ s u
      hi hlb hub)
  rwa [phAt_cell hinj, fcAt_cell hinj, phAt_not_cell hnotcell,
    fcAt_not_cell hnotcell] at hrun

end Guess

/-! ### The turn-around and the walk home -/

section Home

omit hrules in
/-- **The turn-around after a sweep**: standing one cell past the file in the
done phase, the machine steps back onto the last register, and its walk home
begins there. The step writes nothing, so both sides read the same tape. -/
theorem step_doneBack
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {rest : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    {p p' : NexPh (Option dt.KIx) PE}
    (hex : ∀ g : dt.SlotIx → A, PR.HasLeft p f g p' f g) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt p f),
        Sum.inl (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f),
        Sum.inl ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkTop A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_moveBack hR h
    (wmIncr_ixSegCell_top (Wide.blkLe dt.KIx A dt.dd) h
      (Wide.isLinOrd_blkLe dt.KIx A dt.dd) hbase (blkLe_blkTop A dt.KIx dt.dd))
    (fun _ _ => rfl) (hex _)

omit hrules in
/-- **The walk home after a sweep**: from the last register down to the marker,
one step per address, the tape riding along. -/
theorem reachesIn_homeAfterBuild
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v) {f : dt.CtlIx → A}
    {ph : NexPh (Option dt.KIx) PE} {rHome : HomeKit.HomeRule → R'}
    (hrulesH : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHome ρ) = (HomeKit.mk Slot.mir Slot.wk ph).rule PR.one ρ)
    (hle : WMSetLe WMLe v
      ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd))) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)) -
        wideRank v)
      ⟨Sum.inr (PR.stElt ph f),
        Sum.inl ((dt.blkLaid h hpos hbase).cell (blkTop A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one
            dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt ph f), Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          (dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one
            dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩ :=
  HomeKit.reachesIn (κ := HomeKit.mk Slot.mir Slot.wk ph) (rEmb := rHome)
    (dt.blkLaid h hpos hbase).toIxFile hrulesH hR h (fun hc => nomatch hc)
    (m := fun _ => False) (fc := f)
    (fun r => by
      change dt.ixBack _ PR.zero PR.one dt.dd0Le st r Slot.wk = _
      rw [show dt.ixBack (dt.blkLaid h hpos hbase).toLayout PR.zero PR.one
        dt.dd0Le st r Slot.wk = bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hle

omit hrules in
/-- **The whole opening phase**: from the first register's cell with the pointer
at the first register, the machine lays the file out, turns round one cell past
it, and walks home to the marker – in twice the file's length and its base,
which is the stretch out and back with the turn-around and the descent below the
file. -/
theorem reachesIn_buildPhase (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (hmir : ∀ u, ¬st.mir u) (htgt : ∀ u, ¬st.tgt u) (hsav : ∀ u, ¬st.sav u)
    (hval : ∀ u, ¬st.val u)
    (hwk : ∀ v, ¬st.wk ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hbot : ∀ v, ¬st.bot ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hltp : ∀ v, ¬st.ltp ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hold : ∀ i v, ¬st.old i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    (hnew : ∀ i v, ¬st.new i ((dt.blkLaid h hpos (le_of_lt hbase)).cell v))
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v) (hv0 : wideRank v = 0)
    (hle : WMSetLe WMLe v
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    {bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hbelow : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      WMSetLt WMLe r
          ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r)
    (habove : ∀ r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop,
      ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) →
      dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero PR.one
        dt.dd0Le st r = bg₀ r)
    {rEmbB : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    (hrulesB : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbB i ρ) =
        dt.nexRule PR.one (dt.buildSpec PR.zero PR.one coord) γ ruleE evalEntry bot i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + base)
      ⟨Sum.inr (PR.stElt (NexPh.buildP (blkBot A dt.KIx dt.dd).1)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir bg₀ (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP
          (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)),
        Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩ := by
  have hsweep := dt.reachesIn_buildBlkFile (f₀ := f₀) hrulesB hcoord hR h hpos hbase
    hmir htgt hsav hval hwk hbot hltp hold hnew hbelow habove
  have hturn := dt.step_doneBack hR h hpos hbase (m := fun _ => False)
    (rest := dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero
      PR.one dt.dd0Le st)
    (f := dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
    (fun g => hasLeft_buildExit hrulesB _ g)
  have hhome := dt.reachesIn_homeAfterBuild hR h hpos (le_of_lt hbase) hwkS
    (f := dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
    (rHome := fun ρ => rEmbB .homeBuild (Sum.inl ρ))
    (fun ρ => hrulesB .homeBuild (Sum.inl ρ)) hle
  refine ((hsweep.trans ((TMData.reachesIn_of_step hturn).trans hhome))).mono ?_
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have h1 : wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) -
      wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
        (blkBot A dt.KIx dt.dd)) = Nat.card (Wide.BlkIx dt.KIx A dt.dd) :=
    wideRank_ixSegTop_sub_bot (Wide.blkLe dt.KIx A dt.dd) h hlin hbase
      (blkLe_blkBot A dt.KIx dt.dd)
  have h2 : wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
        (blkTop A dt.KIx dt.dd)) + 1 =
      base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) :=
    wideRank_ixSegCell_top (Wide.blkLe dt.KIx A dt.dd) h hlin
      (le_of_lt hbase) (blkLe_blkTop A dt.KIx dt.dd)
  rw [hv0]
  omega

omit hrules in
/-- **The whole guessing phase**: the same three legs at the guess's own phases,
and the same count – the guess is the file-laying walk with a different write,
so it costs exactly what that one costs. -/
theorem reachesIn_guessPhase (hcoord : Function.Injective coord)
    (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) <
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)}
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : ({ st with old := σ } :
      TapeSt dt A R' (NexPh (Option dt.KIx) PE) (Wide.BlkIx dt.KIx A dt.dd)).wk =
      fun r => r = v)
    (hv0 : wideRank v = 0)
    (hle : WMSetLe WMLe v
      ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkTop A dt.KIx dt.dd)))
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r
          ((dt.blkLaid h hpos (le_of_lt hbase)).cell (blkBot A dt.KIx dt.dd)) ∨
        ¬WMSetLt WMLe r (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) →
      (σ i r ↔ st.old i r))
    {rEmbG2 : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    {betaG : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesG2 : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmbG2 i ρ) =
        dt.nexRule PR.one betaG (dt.guessSpec PR.zero PR.one coord) ruleE evalEntry
          bot i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (2 * Nat.card (Wide.BlkIx dt.KIx A dt.dd) + base)
      ⟨Sum.inr (PR.stElt (NexPh.guessP (blkBot A dt.KIx dt.dd).1)
          (dt.ctlOf coord f₀ (blkBot A dt.KIx dt.dd).2)),
        Sum.inl ((dt.blkLaid h hpos (le_of_lt hbase)).cell
          (blkBot A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le st) (fun _ => False)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP
          (dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)),
        Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos (le_of_lt hbase)).cell
          Slot.mir (dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout
            PR.zero PR.one dt.dd0Le { st with old := σ }) (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
  have hsweep := dt.reachesIn_guessBlkTracks (f₀ := f₀) hrulesG2 hcoord hR h hpos hbase
    σ hout
  have hturn := dt.step_doneBack hR h hpos hbase (m := fun _ => False)
    (rest := dt.ixBack (dt.blkLaid h hpos (le_of_lt hbase)).toLayout PR.zero
      PR.one dt.dd0Le { st with old := σ })
    (f := dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
    (fun g => hasLeft_guessExit hrulesG2 _ g)
  have hhome := dt.reachesIn_homeAfterBuild hR h hpos (le_of_lt hbase) hwkS
    (f := dt.ctlOf coord f₀ (blkTop A dt.KIx dt.dd).2)
    (rHome := fun ρ => rEmbG2 .homeGuess (Sum.inl ρ))
    (fun ρ => hrulesG2 .homeGuess (Sum.inl ρ)) hle
  refine ((hsweep.trans ((TMData.reachesIn_of_step hturn).trans hhome))).mono ?_
  have hlin := Wide.isLinOrd_blkLe dt.KIx A dt.dd
  have h1 : wideRank (ixSegTop (Wide.BlkIx dt.KIx A dt.dd) h base) -
      wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
        (blkBot A dt.KIx dt.dd)) = Nat.card (Wide.BlkIx dt.KIx A dt.dd) :=
    wideRank_ixSegTop_sub_bot (Wide.blkLe dt.KIx A dt.dd) h hlin hbase
      (blkLe_blkBot A dt.KIx dt.dd)
  have h2 : wideRank ((dt.blkLaid h hpos (le_of_lt hbase)).cell
        (blkTop A dt.KIx dt.dd)) + 1 =
      base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) :=
    wideRank_ixSegCell_top (Wide.blkLe dt.KIx A dt.dd) h hlin
      (le_of_lt hbase) (blkLe_blkTop A dt.KIx dt.dd)
  rw [hv0]
  omega

omit hrules in
/-- **The opening step**: from the empty address the machine plants the marker
and moves right, into the walk that takes it to the file's base. The base is
*above* the program's data, so it is not the marker's neighbour and the walk is
not a step. -/
theorem step_startBuild (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    {rest rest' :
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    (hframe : ∀ r, r ≠ v → rest' r = rest r)
    (hwr : PR.passTracksAt (dt.blkLaid h hpos hbase).cell Slot.mir rest' m v =
      Function.update (Function.update
        (PR.passTracksAt (dt.blkLaid h hpos hbase).cell Slot.mir rest m v)
        Slot.wk PR.one) Slot.bot PR.one)
    {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS γ ruleE evalEntry (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.start f), Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest' m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR h hvi hframe ?_
  rw [hwr]
  exact hasRight_start hrulesS f _

omit hrules in
/-- **The approach walk**: the machine moves right in one phase, writing
nothing, from wherever the opening step left it up to any address it likes. Its
cost is the stretch it crosses. -/
theorem reachesIn_approachWalk (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {s₀ s₁ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    {rest : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS γ ruleE evalEntry (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₀,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₁,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_of_wideUp h hle fun _ _ hi _ _ =>
    Prog.step_move hR h hi (fun _ _ => rfl) (hasRight_approach hrulesS f _)

omit hrules in
/-- **The approach's exit**: the machine stops walking and moves right into the
phase that lays the first block, so the file's first register is where it has
arrived. -/
theorem step_approachEnter (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {x : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe x
      ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)))
    {rest : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS γ ruleE evalEntry (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl x,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.buildP (blkBot A dt.KIx dt.dd).1) f),
        Sum.inl ((dt.blkLaid h hpos hbase).cell (blkBot A dt.KIx dt.dd)),
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_approachExit hrulesS f _)

omit hrules in
/-- **The dispatch out of the walk home**: at the marker, the machine turns
round and moves right into the guessing phase – the step between the file-laying
phase and the guess. Where it lands is the marker's neighbour, which is where
the guess begins: the certificate lives in the data region, *below* the file. It
writes nothing. -/
theorem step_homeBuildExit (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {v s₀ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v s₀)
    {rest :
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    (hex : dt.exitG PR.one (PR.passTracksAt (dt.blkLaid h hpos hbase).cell
      Slot.mir rest m v))
    {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS γ ruleE evalEntry (blkBot A dt.KIx dt.dd).1 i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP f), Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.guessP (blkBot A dt.KIx dt.dd).1)
          (betaS.st0 f (PR.passTracksAt (dt.blkLaid h hpos hbase).cell
            Slot.mir rest m v))),
        Sum.inl s₀,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeBuildExit hrulesS f _ hex)

omit hrules [Nonempty A] in
/-- **The dispatch into the evaluation**: at the marker after the guess's walk
home, the machine enters the evaluation's first phase one cell to the right. -/
theorem step_homeGuessExit (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) //
        (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Posn p})
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    {rest :
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {m : Wide.BlkIx dt.KIx A dt.dd → Prop} {f : dt.CtlIx → A}
    (hex : dt.exitG PR.one (PR.passTracksAt (dt.blkLaid h hpos hbase).cell
      Slot.mir rest m v))
    {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
    {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
    (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
      PR.rules (rEmbS i ρ) = dt.nexRule PR.one betaS γ ruleE evalEntry bot i ρ) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f), Sum.inl v,
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f), Sum.inl v',
        wideTape (PR.trackTapeAt (dt.blkLaid h hpos hbase).cell Slot.mir
          rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeGuessExit hrulesS f _ hex)

/-! ### The opening's steps, at any file

The five steps above read the file only through the *presentation* of the tape –
`Prog.trackTapeAt cell …` – so they hold at whatever cells a program's file has.
A program that is *handed* its file (`DescriptiveComplexity.WideRegAccept`) uses
them at the channel's cells, where a program that lays one uses them at
`DescriptiveComplexity.Draw.Data.blkLaid`. Nothing but the presentation
changes, and the two sweep sites the steps mention are parameters already. -/

section AnyFile

variable {I : Type} {cell : I → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop)}
variable {m : I → Prop}
variable {rest rest' :
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable {f : dt.CtlIx → A} {botS : Option dt.KIx}
variable {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}
variable {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
variable (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
  PR.rules (rEmbS i ρ) = dt.nexRule PR.one betaS γ ruleE evalEntry botS i ρ)

include hrulesS

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The opening step, at any file**: the machine plants the marker and the
bottom mark at the cell it starts on and moves right into the approach. -/
theorem step_startAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    (hframe : ∀ r, r ≠ v → rest' r = rest r)
    (hwr : PR.passTracksAt cell Slot.mir rest' m v =
      Function.update (Function.update (PR.passTracksAt cell Slot.mir rest m v)
        Slot.wk PR.one) Slot.bot PR.one) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.start f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest' m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR h hvi hframe ?_
  rw [hwr]
  exact hasRight_start hrulesS f _

omit hrules [Nonempty A] in
/-- **The approach walk, at any file**: the machine moves right in one phase,
writing nothing, as far as it likes. -/
theorem reachesIn_approachAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {s₀ s₁ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe s₀ s₁) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_of_wideUp h hle fun _ _ hi _ _ =>
    Prog.step_move hR h hi (fun _ _ => rfl) (hasRight_approach hrulesS f _)

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The approach's exit, at any file**: the machine stops walking and moves
right into the sweep's first phase. -/
theorem step_approachEnterAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {x y : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe x y) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl x,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.buildP botS) f), Sum.inl y,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_approachExit hrulesS f _)

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The dispatch out of the walk home, at any file**: at the marker the
machine turns round into the guessing phase, its pointer reset by the sweep's
own `st0`. -/
theorem step_homeBuildExitAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v s₀ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v s₀)
    (hex : dt.exitG PR.one (PR.passTracksAt cell Slot.mir rest m v)) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.guessP botS)
          (betaS.st0 f (PR.passTracksAt cell Slot.mir rest m v))),
        Sum.inl s₀,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeBuildExit hrulesS f _ hex)

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The dispatch into the evaluation, at any file.** -/
theorem step_homeGuessExitAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    (hex : dt.exitG PR.one (PR.passTracksAt cell Slot.mir rest m v)) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeGuessExit hrulesS f _ hex)

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **A sweep that is over at once, in one step**: when both of the sweep's
tests hold where it starts, the phase fires its exit rule – it writes what the
spec writes and leaves the pointer where the spec's roll-over leaves it, which
for `DescriptiveComplexity.Draw.Data.nullSpec` is nothing and the same
pointer. This is the whole of the file-laying phase of a program that is *handed*
its file. -/
theorem step_sweepDone (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v')
    (hroll : betaS.Roll botS f) (hdone : betaS.Done botS f)
    (hst : betaS.stRoll botS f (PR.passTracksAt cell Slot.mir rest m v) = f)
    (hwr : betaS.wr botS f (PR.passTracksAt cell Slot.mir rest m v) =
      PR.passTracksAt cell Slot.mir rest m v) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.buildP botS) f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.buildDoneP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR h hvi (fun _ _ => rfl) ?_
  have hstep := hasRight_buildLast (PR := PR) (rEmb := rEmbS) (β := betaS) (γ := γ)
    (ruleE := ruleE) (evalEntry := evalEntry) (bot := botS) hrulesS botS f
    (PR.passTracksAt cell Slot.mir rest m v) hroll hdone
  rw [hst, hwr] at hstep
  exact hstep

omit hrules [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The turn-around after a sweep, at any file**: in the done phase the
machine steps back one cell and its walk home begins there. It writes
nothing. -/
theorem step_doneBackAny (hR : PR.table.Reads)
    (h : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr WMLe v v') :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.buildDoneP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_moveBack hR h hvi (fun _ _ => rfl)
    (hasLeft_buildExit hrulesS f (PR.passTracksAt cell Slot.mir rest m v'))

end AnyFile

end Home

end Run

end BuildRun

end Data

end Draw

end DescriptiveComplexity
