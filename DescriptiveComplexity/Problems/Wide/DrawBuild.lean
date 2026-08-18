/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSweep
import DescriptiveComplexity.Problems.Wide.DrawBack

/-!
# A program builds its own register file, and guesses its certificate

A space-bounded program gets its register file free: the input channel marks the
cell of each element before the machine starts, and
`DescriptiveComplexity.Draw.Data.back` reads those marks off the layout. A
program on a **clock** cannot use that file – the marks lie in the top half of
the tape and reaching them costs more than the clock allows
(`DescriptiveComplexity.Problems.Wide.Marks`) – so it lays its own out low on the
tape, in its first `n` steps, and runs the same subroutines at it.

This file is the two phases it opens with, in the form the rest of the layer is
written in: one rule family, supplied by the caller, and a run. Both are
`DescriptiveComplexity.Draw.Prog.reachesIn_installOut` – sweep a stretch, install
a background, leave everything outside alone – with the agreement outside
discharged from what the background is made of.

**The phase may vary along the sweep**, because a clocked program's pointer is
split between the control and the phase: the tuple lives
in the control and the block in the phase, so a sweep that crosses a block
boundary changes phase there. The runs take a phase per address, exactly as they
take a control per address, and a sweep that stays in one phase is that at a
constant family.

**What indexes the file is a parameter** (`DescriptiveComplexity.Draw.LaidFile`):
a clocked program's file has one register per block and tuple, not one per
element, and neither phase cares – the building sweep writes the mark of the
register the pointer names, the guessing sweep writes the stage tracks, and both
are stated at the layout the file carries.

## Why they are sweeps and not inductions

The building phase writes something *different* in every cell – the mark of the
element whose register that cell is – and what it reads tells the cells apart in
no way that helps. What tells them apart is the **pointer**: it holds the
element, and the order successor moves it along as the head moves.

## What each phase owes outside its stretch

The building phase installs `back` at the file it is building, and off the file
that background is the blank
(`DescriptiveComplexity.Draw.Data.back_of_not_reg`: the marks are existentials
over the registers, the register digits are set at registers alone, and the five
per-cell tracks are clear in the state the machine starts in). So the caller has
only to say that the background it starts from is blank outside the stretch, and
a clocked program arranges that once and for all by **declining the input
channel's marks**: what a marked cell carries is `Prog.mark`, the program's own
field, so taking it to be the blank leaves the tape blank everywhere at time zero
(`DescriptiveComplexity.Draw.Prog.initBack_of_mark_blank`) and the channel's ruler
is not there to be mistaken for a register.

Guessing is the same sweep with `back` on *both* sides: the stage tracks are what
changes, everything else rides along
(`DescriptiveComplexity.Draw.Data.back_old_congr`), and the assignment is a
**parameter** – which is what makes the statement a guess, since the run exists
for every certificate. It is the only nondeterminism the clocked program has.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' Q : Type}
variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable {PR : Prog A R' P' Q dt.SlotIx dt.KIx dt.dd}
variable {I : Type}

/-! ### Laying the file out -/

/-- **A program lays its register file out.** Sweeping the stretch that holds the
file, with the pointer walking along, the machine turns the background it starts
with into `DescriptiveComplexity.Draw.Data.back` at that file.

Three things make the sweep the file's stretch and no more: every register lies
in it (`hlo`, `hhi`), the state the background is read at has its five per-cell
tracks clear (`hwk` … `hnew`), and outside the stretch the starting background is
already the blank (`hout`). What is left after that is the rule at a cell: read
what is there, write the mark, move right, advance the pointer.

`hout` is what a clocked program buys by declining the input channel's marks
(`DescriptiveComplexity.Draw.Prog.initBack_of_mark_blank`): with `mark` the blank,
the tape at time zero is blank everywhere, so the only cells that are not already
right are the ones this phase is about to write. -/
theorem reachesIn_buildFile (F : LaidFile dt A R' P' I)
    (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {t : dt.SlotIx} {m : I → Prop}
    {bg₀ : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {hdd : dt.dd0 ≤ dt.dd} {st : TapeSt dt A R' P' I}
    (hwk : ∀ r, ¬st.wk r) (hbot : ∀ r, ¬st.bot r) (hltp : ∀ r, ¬st.ltp r)
    (hold : ∀ (i : dt.d.B.ι) r, ¬st.old i r) (hnew : ∀ (i : dt.d.B.ι) r, ¬st.new i r)
    {ph : (Univ A R' P' dt.KIx dt.dd → Prop) → P'} {fc : (Univ A R' P' dt.KIx dt.dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R' P' dt.KIx dt.dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hlo : ∀ u : I, WMSetLe WMLe s₀ (F.cell u))
    (hhi : ∀ u : I, WMSetLt WMLe (F.cell u) s₁)
    (hout : ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → bg₀ r = fun _ => PR.zero)
    (hstep : ∀ s u : Univ A R' P' dt.KIx dt.dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt F.cell t bg₀ m s) (ph u) (fc u)
        (PR.passTracksAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one hdd st) m s)) :
    (wideData (Univ A R' P' dt.KIx dt.dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (ph s₀) (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt F.cell t bg₀ m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ph s₁) (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one hdd st) m)
          (PR.syElt PR.blank)⟩ := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R' P' dt.KIx dt.dd) hlin
  -- off the file the background to install is the blank
  have hoff : ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      (∀ u : I, r ≠ F.cell u) →
      dt.ixBack F.toLayout PR.zero PR.one hdd st r = fun _ => PR.zero :=
    fun r hr => dt.ixBack_of_not_reg hr (hwk r) (hbot r) (hltp r)
      (fun i => hold i r) (fun i => hnew i r)
  -- below the sweep's start, and at or above its end, no cell is a register
  have hbelow : ∀ r : Univ A R' P' dt.KIx dt.dd → Prop, WMSetLt WMLe r s₀ →
      ∀ u : I, r ≠ F.cell u := by
    rintro r hlt u rfl
    exact ((wmSetLt_iff _ _).mp hlt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt).1 (hlo u))
  have habove : ∀ r : Univ A R' P' dt.KIx dt.dd → Prop, ¬WMSetLt WMLe r s₁ →
      ∀ u : I, r ≠ F.cell u := by
    rintro r hnlt u rfl
    exact hnlt (hhi u)
  exact reachesIn_installOut hR hlin hle
    (fun r hc => (hoff r (hbelow r hc)).trans (hout r (Or.inl hc)).symm)
    (fun r hc => (hoff r (habove r hc)).trans (hout r (Or.inr hc)).symm) hstep

/-! ### Guessing the certificate -/

/-- **A program guesses its certificate onto a stretch.** From the background of
a state, the sweep reaches the background of the same state with its stage tracks
replaced by `σ`, provided `σ` agrees with them outside the stretch – the sweep
never goes there. -/
theorem reachesIn_guessTracks (F : LaidFile dt A R' P' I)
    (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {t : dt.SlotIx} {m : I → Prop}
    {hdd : dt.dd0 ≤ dt.dd} {st : TapeSt dt A R' P' I}
    (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {ph : (Univ A R' P' dt.KIx dt.dd → Prop) → P'} {fc : (Univ A R' P' dt.KIx dt.dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R' P' dt.KIx dt.dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hout : ∀ (i : dt.d.B.ι) (r : Univ A R' P' dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → (σ i r ↔ st.old i r))
    (hstep : ∀ s u : Univ A R' P' dt.KIx dt.dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one hdd st) m s) (ph u) (fc u)
        (PR.passTracksAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one hdd { st with old := σ }) m s)) :
    (wideData (Univ A R' P' dt.KIx dt.dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (ph s₀) (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one hdd st) m)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ph s₁) (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one hdd { st with old := σ }) m) (PR.syElt PR.blank)⟩ :=
  reachesIn_installOut hR hlin hle
    (fun r hc => dt.ixBack_old_congr σ fun i => hout i r (Or.inl hc))
    (fun r hc => dt.ixBack_old_congr σ fun i => hout i r (Or.inr hc)) hstep

end Prog

end Draw

end DescriptiveComplexity
