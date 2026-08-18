/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRules
import DescriptiveComplexity.Problems.Wide.Mirror
import DescriptiveComplexity.Problems.Wide.Test

/-!
# A program's rules run its register passes

`DescriptiveComplexity.Problems.Wide.Mirror` and
`DescriptiveComplexity.Problems.Wide.Test` are the three shapes a register pass
comes in – write with an accumulator, write without one, read with one – stated
about an abstract tape and an abstract supply of transitions. This file joins
them to a `DescriptiveComplexity.Draw.Prog`: the tape is
`DescriptiveComplexity.Draw.Prog.trackTapeAt`, the transitions come from the
program's rules, and what is left for the program to supply is a **rule per case**
and nothing else.

## What a program owes

`DescriptiveComplexity.Draw.Prog.HasLeft` is the contract: *in this phase, at this
pointer, reading these tracks, the program has a rule that goes to that phase and
that pointer, writes those tracks, and moves left.* Every hypothesis below is a
family of those, and the symbols are computed for the caller – it never sees
`DescriptiveComplexity.regBit`, never writes a tape equation, and never mentions
`FirstOrder.Language.wide`. (Two wrappers that used to live here – a
whole-track overwrite and a file test with the question asked of the *cell* –
quantified their per-cell data independently of the symbol, which no
deterministic table can serve; their corrected forms are in
`DescriptiveComplexity.Problems.Wide.DrawSub`.)

## The register mark

Each pass needs to tell a register cell from a cell of the working area, because
its rules act at the first and merely walk over the second. One track slot `rg`
carries that (`hrest` below: the slot is set exactly at the cells of the file),
and the guards read it. That is also what separates the acting rules from the
walking one, so it is what `DescriptiveComplexity.Draw.Prog.sep_of` is discharged
from in these phases.

## Which file

Nothing here is about *where* the registers are. The passes that need only the
cells take the family (`DescriptiveComplexity.Draw.Prog.passTracksAt`, and the
lemmas whose `cell` is inferred from the statement); the passes that need a file
to be a file – the two walks up and down to a marked register, and the mirror
increment – take a `DescriptiveComplexity.RegFile` and are named `file…`. The
`wmSeg` statements below them are those at
`DescriptiveComplexity.wmSegFile`, which is the file a space-bounded program gets
free from the input channel; a clocked program builds its own low on the tape and
calls the same lemmas at it.

## One restriction, and where it bites

`DescriptiveComplexity.reaches_mirrorIncr` may stop in a state that depends on the
**carry position**, and the version here does not use that freedom: it stops in a
single state, because a state's payload holds elements of the *source* structure
while the carry position is an element of the emitted universe, and the registers
are anonymous. The carry position is still delivered, as `u₀` with its
characterization, so every use that only has to *move* an address – advancing the
working cell, seeking – is served. The inner loop of the step-formula evaluator,
which folds accumulators against the **block** that rolled over, needs an indexed
variant: the mark of a register cell records which block that register lies in
(finitely many kinds, so finitely many rules), and the stopping rule reads it off
the symbol. That variant is not built here.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable (PR : Prog A R P Q W K dd)

/-! ### The contract -/

/-- **The program has a leftward rule here**: in the phase `p` at the pointer `f`,
reading the tracks `g`, some rule of it goes to the phase `p'` at the pointer `f'`,
writes the tracks `g'` and moves left. -/
def HasLeft (p : P) (f : Q → A) (g : W → A) (p' : P) (f' : Q → A) (g' : W → A) : Prop :=
  ∃ r : R, (PR.rules r).guard f g ∧ (PR.rules r).srcPh = p ∧ (PR.rules r).dstPh = p' ∧
    (PR.rules r).dstSt f g = f' ∧ (PR.rules r).wr f g = g' ∧ ¬(PR.rules r).moveRight

/-- **The program has a rightward rule here.** -/
def HasRight (p : P) (f : Q → A) (g : W → A) (p' : P) (f' : Q → A) (g' : W → A) : Prop :=
  ∃ r : R, (PR.rules r).guard f g ∧ (PR.rules r).srcPh = p ∧ (PR.rules r).dstPh = p' ∧
    (PR.rules r).dstSt f g = f' ∧ (PR.rules r).wr f g = g' ∧ (PR.rules r).moveRight

variable {PR}

omit [DecidableEq W] in
/-- A leftward rule is a transition with its six attributes. -/
theorem step_of_hasLeft (hR : PR.table.Reads) {p p' : P} {f f' : Q → A} {g g' : W → A}
    (h : PR.HasLeft p f g p' f' g') :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ (PR.stElt p f) ∧ WMRead τ (PR.syElt g) ∧
      WMDst τ (PR.stElt p' f') ∧ WMWrite τ (PR.syElt g') ∧ ¬WMRight τ := by
  obtain ⟨r, hg, hsp, hdp, hds, hw, hd⟩ := h
  have hfire := PR.fire_left hR r f g hg hd
  rw [hsp, hdp, hds, hw] at hfire
  exact hfire

omit [DecidableEq W] in
/-- A rightward rule is a transition with its six attributes. -/
theorem step_of_hasRight (hR : PR.table.Reads) {p p' : P} {f f' : Q → A} {g g' : W → A}
    (h : PR.HasRight p f g p' f' g') :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ (PR.stElt p f) ∧ WMRead τ (PR.syElt g) ∧
      WMDst τ (PR.stElt p' f') ∧ WMWrite τ (PR.syElt g') ∧ WMRight τ := by
  obtain ⟨r, hg, hsp, hdp, hds, hw, hd⟩ := h
  have hfire := PR.fire_right hR r f g hg hd
  rw [hsp, hdp, hds, hw] at hfire
  exact hfire

/-! ### The tracks a pass reads -/

variable [Finite A] [Finite R] [Finite P] [Finite K]

section Reading

variable (PR)
variable {I : Type} {ile : I → I → Prop} (cell : I → (Univ A R P K dd → Prop))
variable (t rg : W) (rest : (Univ A R P K dd → Prop) → W → A)

/-- **The tracks the tape carries at a cell**: the walked track's digit in the
slot `t`, the program's own bits elsewhere. Everything a rule of a register pass
reads is this, at a register cell or at a cell of the working area.

The register file enters as its *cells* and not as a
`DescriptiveComplexity.RegFile`, for the reason
`DescriptiveComplexity.Draw.Prog.trackTapeAt` does: this is a definition, and a
file carries proofs. What indexes those cells is a parameter, as it is
throughout the address layer: a program on a clock cannot give every element of
the universe a register, and the tracks do not care which does. -/
noncomputable def passTracksAt
    (m : I → Prop) (r : Univ A R P K dd → Prop) : W → A :=
  fun s => if s = t then bitVal PR.zero PR.one (bitAtOf cell m r) else rest r s

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
theorem trackTapeAt_eq (m : I → Prop) (r : Univ A R P K dd → Prop) :
    PR.trackTapeAt cell t rest m r = PR.syElt (PR.passTracksAt cell t rest m r) := rfl

variable {PR cell t rg rest}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- At a register cell the walked slot holds the track's digit there. -/
theorem passTracks_cell (F : IxFile (Univ A R P K dd) I ile)
    (hix : IsLinOrd ile)
    (m : I → Prop) (u : I) :
    PR.passTracksAt F.cell t rest m (F.cell u) =
      fun s => if s = t then bitVal PR.zero PR.one (m u) else rest (F.cell u) s := by
  refine funext fun s => ?_
  by_cases hs : s = t
  · simp only [passTracksAt, if_pos hs]
    exact bitVal_congr (F.bitAt_cell hix m u)
  · simp only [passTracksAt, if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The walked slot at a register cell**: the track's digit there, which is what
the acting rules of a pass are guarded by. -/
theorem passTracks_cell_apply (F : IxFile (Univ A R P K dd) I ile)
    (hix : IsLinOrd ile)
    (m : I → Prop) (u : I) :
    PR.passTracksAt F.cell t rest m (F.cell u) t = bitVal PR.zero PR.one (m u) := by
  simp only [passTracksAt]
  exact bitVal_congr (F.bitAt_cell hix m u)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- The same at the file the input channel marks. -/
theorem passTracks_wmSeg (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (m : Univ A R P K dd → Prop) (u : Univ A R P K dd) :
    PR.passTracksAt wmSeg t rest m (wmSeg u) =
      fun s => if s = t then bitVal PR.zero PR.one (m u) else rest (wmSeg u) s :=
  passTracks_cell (wmSegFile hlin).toIx hlin m u

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **The walked slot at a marked cell**: the track's digit there. -/
theorem passTracks_wmSeg_apply (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (m : Univ A R P K dd → Prop) (u : Univ A R P K dd) :
    PR.passTracksAt wmSeg t rest m (wmSeg u) t = bitVal PR.zero PR.one (m u) :=
  passTracks_cell_apply (wmSegFile hlin).toIx hlin m u

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- Away from the register file the walked slot is clear. -/
theorem passTracks_of_not_reg (m : I → Prop) {r : Univ A R P K dd → Prop}
    (hno : ∀ u : I, r ≠ cell u) :
    PR.passTracksAt cell t rest m r =
      fun s => if s = t then PR.zero else rest r s := by
  refine funext fun s => ?_
  by_cases hs : s = t
  · simp only [passTracksAt, if_pos hs]
    exact bitVal_neg (bitAtOf_of_not_reg hno)
  · simp only [passTracksAt, if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- **A slot other than the walked one** shows what the program keeps there. Every
guard of a register pass that is not about the track itself reads through this. -/
theorem passTracks_of_ne {sl : W} (hne : sl ≠ t) (m : I → Prop) (r : Univ A R P K dd → Prop) :
    PR.passTracksAt cell t rest m r sl = rest r sl := by
  simp only [passTracksAt, if_neg hne]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- **The tracks at a cell read the background there and nowhere else.** Two
backgrounds agreeing at one address present the same tracks there, whatever they
do elsewhere – which is what lets a sweep describe its progress by a frontier
rather than by an induction. -/
theorem passTracks_congr {bgA bgB : (Univ A R P K dd → Prop) → W → A}
    {r : Univ A R P K dd → Prop} (hbg : bgA r = bgB r) (m : I → Prop) :
    PR.passTracksAt cell t bgA m r = PR.passTracksAt cell t bgB m r := by
  refine funext fun sl => ?_
  simp only [passTracksAt, hbg]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- **The register mark, read**: the slot `rg` is set exactly at the cells of the
file, which is what tells the acting rules of a pass from its walking one. -/
theorem passTracks_rg (hne : t ≠ rg)
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = cell u))
    (m : I → Prop) (r : Univ A R P K dd → Prop) :
    PR.passTracksAt cell t rest m r rg =
      bitVal PR.zero PR.one (∃ u : I, r = cell u) := by
  rw [passTracks_of_ne (Ne.symm hne)]
  exact hrest r

end Reading

/-! ### One step in the working area

A register pass leaves the program's other bits alone; the work between passes is
the other way round – the track is untouched and the **background** changes, at
the one cell the head is on. That is one step, and it is the only place a
program's own data is written. -/

variable {I : Type} {ile : I → I → Prop} {cell : I → (Univ A R P K dd → Prop)}

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Language.wide.Structure (Univ A R P K dd)] in
/-- **Backgrounds agreeing off a cell present tapes agreeing off it.** -/
theorem trackTape_frame {t : W} {rest rest' : (Univ A R P K dd → Prop) → W → A}
    {m : I → Prop} {v : Univ A R P K dd → Prop}
    (hframe : ∀ r, r ≠ v → rest' r = rest r) :
    ∀ r, r ≠ v →
      PR.trackTapeAt cell t rest' m r = PR.trackTapeAt cell t rest m r := fun r hr => by
  simp only [trackTapeAt, hframe r hr]

/-- **One step of the program to the right**, writing its own data at the cell it
leaves. The track is carried along untouched, so a step and a register pass compose
without either having to know what the other keeps on the tape. -/
theorem step_move (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {v v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v v')
    {t : W} {rest rest' : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    (hframe : ∀ r, r ≠ v → rest' r = rest r) {p p' : P} {f f' : Q → A}
    (hrule : PR.HasRight p f (PR.passTracksAt cell t rest m v) p' f' (PR.passTracksAt cell t
      rest' m v)) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl v,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTapeAt cell t rest' m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasRight hR hrule
  rw [← trackTapeAt_eq] at hread hwrite
  exact step_wideTape_right hlin hi htr hsrc hread hdst hwrite hright (PR.trackTape_frame hframe)

/-- **One step of the program to the left.** -/
theorem step_moveBack (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {v v' : Univ A R P K dd → Prop} (hi : WMIncr WMLe v' v)
    {t : W} {rest rest' : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    (hframe : ∀ r, r ≠ v → rest' r = rest r) {p p' : P} {f f' : Q → A}
    (hrule : PR.HasLeft p f (PR.passTracksAt cell t rest m v) p' f' (PR.passTracksAt cell t
      rest' m v)) :
    (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl v,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f'), Sum.inl v',
        wideTape (PR.trackTapeAt cell t rest' m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := step_of_hasLeft hR hrule
  rw [← trackTapeAt_eq] at hread hwrite
  exact step_wideTape_left hlin hi htr hsrc hread hdst hwrite hright (PR.trackTape_frame hframe)

/-! ### Getting to a marked register

The two ends of the file have to be recognized on sight – the last one to begin a
downward pass, the first one to come back from one – and that is all that has to
be. One slot marks the target cell, one rule family walks over everything else,
and the same theorem serves both ends by taking the target as a parameter. -/

/-- **Walking up to a marked register.** From any cell at or below the register of
`u`, the machine scans right to it, stopped by the slot `sl` that marks that cell
and no other. The cost is the stretch of addresses it crosses. -/
theorem reachesIn_fileToMark (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {u : I}
    (hsl : ∀ r : Univ A R P K dd → Prop, rest r sl = bitVal PR.zero PR.one (r = F.cell u))
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl = PR.zero → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s (F.cell u)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank (F.cell u) - wideRank s)
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ := by
  have hclear : ∀ r : Univ A R P K dd → Prop, r ≠ F.cell u →
      PR.passTracksAt F.cell t rest m r sl = PR.zero := fun r hr => by
    rw [passTracks_of_ne hne, hsl r]
    exact bitVal_neg hr
  refine F.reachesIn_toReg hlin hle (fun x hx => ?_) (fun r _ hno => ?_)
  · rw [trackTapeAt_eq]
    exact step_of_hasRight hR (hgo _ (hclear _ fun hc => hx (F.injective hix hc)))
  · rw [trackTapeAt_eq]
    exact step_of_hasRight hR (hgo _ (hclear _ (hno u)))

/-- **Walking up to a marked register**, the budget forgotten. -/
theorem reaches_fileToMark (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {u : I}
    (hsl : ∀ r : Univ A R P K dd → Prop, rest r sl = bitVal PR.zero PR.one (r = F.cell u))
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl = PR.zero → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s (F.cell u)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_fileToMark F hR hlin hix hne hsl hgo hle).reflTransGen
/-- **Walking back down to a marked register**, the same reading downwards. -/
theorem reachesIn_fileToMarkBack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {u : I}
    (hsl : ∀ r : Univ A R P K dd → Prop, rest r sl = bitVal PR.zero PR.one (r = F.cell u))
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl = PR.zero → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe (F.cell u) s) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank (F.cell u))
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ := by
  have hclear : ∀ r : Univ A R P K dd → Prop, r ≠ F.cell u →
      PR.passTracksAt F.cell t rest m r sl = PR.zero := fun r hr => by
    rw [passTracks_of_ne hne, hsl r]
    exact bitVal_neg hr
  refine F.reachesIn_toRegBack hlin hle (fun x hx => ?_) (fun r _ hno => ?_)
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hgo _ (hclear _ fun hc => hx (F.injective hix hc)))
  · rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hgo _ (hclear _ (hno u)))

/-- **Walking back down to a marked register**, the budget forgotten. -/
theorem reaches_fileToMarkBack (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {u : I}
    (hsl : ∀ r : Univ A R P K dd → Prop, rest r sl = bitVal PR.zero PR.one (r = F.cell u))
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl = PR.zero → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop} (hle : WMSetLe WMLe (F.cell u) s) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl (F.cell u),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_fileToMarkBack F hR hlin hix hne hsl hgo hle).reflTransGen
/-! ### Seeking a marked cell

The other navigation a program does, and the one it does in the working area: walk
until the cell whose slot `sl` is set. Unlike the register ends, the program does
not know *which* cell that will be – it wrote the mark itself, exponentially many
rounds ago – so the arrival comes with the promise that nothing passed was marked,
which is where the extremum is taken. -/

/-- **Seeking right to the nearest marked cell.** -/
theorem reachesIn_seek (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl ≠ PR.one → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe s r) :
    ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe s r ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLe WMLe s r' → WMSetLt WMLe r' r →
        rest r' sl ≠ PR.one) ∧
      (wideData (Univ A R P K dd)).ReachesIn (wideRank r - wideRank s)
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_scan_tape (Stop := fun r => rest r sl = PR.one) hlin hex fun r _ _ hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      step_of_hasRight hR (hgo (PR.passTracksAt cell t rest m r)
        (by rw [passTracks_of_ne hne]; exact hstop))
    rw [← trackTapeAt_eq] at hread hwrite
    exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Seeking right to the nearest marked cell**, the budget forgotten. -/
theorem reaches_seek (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl ≠ PR.one → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe s r) :
    ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe s r ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLe WMLe s r' → WMSetLt WMLe r' r →
        rest r' sl ≠ PR.one) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, hfirst, hrun⟩ := reachesIn_seek hR hlin hne hgo hex
  exact ⟨r, hr, hge, hfirst, hrun.reflTransGen⟩
/-- **Seeking left to the nearest marked cell.** -/
theorem reachesIn_seekBack (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl ≠ PR.one → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe r s) :
    ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe r s ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLt WMLe r r' → WMSetLe WMLe r' s →
        rest r' sl ≠ PR.one) ∧
      (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank r)
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_scanBack_tape (Stop := fun r => rest r sl = PR.one) hlin hex fun r _ _ hstop => by
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      step_of_hasLeft hR (hgo (PR.passTracksAt cell t rest m r)
        (by rw [passTracks_of_ne hne]; exact hstop))
    rw [← trackTapeAt_eq] at hread hwrite
    exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Seeking left to the nearest marked cell**, the budget forgotten. -/
theorem reaches_seekBack (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t sl : W} (hne : sl ≠ t) {rest : (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, g sl ≠ PR.one → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe r s) :
    ∃ r : Univ A R P K dd → Prop, rest r sl = PR.one ∧ WMSetLe WMLe r s ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLt WMLe r r' → WMSetLe WMLe r' s →
        rest r' sl ≠ PR.one) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, hfirst, hrun⟩ := reachesIn_seekBack hR hlin hne hgo hex
  exact ⟨r, hr, hge, hfirst, hrun.reflTransGen⟩
/-! ### The mirror increment

The stopped phase may depend on the register the increment carried at – on the
**block** that rolled over, which is what the fold of
`DescriptiveComplexity.Problems.Wide.Fold` has to know. The machine cannot name
that register: a state's payload holds elements of the source structure, and the
registers are anonymous. What it can do is read the block off the *mark*, since a
reduction chooses what each register cell starts holding and there are finitely
many blocks; so the stopping rule comes in one copy per block, and the phase it
goes to is the copy's. -/

/-- **A program increments its mirror, and lands in the phase of the block that
carried.** From the last register in the carrying phase with the track at `m`, the
machine walks down the file and arrives just below the first register with the
track at the increment of `m`, in the phase `pd b` for the block `b` of the carry
position.

The four families of rules are the whole of what the program supplies, and each is
a statement about the tracks a symbol carries, not about the tape. -/
theorem reachesIn_fileIncrBlk [Finite I] (F : IxFile (Univ A R P K dd) I ile)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {m m' : I → Prop} (hi : WMIncr ile m m')
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {B : Type} {bs : B → W} (hbs : ∀ b, bs b ≠ t) {blkOf : I → B}
    (hblk : ∀ (u : I) (b : B),
      rest (F.cell u) (bs b) = bitVal PR.zero PR.one (blkOf u = b))
    {pc : P} {pd : B → P} {fc : Q → A}
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pc fc g pc fc (Function.update g t PR.zero))
    (hset : ∀ (b : B) (g : W → A), g t = PR.zero → g rg = PR.one → g (bs b) = PR.one →
      (∀ b' : B, g (bs b') = PR.one → b' = b) →
      PR.HasLeft pc fc g (pd b) fc (Function.update g t PR.one))
    (hhold : ∀ (b : B) (g : W → A), g rg = PR.one → PR.HasLeft (pd b) fc g (pd b) fc g)
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pc fc (PR.passTracksAt F.cell t rest k r) pc fc
        (PR.passTracksAt F.cell t rest k r))
    (hwalkD : ∀ (b : B) (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft (pd b) fc (PR.passTracksAt F.cell t rest k r) (pd b) fc (PR.passTracksAt F.cell t
        rest k r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ (u₀ : I) (p : Univ A R P K dd → Prop),
      (¬m u₀ ∧ ∀ v, WMLt ile u₀ v → m v) ∧ WMIncr WMLe p (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt pc fc), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (pd (blkOf u₀)) fc), Sum.inl p,
          wideTape (PR.trackTapeAt F.cell t rest m') (PR.syElt PR.blank)⟩ := by
  -- The mark of a register cell is set, and of no other cell.
  have hrgSeg : ∀ (k : I → Prop) (u : I),
      PR.passTracksAt F.cell t rest k (F.cell u) rg = PR.one := fun k u => by
    rw [passTracks_rg hne hrest]
    exact bitVal_pos ⟨u, rfl⟩
  have hrgOff : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∀ x : I, r ≠ F.cell x) → PR.passTracksAt F.cell t rest k r rg = PR.zero :=
    fun k r hno => by
      rw [passTracks_rg hne hrest]
      exact bitVal_neg fun hc => hc.elim fun x hx => hno x hx
  -- The block slot of a register cell names that register's block.
  have hbsSeg : ∀ (k : I → Prop) (u : I),
      PR.passTracksAt F.cell t rest k (F.cell u) (bs (blkOf u)) = PR.one := fun k u => by
    rw [passTracks_of_ne (hbs _), hblk u (blkOf u)]
    exact bitVal_pos rfl
  refine F.reachesIn_mirrorIncr hix hlin hi (b := PR.syElt PR.blank) (w := w) hgap
    (tapeOf := PR.trackTapeAt F.cell t rest) (qc := PR.stElt pc fc)
    (qd := fun u => PR.stElt (pd (blkOf u)) fc)
    (PR.trackTapeAt_coh F.cell t rest) (fun k u hk => ?_) (fun k u hk => ?_) (fun u k w => ?_)
    (fun q hq k r hbnd hno => ?_) htop hbot
  · -- a set digit: clear it and carry on
    have hwrite : PR.passTracksAt F.cell t rest (fun v => k v ∧ v ≠ u) (F.cell u) =
        Function.update (PR.passTracksAt F.cell t rest k (F.cell u)) t PR.zero := by
      rw [passTracks_cell F hix, passTracks_cell F hix]
      refine funext fun s => ?_
      by_cases hs : s = t
      · subst hs
        rw [Function.update_self, if_pos rfl]
        exact bitVal_neg fun hc => hc.2 rfl
      · rw [Function.update_of_ne hs, if_neg hs, if_neg hs]
    rw [trackTapeAt_eq, trackTapeAt_eq, hwrite]
    refine step_of_hasLeft hR (hclear _ ?_ (hrgSeg k u))
    rw [passTracks_cell_apply F hix]
    exact bitVal_pos hk
  · -- a clear digit: set it, and stop in the phase of this register's block
    have hwrite : PR.passTracksAt F.cell t rest (fun v => k v ∨ v = u) (F.cell u) =
        Function.update (PR.passTracksAt F.cell t rest k (F.cell u)) t PR.one := by
      rw [passTracks_cell F hix, passTracks_cell F hix]
      refine funext fun s => ?_
      by_cases hs : s = t
      · subst hs
        rw [Function.update_self, if_pos rfl]
        exact bitVal_pos (Or.inr rfl)
      · rw [Function.update_of_ne hs, if_neg hs, if_neg hs]
    rw [trackTapeAt_eq, trackTapeAt_eq, hwrite]
    refine step_of_hasLeft hR
      (hset (blkOf u) _ ?_ (hrgSeg k u) (hbsSeg k u) fun b' hb' => ?_)
    · rw [passTracks_cell_apply F hix]
      exact bitVal_neg hk
    · rw [passTracks_of_ne (hbs b'), hblk u b'] at hb'
      by_contra hne'
      rw [bitVal_neg fun hc => hne' hc.symm] at hb'
      exact PR.zero_ne_one hb'
  · -- already stopped: rewrite the register's symbol and walk on
    rw [trackTapeAt_eq]
    exact step_of_hasLeft hR (hhold (blkOf u) _ (hrgSeg k w))
  · -- an unmarked cell of the file: walk over it, in whichever phase
    rw [trackTapeAt_eq]
    rcases hq with rfl | ⟨u, rfl⟩
    · exact step_of_hasLeft hR (hwalk k r hbnd hno)
    · exact step_of_hasLeft hR (hwalkD (blkOf u) k r hbnd hno)

/-- **A program increments its mirror**, stopping in one phase whatever carried:
`DescriptiveComplexity.Draw.Prog.reachesIn_fileIncrBlk` with a single block, the register
mark serving as its indicator. This is the form every use that only has to *move*
an address takes – advancing the working cell, seeking. -/
theorem reachesIn_fileIncr [Finite I] (F : IxFile (Univ A R P K dd) I ile)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {m m' : I → Prop} (hi : WMIncr ile m m')
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {pc pd : P} {fc : Q → A}
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pc fc g pc fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft pc fc g pd fc (Function.update g t PR.one))
    (hhold : ∀ g : W → A, g rg = PR.one → PR.HasLeft pd fc g pd fc g)
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pc fc (PR.passTracksAt F.cell t rest k r) pc fc
        (PR.passTracksAt F.cell t rest k r))
    (hwalkD : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pd fc (PR.passTracksAt F.cell t rest k r) pd fc
        (PR.passTracksAt F.cell t rest k r))
    {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ (u₀ : I) (p : Univ A R P K dd → Prop),
      (¬m u₀ ∧ ∀ v, WMLt ile u₀ v → m v) ∧ WMIncr WMLe p (F.cell bot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr (PR.stElt pc fc), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pd fc), Sum.inl p,
          wideTape (PR.trackTapeAt F.cell t rest m') (PR.syElt PR.blank)⟩ :=
  reachesIn_fileIncrBlk F hR hlin hix hi hne hrest (B := Unit) (bs := fun _ => rg)
    (fun _ => Ne.symm hne)
    (blkOf := fun _ => ())
    (fun u b => by
      cases b
      exact (hrest _).trans (bitVal_congr (iff_of_true ⟨u, rfl⟩ rfl)))
    (pd := fun _ => pd) hclear (fun _ g h1 h2 _ _ => hset g h1 h2) (fun _ g h => hhold g h)
    hwalk (fun _ => hwalkD) hgap htop hbot

/-- **A program increments its mirror**, landing in the phase of the block that
carried, the budget forgotten. -/
theorem reaches_fileIncrBlk [Finite I] (F : IxFile (Univ A R P K dd) I ile)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {m m' : I → Prop} (hi : WMIncr ile m m')
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {B : Type} {bs : B → W} (hbs : ∀ b, bs b ≠ t) {blkOf : I → B}
    (hblk : ∀ (u : I) (b : B),
      rest (F.cell u) (bs b) = bitVal PR.zero PR.one (blkOf u = b))
    {pc : P} {pd : B → P} {fc : Q → A}
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pc fc g pc fc (Function.update g t PR.zero))
    (hset : ∀ (b : B) (g : W → A), g t = PR.zero → g rg = PR.one → g (bs b) = PR.one →
      (∀ b' : B, g (bs b') = PR.one → b' = b) →
      PR.HasLeft pc fc g (pd b) fc (Function.update g t PR.one))
    (hhold : ∀ (b : B) (g : W → A), g rg = PR.one → PR.HasLeft (pd b) fc g (pd b) fc g)
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pc fc (PR.passTracksAt F.cell t rest k r) pc fc
        (PR.passTracksAt F.cell t rest k r))
    (hwalkD : ∀ (b : B) (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft (pd b) fc (PR.passTracksAt F.cell t rest k r) (pd b) fc (PR.passTracksAt F.cell t
        rest k r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ (u₀ : I) (p : Univ A R P K dd → Prop),
      (¬m u₀ ∧ ∀ v, WMLt ile u₀ v → m v) ∧ WMIncr WMLe p (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pc fc), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (pd (blkOf u₀)) fc), Sum.inl p,
          wideTape (PR.trackTapeAt F.cell t rest m') (PR.syElt PR.blank)⟩ := by
  obtain ⟨u₀, p, hu₀, hp, hrun⟩ := reachesIn_fileIncrBlk F hR hlin hix hi hne hrest hbs hblk
    hclear hset hhold hwalk hwalkD
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _))) htop hbot
  exact ⟨u₀, p, hu₀, hp, hrun.reflTransGen⟩
/-- **A program increments its mirror**, stopping in one phase whatever carried,
the budget forgotten. -/
theorem reaches_fileIncr [Finite I] (F : IxFile (Univ A R P K dd) I ile)
    (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (hix : IsLinOrd ile)
    {m m' : I → Prop} (hi : WMIncr ile m m')
    {t rg : W} (hne : t ≠ rg) {rest : (Univ A R P K dd → Prop) → W → A}
    (hrest : ∀ r : Univ A R P K dd → Prop,
      rest r rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))
    {pc pd : P} {fc : Q → A}
    (hclear : ∀ g : W → A, g t = PR.one → g rg = PR.one →
      PR.HasLeft pc fc g pc fc (Function.update g t PR.zero))
    (hset : ∀ g : W → A, g t = PR.zero → g rg = PR.one →
      PR.HasLeft pc fc g pd fc (Function.update g t PR.one))
    (hhold : ∀ g : W → A, g rg = PR.one → PR.HasLeft pd fc g pd fc g)
    (hwalk : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pc fc (PR.passTracksAt F.cell t rest k r) pc fc
        (PR.passTracksAt F.cell t rest k r))
    (hwalkD : ∀ (k : I → Prop) (r : Univ A R P K dd → Prop),
      (∃ x : I, WMSetLe WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      PR.HasLeft pd fc (PR.passTracksAt F.cell t rest k r) pd fc
        (PR.passTracksAt F.cell t rest k r))
    {top bot : I} (htop : ∀ v, ile v top) (hbot : ∀ v, ile bot v) :
    ∃ (u₀ : I) (p : Univ A R P K dd → Prop),
      (¬m u₀ ∧ ∀ v, WMLt ile u₀ v → m v) ∧ WMIncr WMLe p (F.cell bot) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt pc fc), Sum.inl (F.cell top),
          wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt pd fc), Sum.inl p,
          wideTape (PR.trackTapeAt F.cell t rest m') (PR.syElt PR.blank)⟩ :=
  reaches_fileIncrBlk F hR hlin hix hi hne hrest (B := Unit) (bs := fun _ => rg)
    (fun _ => Ne.symm hne)
    (blkOf := fun _ => ())
    (fun u b => by
      cases b
      exact (hrest _).trans (bitVal_congr (iff_of_true ⟨u, rfl⟩ rfl)))
    (pd := fun _ => pd) hclear (fun _ g h1 h2 _ _ => hset g h1 h2) (fun _ g h => hhold g h)
    hwalk (fun _ => hwalkD) htop hbot

end Prog

end Draw

end DescriptiveComplexity
