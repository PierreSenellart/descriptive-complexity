/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawPass

/-!
# Scanning to a cell recognized by its tracks

`DescriptiveComplexity.Problems.Wide.DrawPass` navigates to cells marked by a
*single slot* – the two ends of the register file, the working-cell marker.
The atom subroutines of the EXPSPACE program navigate differently: they scan
for the register cell whose **name slots** – the mark a canonically padded
cell carries its own coordinates in – match a tuple the machine holds in its
control. That stopping condition reads several slots at once, so the scans are
restated here with an arbitrary guard on the tracks:

* `DescriptiveComplexity.Draw.Prog.reaches_scanStop` /
  `reaches_scanStopBack` – scan to the first cell whose tracks satisfy the
  guard, learning on arrival that no cell passed did;
* `DescriptiveComplexity.Draw.Prog.reaches_toCell` /
  `reaches_toCellBack` – the same when the caller knows *which* cell that is,
  because the guard identifies it uniquely: arrival at the named cell exactly.

As everywhere in the pass layer, the caller supplies rules (`Prog.HasRight` /
`Prog.HasLeft` families), the symbols are computed for it, and the tape is the
`Prog.trackTapeAt` presentation, so a program never mentions
`FirstOrder.Language.wide`.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {I : Type} {cell : I → (Univ A R P K dd → Prop)}

/-- **Scanning right to the first cell whose tracks satisfy a guard.** The
program supplies one rightward rule per unsatisfying symbol; the machine
arrives at the first satisfying cell at or above its position, and learns on
arrival that nothing it passed satisfied the guard. -/
theorem reachesIn_scanStop (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe s r) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe s r ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLe WMLe s r' → WMSetLt WMLe r' r →
        ¬StopG (PR.passTracksAt cell t rest m r')) ∧
      (wideData (Univ A R P K dd)).ReachesIn (wideRank r - wideRank s)
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_scan_tape (Stop := fun r => StopG (PR.passTracksAt cell t rest m r)) hlin hex
    fun r _ _ hstop => by
      obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
        step_of_hasRight hR (hgo (PR.passTracksAt cell t rest m r) hstop)
      rw [← trackTapeAt_eq] at hread hwrite
      exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Scanning right to the first cell whose tracks satisfy a guard**, the budget
forgotten. -/
theorem reaches_scanStop (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe s r) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe s r ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLe WMLe s r' → WMSetLt WMLe r' r →
        ¬StopG (PR.passTracksAt cell t rest m r')) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, hfirst, hrun⟩ := reachesIn_scanStop hR hlin hgo hex
  exact ⟨r, hr, hge, hfirst, hrun.reflTransGen⟩

/-- **Scanning left to the first cell whose tracks satisfy a guard**, the same
reading downwards. -/
theorem reachesIn_scanStopBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe r s) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe r s ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLt WMLe r r' → WMSetLe WMLe r' s →
        ¬StopG (PR.passTracksAt cell t rest m r')) ∧
      (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank r)
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_scanBack_tape (Stop := fun r => StopG (PR.passTracksAt cell t rest m r)) hlin hex
    fun r _ _ hstop => by
      obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
        step_of_hasLeft hR (hgo (PR.passTracksAt cell t rest m r) hstop)
      rw [← trackTapeAt_eq] at hread hwrite
      exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Scanning right to the first cell whose tracks satisfy a guard**, the budget
forgotten. -/
theorem reaches_scanStopBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe r s) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracksAt cell t rest m r) ∧ WMSetLe WMLe r s ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLt WMLe r r' → WMSetLe WMLe r' s →
        ¬StopG (PR.passTracksAt cell t rest m r')) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, hfirst, hrun⟩ := reachesIn_scanStopBack hR hlin hgo hex
  exact ⟨r, hr, hge, hfirst, hrun.reflTransGen⟩

/-- **Scanning right to a cell the guard identifies uniquely**: when the caller
knows the one cell at or above its position whose tracks satisfy the guard, the
scan arrives exactly there. This is the navigation of the atom subroutines –
the guard compares a cell's name slots with a tuple held in the control, and
the marks make the match unique. -/
theorem reachesIn_toCell (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracksAt cell t rest m u))
    (hle : WMSetLe WMLe s u)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe s r →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank u - wideRank s)
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, -, hreach⟩ := reachesIn_scanStop hR hlin hgo ⟨u, hstop, hle⟩
  rwa [huniq r hge hr] at hreach

/-- **Scanning right to a cell the guard identifies uniquely**, the budget
forgotten. -/
theorem reaches_toCell (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracksAt cell t rest m u))
    (hle : WMSetLe WMLe s u)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe s r →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_toCell hR hlin hgo hstop hle huniq).reflTransGen

/-- **Scanning left to a cell the guard identifies uniquely.** -/
theorem reachesIn_toCellBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracksAt cell t rest m u))
    (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank u)
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hle', -, hreach⟩ := reachesIn_scanStopBack hR hlin hgo ⟨u, hstop, hle⟩
  rwa [huniq r hle' hr] at hreach

/-- **Scanning right to a cell the guard identifies uniquely**, the budget
forgotten. -/
theorem reaches_toCellBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracksAt cell t rest m u))
    (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_toCellBack hR hlin hgo hstop hle huniq).reflTransGen

/-- **Scanning left to a cell the guard identifies uniquely, rules
cell-coupled**: the supplier of the walking rules sees the cell, its position
at or below the start, and the guard's failure there. A verdict phase that
also hosts register rules can only discharge this form – the coupled facts are
what make its guards disjoint from theirs. -/
theorem reachesIn_toCellBackC (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    {s u : Univ A R P K dd → Prop}
    (hgo : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      ¬StopG (PR.passTracksAt cell t rest m r) →
      PR.HasLeft p f (PR.passTracksAt cell t rest m r) p f (PR.passTracksAt cell t rest m r))
    (hstop : StopG (PR.passTracksAt cell t rest m u)) (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s - wideRank u)
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hle', -, hreach⟩ :=
    reachesIn_scanBack_tape (Stop := fun r => StopG (PR.passTracksAt cell t rest m r)) hlin
      ⟨u, hstop, hle⟩ (fun r hub _ hstopr => by
        obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
          step_of_hasLeft hR (hgo r hub hstopr)
        rw [← trackTapeAt_eq] at hread hwrite
        exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩)
  rwa [huniq r hle' hr] at hreach

/-- **Scanning right to a cell the guard identifies uniquely**, the budget
forgotten. -/
theorem reaches_toCellBackC (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : I → Prop}
    {s u : Univ A R P K dd → Prop}
    (hgo : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      ¬StopG (PR.passTracksAt cell t rest m r) →
      PR.HasLeft p f (PR.passTracksAt cell t rest m r) p f (PR.passTracksAt cell t rest m r))
    (hstop : StopG (PR.passTracksAt cell t rest m u)) (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracksAt cell t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_toCellBackC hR hlin hgo hstop hle huniq).reflTransGen

/-! ### Re-presenting the tape between passes

A register pass walks one track and carries the rest of the tape as its
background. Two consecutive passes walk *different* tracks, so the after-tape
of one has to be read as the before-tape of the other: the walked track moves
into the background and a background slot becomes the walked track. That is one
equality of presentations, provable once – the only condition being that the
slot about to be walked satisfies the register discipline, i.e. is the
`DescriptiveComplexity.bitAtOf` of some track (set nowhere off the register
file). -/

end Prog

end Draw

end DescriptiveComplexity
