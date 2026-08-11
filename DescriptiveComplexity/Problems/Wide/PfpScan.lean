/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpPass

/-!
# Scanning to a cell recognized by its tracks

`DescriptiveComplexity.Problems.Wide.PfpPass` navigates to cells marked by a
*single slot* – the two ends of the register file, the working-cell marker.
The atom subroutines of the EXPSPACE program navigate differently: they scan
for the register cell whose **name slots** – the mark a canonically padded
cell carries its own coordinates in – match a tuple the machine holds in its
control. That stopping condition reads several slots at once, so the scans are
restated here with an arbitrary guard on the tracks:

* `DescriptiveComplexity.Pfp.Prog.reaches_scanStop` /
  `reaches_scanStopBack` – scan to the first cell whose tracks satisfy the
  guard, learning on arrival that no cell passed did;
* `DescriptiveComplexity.Pfp.Prog.reaches_toCell` /
  `reaches_toCellBack` – the same when the caller knows *which* cell that is,
  because the guard identifies it uniquely: arrival at the named cell exactly.

As everywhere in the pass layer, the caller supplies rules (`Prog.HasRight` /
`Prog.HasLeft` families), the symbols are computed for it, and the tape is the
`Prog.trackTape` presentation, so a program never mentions
`FirstOrder.Language.wide`.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}

/-- **Scanning right to the first cell whose tracks satisfy a guard.** The
program supplies one rightward rule per unsatisfying symbol; the machine
arrives at the first satisfying cell at or above its position, and learns on
arrival that nothing it passed satisfied the guard. -/
theorem reaches_scanStop (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : Univ A R P K dd → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracks t rest m r) ∧ WMSetLe WMLe s r) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracks t rest m r) ∧ WMSetLe WMLe s r ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLe WMLe s r' → WMSetLt WMLe r' r →
        ¬StopG (PR.passTracks t rest m r')) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ :=
  reaches_scan_tape (Stop := fun r => StopG (PR.passTracks t rest m r)) hlin hex
    fun r _ _ hstop => by
      obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
        step_of_hasRight hR (hgo (PR.passTracks t rest m r) hstop)
      rw [← trackTape_eq] at hread hwrite
      exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Scanning left to the first cell whose tracks satisfy a guard**, the same
reading downwards. -/
theorem reaches_scanStopBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : Univ A R P K dd → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s : Univ A R P K dd → Prop}
    (hex : ∃ r : Univ A R P K dd → Prop,
      StopG (PR.passTracks t rest m r) ∧ WMSetLe WMLe r s) :
    ∃ r : Univ A R P K dd → Prop, StopG (PR.passTracks t rest m r) ∧ WMSetLe WMLe r s ∧
      (∀ r' : Univ A R P K dd → Prop, WMSetLt WMLe r r' → WMSetLe WMLe r' s →
        ¬StopG (PR.passTracks t rest m r')) ∧
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt p f), Sum.inl s,
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt p f), Sum.inl r,
          wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ :=
  reaches_scanBack_tape (Stop := fun r => StopG (PR.passTracks t rest m r)) hlin hex
    fun r _ _ hstop => by
      obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
        step_of_hasLeft hR (hgo (PR.passTracks t rest m r) hstop)
      rw [← trackTape_eq] at hread hwrite
      exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩

/-- **Scanning right to a cell the guard identifies uniquely**: when the caller
knows the one cell at or above its position whose tracks satisfy the guard, the
scan arrives exactly there. This is the navigation of the atom subroutines –
the guard compares a cell's name slots with a tuple held in the control, and
the marks make the match unique. -/
theorem reaches_toCell (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : Univ A R P K dd → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasRight p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracks t rest m u))
    (hle : WMSetLe WMLe s u)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe s r →
      StopG (PR.passTracks t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hge, -, hreach⟩ := reaches_scanStop hR hlin hgo ⟨u, hstop, hle⟩
  rwa [huniq r hge hr] at hreach

/-- **Scanning left to a cell the guard identifies uniquely.** -/
theorem reaches_toCellBack (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : Univ A R P K dd → Prop}
    (hgo : ∀ g : W → A, ¬StopG g → PR.HasLeft p f g p f g)
    {s u : Univ A R P K dd → Prop} (hstop : StopG (PR.passTracks t rest m u))
    (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracks t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hle', -, hreach⟩ := reaches_scanStopBack hR hlin hgo ⟨u, hstop, hle⟩
  rwa [huniq r hle' hr] at hreach

/-- **Scanning left to a cell the guard identifies uniquely, rules
cell-coupled**: the supplier of the walking rules sees the cell, its position
at or below the start, and the guard's failure there. A verdict phase that
also hosts register rules can only discharge this form – the coupled facts are
what make its guards disjoint from theirs. -/
theorem reaches_toCellBackC (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {StopG : (W → A) → Prop}
    {p : P} {f : Q → A} {m : Univ A R P K dd → Prop}
    {s u : Univ A R P K dd → Prop}
    (hgo : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      ¬StopG (PR.passTracks t rest m r) →
      PR.HasLeft p f (PR.passTracks t rest m r) p f (PR.passTracks t rest m r))
    (hstop : StopG (PR.passTracks t rest m u)) (hle : WMSetLe WMLe u s)
    (huniq : ∀ r : Univ A R P K dd → Prop, WMSetLe WMLe r s →
      StopG (PR.passTracks t rest m r) → r = u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl u,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨r, hr, hle', -, hreach⟩ :=
    reaches_scanBack_tape (Stop := fun r => StopG (PR.passTracks t rest m r)) hlin
      ⟨u, hstop, hle⟩ (fun r hub _ hstopr => by
        obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
          step_of_hasLeft hR (hgo r hub hstopr)
        rw [← trackTape_eq] at hread hwrite
        exact ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩)
  rwa [huniq r hle' hr] at hreach

/-! ### Re-presenting the tape between passes

A register pass walks one track and carries the rest of the tape as its
background. Two consecutive passes walk *different* tracks, so the after-tape
of one has to be read as the before-tape of the other: the walked track moves
into the background and a background slot becomes the walked track. That is one
equality of presentations, provable once – the only condition being that the
slot about to be walked satisfies the register discipline, i.e. is the
`DescriptiveComplexity.regBit` of some track (set nowhere off the register
file). -/

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **Handing the walk from one track to another**: the walked track `t` moves
into the background at its own digits, and the background slot `t'` – which
holds the register digits of `m₂` – becomes the walked track. -/
theorem trackTape_swap (PR : Prog A R P Q W K dd) {t t' : W} (hne : t ≠ t')
    {rest : (Univ A R P K dd → Prop) → W → A} {m m₂ : Univ A R P K dd → Prop}
    (ht' : ∀ r : Univ A R P K dd → Prop,
      rest r t' = bitVal PR.zero PR.one (regBit m₂ r)) :
    PR.trackTape t rest m =
      PR.trackTape t'
        (fun r s => if s = t then bitVal PR.zero PR.one (regBit m r) else rest r s) m₂ := by
  refine funext fun r => congrArg _ (congrArg _ (funext fun s => ?_))
  change (if s = t then bitVal PR.zero PR.one (regBit m r) else rest r s) =
    if s = t' then bitVal PR.zero PR.one (regBit m₂ r)
      else if s = t then bitVal PR.zero PR.one (regBit m r) else rest r s
  by_cases hs : s = t'
  · subst hs
    rw [if_pos rfl, if_neg (Ne.symm hne)]
    exact ht' r
  · rw [if_neg hs]

end Prog

end Pfp

end DescriptiveComplexity
