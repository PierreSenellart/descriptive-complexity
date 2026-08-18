/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexOuter
import DescriptiveComplexity.Problems.Wide.NexSpec
import DescriptiveComplexity.Problems.Wide.DrawBuild

/-!
# Guessing the certificate onto the region

The certificate is one bit per **address** of the region, not per register of
the file: the evaluation reads its dictionary at the address whose argument
blocks encode a tuple of points, and there are `2 ^ (k · nᵈ)` of those, where the
file has one register per block and tuple and is polynomial. So the guessing
sweep is not the file-laying sweep with a different write; it is a walk over the
region.

That has one consequence for its rules, and it is what this file is: the walk
**cannot be pointer-driven**. A pointer holds a block and a tuple and can count
the file's registers; it cannot count the region. So the guess is a sweep in the
space-bounded program's style – one phase for the whole walk, a nondeterministic
write, a step right – and its exit is a rule available at *every* address, so
that where the guess stops is one more nondeterministic choice. Nothing has to
recognize the region's end: the run a yes-instance exhibits stops at the logical
top, and a run that stops earlier has left its remaining bits clear, which is a
certificate like any other.

The rules are the program's own at
`DescriptiveComplexity.Draw.DrawData.regionSpec` – a guess specification whose
pointer never moves, so that the site's *roll-over* arm is the walk's every step
– together with the stopping rule `hasLeft_guessStop`. The sweep is
`reachesIn_guessRegion`, at the stretch's own length, and the whole phase –
sweep, stop, walk home – is `reachesIn_guessRegionPhase`.
-/

namespace DescriptiveComplexity

namespace Draw

namespace DrawData

open FirstOrder

open Language Structure

section Run

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' I PE : Type}
variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]
variable [LinearOrder A] [LinearOrder R']
variable [LinearOrder (NexPh (Option dt.KIx) PE)]
variable [Language.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] [Finite dt.KIx]
variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable {F : LaidFile dt A R' (NexPh (Option dt.KIx) PE) I} {m : I → Prop}
variable {SE : Type} {ShE : SE → Type} {f₀ : dt.CtlIx → A}
variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}
variable {evalEntry : PE} {bot : Option dt.KIx}
variable {β : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}
variable {rEmb : ∀ i : NexSite SE,
  NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
variable (hrules : ∀ (i : NexSite SE)
    (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
  PR.rules (rEmb i ρ) = dt.nexRule PR.one β (dt.regionSpec PR.zero PR.one) ruleE
    evalEntry bot i ρ)

omit [Finite A] [Finite R'] [Finite (NexPh (Option dt.KIx) PE)] [Finite dt.KIx] in
include hrules in
/-- **The write step of the region-wide guess**, at an address of the stretch:
the rule whose bit vector is the certificate's there fires. It is the guess
site's *roll-over* arm – at `regionSpec` the pointer never moves, so that arm's
guard is always true and its destination is the phase it came from. -/
theorem hasRight_guessRegion
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    (σ : dt.d.B.ι → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    {t : dt.SlotIx} (hne : ∀ i : dt.d.B.ι, (Slot.old i : dt.SlotIx) ≠ t)
    (b : Option dt.KIx)
    (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    PR.HasRight (NexPh.guessP b) f₀
      (PR.passTracksAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
        m r) (NexPh.guessP b) f₀
      (PR.passTracksAt F.cell t
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m r) := by
  classical
  have h := hasRight_guessRoll (dt := dt) (β := β)
    (γ := dt.regionSpec PR.zero PR.one) (ruleE := ruleE) (evalEntry := evalEntry)
    (bot := bot) hrules b (fun i => decide (σ i r)) f₀
    (PR.passTracksAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m r)
    trivial not_false
  rwa [show (dt.regionSpec PR.zero PR.one).wr b (fun i => decide (σ i r)) f₀
      (PR.passTracksAt F.cell t
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m r) =
      PR.passTracksAt F.cell t
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m r from
    dt.guessWr_eq_passTracks σ hne _ (fun i => by simp)] at h

include hrules in
/-- **The clocked program guesses its certificate onto the region**: one
nondeterministic write per address of the stretch, at the stretch's own length.
The walk carries no pointer – every step is the same rule at the same phase – so
it is as long as the region asks and no wider than a bit vector. -/
theorem reachesIn_guessRegion (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    (σ : dt.d.B.ι → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    {t : dt.SlotIx} (hne : ∀ i : dt.d.B.ι, (Slot.old i : dt.SlotIx) ≠ t)
    (b : Option dt.KIx)
    {s₀ s₁ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe s₀ s₁)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → (σ i r ↔ st.old i r)) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (NexPh.guessP b) f₀), Sum.inl s₀,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.guessP b) f₀), Sum.inl s₁,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m)
          (PR.syElt PR.blank)⟩ :=
  Prog.reachesIn_guessTracks F hR hlin σ (ph := fun _ => NexPh.guessP b)
    (fc := fun _ => f₀) hle hout
    (fun s _ _ _ _ => hasRight_guessRegion hrules σ hne b s)

include hrules in
/-- **The whole guessing phase of a clocked program**: the sweep over the region,
the stop – which may fall anywhere, and here falls at the stretch's top – and the
walk home to the marker. Its cost is the stretch out and back with the one step
that turns round. -/
theorem reachesIn_guessRegionPhase (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    (σ : dt.d.B.ι → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    {t : dt.SlotIx} (hne : ∀ i : dt.d.B.ι, (Slot.old i : dt.SlotIx) ≠ t)
    (hnewk : (Slot.wk : dt.SlotIx) ≠ t) (b : Option dt.KIx)
    {v s₀ s₁ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    (hle : WMSetLe WMLe s₀ s₁) (hv : WMSetLt WMLe v s₀)
    (hne₁ : ∃ x, s₁ x)
    {rHome : HomeKit.HomeRule → R'}
    (hrulesH : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHome ρ) =
        (HomeKit.mk t Slot.wk (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE))).rule
          PR.one ρ)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt WMLe r s₀ ∨ ¬WMSetLt WMLe r s₁ → (σ i r ↔ st.old i r)) :
    (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      ((wideRank s₁ - wideRank s₀) + (wideRank s₁ - wideRank v) + 1)
      ⟨Sum.inr (PR.stElt (NexPh.guessP b) f₀), Sum.inl s₀,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hlinSet := isLinOrd_wmSetLe
    (α := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd) hlin
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin hne₁
  have hvs₁ : WMSetLt WMLe v s₁ :=
    (wmSetLt_iff _ _).mpr ⟨hlinSet.2.1 _ _ _ ((wmSetLt_iff _ _).mp hv).1 hle,
      fun hc => ((wmSetLt_iff _ _).mp hv).2
        (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hv).1 (hc ▸ hle))⟩
  have hvpt : WMSetLe WMLe v pt := (wmSetLt_iff_of_wmIncr hlin hpt v).mp hvs₁
  have hsweep := reachesIn_guessRegion (F := F) (m := m) (f₀ := f₀) hrules hR
    hlin σ hne b hle hout
  have hstop : (wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.guessP b) f₀), Sum.inl s₁,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f₀), Sum.inl pt,
        wideTape (PR.trackTapeAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ }) m)
          (PR.syElt PR.blank)⟩ :=
    Prog.step_moveBack hR hlin hpt (fun _ _ => rfl)
      (hasLeft_guessStop (dt := dt) hrules b f₀ _)
  have hhome := HomeKit.reachesIn
    (κ := HomeKit.mk t Slot.wk (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE)))
    (rEmb := rHome) F.toIxFile hrulesH hR hlin hnewk
    (m := m) (fc := f₀)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
    (fun r => by
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with old := σ } r Slot.wk = _
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ } r
        Slot.wk = bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hvpt
  refine TMData.ReachesIn.mono ?_ ((hsweep.tail hstop).trans hhome)
  have h₁ : wideRank pt ≤ wideRank s₁ := wideRank_mono hlin (wmSetLe_of_wmIncr hpt)
  omega

end Run

end DrawData

end Draw

end DescriptiveComplexity
