/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSub

/-!
# Plain sweeps: one step per address, a flag or a write

COMPARE and COPY are *plain* sweeps: one step per
address of a stretch, no register visits, no rounds. This file is their two
shapes.

* `DescriptiveComplexity.Draw.Prog.reaches_flagSweep` – the machine walks the
  stretch asking one question per cell, the verdict carried in the phase: the
  passing one exactly while every cell so far passed
  (`DescriptiveComplexity.sweepState`, whose two ends the caller reads off
  `DescriptiveComplexity.sweepState_bot` /
  `DescriptiveComplexity.sweepStateAfter_pos` / `_neg`). COMPARE is this with
  *these two stage tracks agree here*.
* `DescriptiveComplexity.Draw.Prog.reaches_writeSweep` – the machine walks the
  stretch rewriting each cell's background once, the background presented as a
  function of the frontier. COPY is this with *the current stage track takes
  the next one's digit*.

Both take their rules **cell-coupled and bounded to the stretch**, for the
reason `DrawAdv` taught: a sweep whose stepping rules covered every cell could
never stop. How a program's actual rules respect the bound is its own
business – the intended device is a permanent **end marker** planted at the
top of the logical interval once, at startup, since a cell of the working area
is not otherwise recognizable (its tracks are stage bits like any other).
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

/-- **A sweep asking one question per cell**, the verdict in the phase: from the
bottom of the stretch in the passing phase, the machine arrives at the top in
the phase `DescriptiveComplexity.sweepState` names – passing exactly when every
cell strictly below passed. The three rule families are the two branches of the
passing phase and the cruise of the failing one, each at the cells of the
stretch only. -/
theorem reachesIn_flagSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {Test : (Univ A R P K dd → Prop) → Prop} {py pn : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstepY : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → Test r →
      PR.HasRight py f (PR.passTracksAt cell t rest m r) py f (PR.passTracksAt cell t rest m r))
    (hstepN : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → ¬Test r →
      PR.HasRight py f (PR.passTracksAt cell t rest m r) pn f (PR.passTracksAt cell t rest m r))
    (hstepP : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ →
      PR.HasRight pn f (PR.passTracksAt cell t rest m r) pn f (PR.passTracksAt cell t rest m r)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₀), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₁), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ := by
  refine reachesIn_of_wideUp
    (conf := fun r => ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) r),
      Sum.inl r, wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩)
    hlin hle fun s u hi hlb hub => ?_
  rw [show sweepState Test (PR.stElt py f) (PR.stElt pn f) u =
    sweepStateAfter Test (PR.stElt py f) (PR.stElt pn f) s from
      (sweepStateAfter_succ hlin hi).symm]
  by_cases hall : ∀ r : Univ A R P K dd → Prop, WMSetLt WMLe r s → Test r
  · rw [show sweepState Test (PR.stElt py f) (PR.stElt pn f) s = PR.stElt py f from
      if_pos hall]
    by_cases hTest : Test s
    · rw [show sweepStateAfter Test (PR.stElt py f) (PR.stElt pn f) s = PR.stElt py f from
        sweepStateAfter_pos fun r hr => by
          rcases eq_or_ne r s with rfl | hne
          · exact hTest
          · exact hall r ((wmSetLt_iff r s).mpr ⟨hr, hne⟩)]
      exact PR.step_move hR hlin hi (fun _ _ => rfl) (hstepY s u hi hlb hub hTest)
    · rw [show sweepStateAfter Test (PR.stElt py f) (PR.stElt pn f) s = PR.stElt pn f from
        sweepStateAfter_neg ((isLinOrd_wmSetLe hlin).1 s) hTest]
      exact PR.step_move hR hlin hi (fun _ _ => rfl) (hstepN s u hi hlb hub hTest)
  · obtain ⟨r₀, hr₀⟩ := Classical.exists_not_of_not_forall hall
    have hfail : ∃ r : Univ A R P K dd → Prop, WMSetLt WMLe r s ∧ ¬Test r := by
      by_contra hc
      push Not at hc
      exact hall fun r hr => hc r hr
    obtain ⟨r₁, hr₁lt, hr₁⟩ := hfail
    rw [show sweepState Test (PR.stElt py f) (PR.stElt pn f) s = PR.stElt pn f from
      if_neg hall]
    rw [show sweepStateAfter Test (PR.stElt py f) (PR.stElt pn f) s = PR.stElt pn f from
      sweepStateAfter_neg ((wmSetLt_iff r₁ s).mp hr₁lt).1 hr₁]
    exact PR.step_move hR hlin hi (fun _ _ => rfl) (hstepP s u hi hlb hub)

/-- **A flag sweep**, the budget forgotten. -/
theorem reaches_flagSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}
    {Test : (Univ A R P K dd → Prop) → Prop} {py pn : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstepY : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → Test r →
      PR.HasRight py f (PR.passTracksAt cell t rest m r) py f (PR.passTracksAt cell t rest m r))
    (hstepN : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → ¬Test r →
      PR.HasRight py f (PR.passTracksAt cell t rest m r) pn f (PR.passTracksAt cell t rest m r))
    (hstepP : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ →
      PR.HasRight pn f (PR.passTracksAt cell t rest m r) pn f (PR.passTracksAt cell t rest m r)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₀), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₁), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_flagSweep hR hlin hle hstepY hstepN hstepP).reflTransGen

/-- **A writing sweep carrying a pointer.** The same sweep with the state's
*pointer* advancing with the head: at the cell `s` the program stands in the
phase `p` at the pointer `fc s`, and the rule that rewrites `s` leaves it at
`fc u`. The phase does not move, so this is still one rule family.

A pointer that varies is what lets a sweep write something different in every
cell. The tape a phase like this starts from is blank, so the rule has nothing
to read that distinguishes one cell from the next; what distinguishes them is the
pointer, whose slots hold elements of the instance. That is how a program lays
down a pattern indexed by the elements – its own register file, for instance. -/
theorem reachesIn_writeSweepSt (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {ph : (Univ A R P K dd → Prop) → P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt cell t (restAt s) m s) (ph u) (fc u)
        (PR.passTracksAt cell t (restAt u) m s)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (ph s₀) (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ph s₁) (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (restAt s₁) m) (PR.syElt PR.blank)⟩ := by
  refine reachesIn_of_wideUp
    (conf := fun r => ⟨Sum.inr (PR.stElt (ph r) (fc r)), Sum.inl r,
      wideTape (PR.trackTapeAt cell t (restAt r) m) (PR.syElt PR.blank)⟩)
    hlin hle fun s u hi hlb hub => ?_
  exact PR.step_move hR hlin hi (hframe s u hi hlb hub) (hstep s u hi hlb hub)

/-- **A writing sweep carrying a pointer**, the budget forgotten. -/
theorem reaches_writeSweepSt (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {p : P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p (fc s) (PR.passTracksAt cell t (restAt s) m s) p (fc u)
        (PR.passTracksAt cell t (restAt u) m s)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (restAt s₁) m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_writeSweepSt hR hlin hle hframe hstep).reflTransGen

/-- **A sweep rewriting each cell once**: the background is a function of the
frontier – everything strictly below has its new value, everything at or above
its old one – and one rule per cell writes the change as the head leaves. COPY
is this sweep. -/
theorem reachesIn_writeSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p f (PR.passTracksAt cell t (restAt s) m s) p f
        (PR.passTracksAt cell t (restAt u) m s)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (restAt s₁) m) (PR.syElt PR.blank)⟩ := by
  refine reachesIn_of_wideUp
    (conf := fun r => ⟨Sum.inr (PR.stElt p f), Sum.inl r,
      wideTape (PR.trackTapeAt cell t (restAt r) m) (PR.syElt PR.blank)⟩)
    hlin hle fun s u hi hlb hub => ?_
  exact PR.step_move hR hlin hi (hframe s u hi hlb hub) (hstep s u hi hlb hub)

/-- **A writing sweep**, the budget forgotten. -/
theorem reaches_writeSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p f (PR.passTracksAt cell t (restAt s) m s) p f
        (PR.passTracksAt cell t (restAt u) m s)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (restAt s₁) m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_writeSweep hR hlin hle hframe hstep).reflTransGen

/-! ### Installing a background

The two phases a *clocked* program opens with – laying its own register file out
and guessing the certificate onto its working region – are one shape: sweep a
stretch replacing the background wholesale, one cell per step. The frontier form
`DescriptiveComplexity.midTape` is what makes them a sweep rather than an
induction, and the new background is a **parameter**, so the guessing reading is
the same statement at an arbitrary choice. -/

/-- **A phase installing a new background over a stretch.** From the bottom of
the stretch with the old background everywhere, one rule per cell rewrites that
cell and moves right; the run ends at the top of the stretch with the new
background below it and the old one above. The pointer walks along, so the rule
at a cell may write something that depends on where the head is. -/
theorem reachesIn_installSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {bg₀ bg₁ : (Univ A R P K dd → Prop) → W → A}
    {ph : (Univ A R P K dd → Prop) → P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt cell t bg₀ m s) (ph u) (fc u)
        (PR.passTracksAt cell t bg₁ m s)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (ph s₀) (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (midTape bg₀ bg₁ s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ph s₁) (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (midTape bg₀ bg₁ s₁) m) (PR.syElt PR.blank)⟩ := by
  refine reachesIn_writeSweepSt (restAt := midTape bg₀ bg₁) hR hlin hle
    (fun s u hi _ _ => midTape_agree hlin bg₀ bg₁ hi) fun s u hi hlb hub => ?_
  rw [Prog.passTracks_congr (midTape_self bg₀ bg₁ s) m,
    Prog.passTracks_congr (midTape_incr hlin bg₀ bg₁ hi) m]
  exact hstep s u hi hlb hub

/-- **A phase installing a new background over a stretch**, the budget
forgotten. -/
theorem reaches_installSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {bg₀ bg₁ : (Univ A R P K dd → Prop) → W → A}
    {p : P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p (fc s) (PR.passTracksAt cell t bg₀ m s) p (fc u)
        (PR.passTracksAt cell t bg₁ m s)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t (midTape bg₀ bg₁ s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t (midTape bg₀ bg₁ s₁) m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_installSweep hR hlin hle hstep).reflTransGen
/-- **A phase installing a background that already agrees outside the stretch.**
The sweep only ever writes inside the stretch, so if the background it is
installing is the one already there below the start and at or above the end,
the run begins and ends at that background *whole* rather than at a frontier
form. That is the shape every opening phase of a program takes: what it changes
lies in a stretch, and what lies outside it was right to begin with. -/
theorem reachesIn_installOut (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {bg₀ bg₁ : (Univ A R P K dd → Prop) → W → A}
    {ph : (Univ A R P K dd → Prop) → P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hbelow : ∀ r : Univ A R P K dd → Prop, WMSetLt WMLe r s₀ → bg₁ r = bg₀ r)
    (habove : ∀ r : Univ A R P K dd → Prop, ¬WMSetLt WMLe r s₁ → bg₁ r = bg₀ r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt cell t bg₀ m s) (ph u) (fc u)
        (PR.passTracksAt cell t bg₁ m s)) :
    (wideData (Univ A R P K dd)).ReachesIn (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt (ph s₀) (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t bg₀ m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ph s₁) (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t bg₁ m) (PR.syElt PR.blank)⟩ := by
  have hstart : midTape bg₀ bg₁ s₀ = bg₀ := by
    refine funext fun r => ?_
    by_cases hc : WMSetLt WMLe r s₀
    · exact (if_pos hc).trans (hbelow r hc)
    · exact if_neg hc
  have hend : midTape bg₀ bg₁ s₁ = bg₁ := by
    refine funext fun r => ?_
    by_cases hc : WMSetLt WMLe r s₁
    · exact if_pos hc
    · exact (if_neg hc).trans (habove r hc).symm
  have hrun := reachesIn_installSweep (cell := cell) (bg₀ := bg₀) (bg₁ := bg₁)
    hR hlin hle hstep
  rwa [hstart, hend] at hrun

/-- **A phase installing a background that already agrees outside the stretch**,
the budget forgotten. -/
theorem reaches_installOut (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : I → Prop}
    {bg₀ bg₁ : (Univ A R P K dd → Prop) → W → A}
    {p : P} {fc : (Univ A R P K dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hbelow : ∀ r : Univ A R P K dd → Prop, WMSetLt WMLe r s₀ → bg₁ r = bg₀ r)
    (habove : ∀ r : Univ A R P K dd → Prop, ¬WMSetLt WMLe r s₁ → bg₁ r = bg₀ r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p (fc s) (PR.passTracksAt cell t bg₀ m s) p (fc u)
        (PR.passTracksAt cell t bg₁ m s)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p (fc s₀)), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell t bg₀ m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p (fc s₁)), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell t bg₁ m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_installOut hR hlin hle hbelow habove hstep).reflTransGen

end Prog

end Draw

end DescriptiveComplexity
