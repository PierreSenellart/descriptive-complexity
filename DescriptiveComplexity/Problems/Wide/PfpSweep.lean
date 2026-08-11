/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSub

/-!
# Plain sweeps: one step per address, a flag or a write

COMPARE and COPY (EXPONENTIAL.md §6.4.4) are *plain* sweeps: one step per
address of a stretch, no register visits, no rounds. This file is their two
shapes.

* `DescriptiveComplexity.Pfp.Prog.reaches_flagSweep` – the machine walks the
  stretch asking one question per cell, the verdict carried in the phase: the
  passing one exactly while every cell so far passed
  (`DescriptiveComplexity.sweepState`, whose two ends the caller reads off
  `DescriptiveComplexity.sweepState_bot` /
  `DescriptiveComplexity.sweepStateAfter_pos` / `_neg`). COMPARE is this with
  *these two stage tracks agree here*.
* `DescriptiveComplexity.Pfp.Prog.reaches_writeSweep` – the machine walks the
  stretch rewriting each cell's background once, the background presented as a
  function of the frontier. COPY is this with *the current stage track takes
  the next one's digit*.

Both take their rules **cell-coupled and bounded to the stretch**, for the
reason `PfpAdv` taught: a sweep whose stepping rules covered every cell could
never stop. How a program's actual rules respect the bound is its own
business – the intended device is a permanent **end marker** planted at the
top of the logical interval once, at startup, since a cell of the working area
is not otherwise recognizable (its tracks are stage bits like any other).
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

/-- **A sweep asking one question per cell**, the verdict in the phase: from the
bottom of the stretch in the passing phase, the machine arrives at the top in
the phase `DescriptiveComplexity.sweepState` names – passing exactly when every
cell strictly below passed. The three rule families are the two branches of the
passing phase and the cruise of the failing one, each at the cells of the
stretch only. -/
theorem reaches_flagSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {rest : (Univ A R P K dd → Prop) → W → A} {m : Univ A R P K dd → Prop}
    {Test : (Univ A R P K dd → Prop) → Prop} {py pn : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hstepY : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → Test r →
      PR.HasRight py f (PR.passTracks t rest m r) py f (PR.passTracks t rest m r))
    (hstepN : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ → ¬Test r →
      PR.HasRight py f (PR.passTracks t rest m r) pn f (PR.passTracks t rest m r))
    (hstepP : ∀ r r' : Univ A R P K dd → Prop, WMIncr WMLe r r' →
      WMSetLe WMLe s₀ r → WMSetLe WMLe r' s₁ →
      PR.HasRight pn f (PR.passTracks t rest m r) pn f (PR.passTracks t rest m r)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₀), Sum.inl s₀,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) s₁), Sum.inl s₁,
        wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩ := by
  refine reaches_of_wideUp
    (conf := fun r => ⟨Sum.inr (sweepState Test (PR.stElt py f) (PR.stElt pn f) r),
      Sum.inl r, wideTape (PR.trackTape t rest m) (PR.syElt PR.blank)⟩)
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

/-- **A sweep rewriting each cell once**: the background is a function of the
frontier – everything strictly below has its new value, everything at or above
its old one – and one rule per cell writes the change as the head leaves. COPY
is this sweep. -/
theorem reaches_writeSweep (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t : W} {m : Univ A R P K dd → Prop}
    {restAt : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    {p : P} {f : Q → A}
    {s₀ s₁ : Univ A R P K dd → Prop} (hle : WMSetLe WMLe s₀ s₁)
    (hframe : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      ∀ r : Univ A R P K dd → Prop, r ≠ s → restAt u r = restAt s r)
    (hstep : ∀ s u : Univ A R P K dd → Prop, WMIncr WMLe s u →
      WMSetLe WMLe s₀ s → WMSetLe WMLe u s₁ →
      PR.HasRight p f (PR.passTracks t (restAt s) m s) p f
        (PR.passTracks t (restAt u) m s)) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₀,
        wideTape (PR.trackTape t (restAt s₀) m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p f), Sum.inl s₁,
        wideTape (PR.trackTape t (restAt s₁) m) (PR.syElt PR.blank)⟩ := by
  refine reaches_of_wideUp
    (conf := fun r => ⟨Sum.inr (PR.stElt p f), Sum.inl r,
      wideTape (PR.trackTape t (restAt r) m) (PR.syElt PR.blank)⟩)
    hlin hle fun s u hi hlb hub => ?_
  exact PR.step_move hR hlin hi (hframe s u hi hlb hub) (hstep s u hi hlb hub)

end Prog

end Pfp

end DescriptiveComplexity
