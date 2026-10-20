/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSub
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe WMSetLe wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# A round trip to the register file

Every visit the program pays to its register file has the same itinerary: scan
up to the file's top, **bounce** (two steps changing phase, since the scan
cannot overshoot the maximal cell), run one pass down the file, and scan back
to the working-cell marker. Only the middle differs – a mirror increment, a
file test, a track write. `DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip`
is the itinerary with the middle a *hypothesis*: any run from the file's top
to just below its bottom, changing at most the walked track.

The seek loop, the test rounds of a random access and the gate checks are all
this composite around their respective passes; `DrawAdv`'s ADVANCE is the same
shape inlined with its two marker steps.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

variable [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)]

variable [Finite A] [Finite R] [Finite P] [Finite K]

variable {I : Type} {ile : I → I → Prop}

variable {PR : Prog A R P Q W K dd}

/-- **A round trip to the register file**: from anywhere at or below the file's
top, scan up to it, bounce into the pass phase, run the middle – any run from
the top to just below the file, changing at most the walked track – and scan
back down to the working-cell marker. The marker sits strictly below the file,
so the return scan's stop is unique. -/
theorem reachesIn_fileRoundTrip (F : IxFile (Univ A R P K dd) I ile) (hR : PR.table.Reads)
    (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd))) (hix : Lax904597.Machines.IsLinOrd ile)
    {t rl wk : W} (hnerl : rl ≠ t) (hnewk : wk ≠ t)
    {gtop gbot : I} (hbot : ∀ y, ile gbot y)
    {rest : (Univ A R P K dd → Prop) → W → A} {m m₂ : I → Prop}
    {wkAddr : Univ A R P K dd → Prop}
    (hrl : ∀ r : Univ A R P K dd → Prop, rest r rl = bitVal PR.zero PR.one (r = F.cell gtop))
    (hwkS : ∀ r : Univ A R P K dd → Prop, rest r wk = bitVal PR.zero PR.one (r = wkAddr))
    {p₁ p₂b pIn pOut : P} {fc : Q → A}
    (hscanUp : ∀ g : W → A, g rl ≠ PR.one → PR.HasRight p₁ fc g p₁ fc g)
    (hb₁ : PR.HasLeft p₁ fc (PR.passTracksAt F.cell t rest m (F.cell gtop)) p₂b fc
      (PR.passTracksAt F.cell t rest m (F.cell gtop)))
    (hb₂ : ∀ g : W → A, PR.HasRight p₂b fc g pIn fc g)
    {pend : Univ A R P K dd → Prop} (hpend : WMIncr Lax822549.WideMachines.WMLe pend (F.cell gbot)) {n : ℕ}
    (hmid : (Lax822549.WideMachines.wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (PR.stElt pIn fc), Sum.inl (F.cell gtop),
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pOut fc), Sum.inl pend,
        wideTape (PR.trackTapeAt F.cell t rest m₂) (PR.syElt PR.blank)⟩)
    (hback : ∀ r : Univ A R P K dd → Prop, (∀ x : I, r ≠ F.cell x) →
      PR.passTracksAt F.cell t rest m₂ r wk ≠ PR.one →
      PR.HasLeft pOut fc (PR.passTracksAt F.cell t rest m₂ r) pOut fc
        (PR.passTracksAt F.cell t rest m₂ r))
    (hwkLt : WMSetLt Lax822549.WideMachines.WMLe wkAddr (F.cell gbot))
    {s : Univ A R P K dd → Prop} (hsle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s (F.cell gtop)) :
    (Lax822549.WideMachines.wideData (Univ A R P K dd)).ReachesIn
      ((wideRank (F.cell gtop) - wideRank s) + 2 + n + (wideRank pend - wideRank wkAddr))
      ⟨Sum.inr (PR.stElt p₁ fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt pOut fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell t rest m₂) (PR.syElt PR.blank)⟩ := by
  -- the file top's predecessor, for the bounce
  obtain ⟨pt, hpt⟩ := exists_wmPred hlin (s := F.cell gtop) (F.cell_nonempty gtop)
  -- the scan up to the file top
  have hscan := reachesIn_toCell (cell := F.cell) (StopG := fun g => g rl = PR.one) hR hlin
    (t := t) (rest := rest) (m := m) (p := p₁) (f := fc)
    (fun g hg => hscanUp g hg) (u := F.cell gtop) (s := s)
    (by rw [passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)
    hsle
    (fun r _ hstop => by
      rw [passTracks_of_ne hnerl, hrl] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  -- the bounce
  have s₃ := PR.step_moveBack (rest := rest) (rest' := rest) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₁) (p' := p₂b) (f := fc) (f' := fc) hb₁
  have s₄ := PR.step_move (t := t) (rest := rest) (rest' := rest) (m := m) hR hlin hpt
    (fun _ _ => rfl) (p := p₂b) (p' := pIn) (f := fc) (f' := fc)
    (hb₂ (PR.passTracksAt F.cell t rest m pt))
  -- the return scan: every cell at or below `pend` is nobody's register
  have hnonreg : ∀ r : Univ A R P K dd → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r pend →
      ∀ x : I, r ≠ F.cell x := by
    intro r hle x hrx
    subst hrx
    exact ((F.lt_iff hix x gbot).mp
      ((wmSetLt_iff_of_wmIncr hlin hpend (F.cell x)).mpr hle)).2 (hbot x)
  have hle_back : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe wkAddr pend :=
    (wmSetLt_iff_of_wmIncr hlin hpend wkAddr).mp hwkLt
  have hret := reachesIn_toCellBackC (cell := F.cell) (StopG := fun g => g wk = PR.one) hR hlin
    (t := t) (rest := rest) (m := m₂) (p := pOut) (f := fc)
    (fun r hle hstop => hback r (hnonreg r hle) hstop) (u := wkAddr) (s := pend)
    (by rw [passTracks_of_ne hnewk, hwkS]; exact bitVal_pos rfl)
    hle_back
    (fun r _ hstop => by
      rw [passTracks_of_ne hnewk, hwkS] at hstop
      by_contra hc
      rw [bitVal_neg hc] at hstop
      exact PR.zero_ne_one hstop)
  exact (hscan.trans (TMData.ReachesIn.head s₃ (TMData.ReachesIn.head s₄
    (hmid.trans hret)))).mono (by omega)

end Prog

end Draw

end Lax822549Proofs.DescriptiveComplexity


