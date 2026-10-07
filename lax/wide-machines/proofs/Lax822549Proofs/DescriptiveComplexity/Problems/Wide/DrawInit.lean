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

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# The two ends of a program's run, at the pass-layer presentation

`DescriptiveComplexity.Draw.Table.isInit` and
`DescriptiveComplexity.Draw.Table.acceptsSpace` state the two ends of a run at
an arbitrary tape function; a program's phases are all stated at the
`DescriptiveComplexity.Draw.Prog.trackTapeAt` presentation. This file joins them.

`DescriptiveComplexity.Draw.Prog.initBack` is the background at time zero – the
mark of the cell's element on the register file, the blank everywhere else –
and `DescriptiveComplexity.Draw.Prog.trackTape_initBack` says the initial tape
*is* the presentation walking any track whose mark and blank digits are clear,
with the empty track: which is why the all-blank start needs no initialization
sweep. On top of it, `DescriptiveComplexity.Draw.Prog.isInit_prog` is the
initial configuration a program's first phase starts from, and
`DescriptiveComplexity.Draw.Prog.acceptsSpace_prog` /
`DescriptiveComplexity.Draw.Prog.dwideAcceptSpace_prog` are what a finished run
delivers – for the latter, together with the separation argument
(`DescriptiveComplexity.Draw.Prog.sep_of`), the two promises of
`DescriptiveComplexity.DWideAcceptSpace`.
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

variable (PR : Prog A R P Q W K dd)

/-! ### The background at time zero -/

open Classical in
/-- **The background at time zero**: the mark of the cell's element on the
register file, the blank everywhere else. -/
noncomputable def initBack : (Univ A R P K dd → Prop) → W → A := fun r s =>
  if h : ∃ x : Univ A R P K dd, r = wmSeg x then PR.mark h.choose s else PR.blank s

variable {PR}

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- On a register cell the background is the mark. -/
theorem initBack_wmSeg (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd)))
    (x : Univ A R P K dd) : PR.initBack (wmSeg x) = PR.mark x := by
  funext s
  rw [initBack, dif_pos ⟨x, rfl⟩]
  have hspec := (⟨x, rfl⟩ : ∃ y : Univ A R P K dd, wmSeg x = wmSeg y).choose_spec
  rw [show (⟨x, rfl⟩ : ∃ y : Univ A R P K dd, wmSeg x = wmSeg y).choose = x from
    (wmSeg_injective hlin hspec).symm]

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- Off the register file the background is the blank. -/
theorem initBack_of_not_reg {r : Univ A R P K dd → Prop}
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) : PR.initBack r = PR.blank := by
  funext s
  rw [initBack, dif_neg fun hc => hno _ hc.choose_spec]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The initial tape is the pass-layer presentation**, walking any track
whose mark and blank digits are clear, with the empty track: the all-blank
start needs no initialization sweep. -/
theorem trackTape_initBack {t₀ : W}
    (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero) (hb : PR.blank t₀ = PR.zero) :
    PR.trackTapeAt wmSeg t₀ PR.initBack (fun _ => False) =
      fun r => PR.syElt (PR.initBack r) := by
  funext r
  refine congrArg PR.syElt (funext fun s => ?_)
  change (if s = t₀ then bitVal PR.zero PR.one (regBit (fun _ => False) r)
    else PR.initBack r s) = PR.initBack r s
  by_cases hs : s = t₀
  · subst hs
    rw [if_pos rfl, bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)]
    rw [initBack]
    split
    · exact (hmk _).symm
    · exact hb.symm
  · rw [if_neg hs]

/-! ### The two ends of a run -/

/-- **The initial configuration of a program**: its start phase and pointer,
the head on the empty address, the tape presenting the marks with any clear
track walked. -/
theorem isInit_prog (hR : PR.table.Reads) (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) :
    (Lax822549.WideMachines.wideData (Univ A R P K dd)).IsInit
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ := by
  rw [trackTape_initBack hmk hb]
  exact PR.table.isInit hR hall
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- A program's accepting states are the table's. -/
theorem accept_table {p : P} {f : Q → A} (h : PR.accept p f) :
    PR.table.accept p (stPl (W := W) PR.zero f) := by
  have he : (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) = f :=
    funext fun q => by
      rw [stPl, unslot_slotPl]
      exact stVec_inl f q
  change PR.accept p fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)
  rw [he]
  exact h

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Lax822549.WideMachines.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **And conversely**: a state the table accepts is one the program accepts.
The pointer is recovered from the payload by the same equation, which is what a
*backward* reading needs – it is handed an accepting configuration and has to
say what the program decided. -/
theorem accept_of_isAcc {p : P} {f : Q → A}
    (h : PR.table.IsAcc (PR.stElt p f)) : PR.accept p f := by
  have h2 : PR.table.accept p (stPl (W := W) PR.zero f) := by
    have h3 : PR.table.accept p
        (unpad PR.table.payload_le (pad PR.zero (stPl (W := W) PR.zero f))) := h.2
    rwa [unpad_pad] at h3
  have he : (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) = f :=
    funext fun q => by
      rw [stPl, unslot_slotPl]
      exact stVec_inl f q
  change PR.accept p (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) at h2
  rwa [he] at h2

/-- **A program's run accepts in bounded space**: start as
`DescriptiveComplexity.Draw.Prog.isInit_prog` says, roam, and end in a phase and
pointer the program accepts. -/
theorem acceptsSpace_prog (hR : PR.table.Reads)
    (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {cfg : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (Lax822549.WideMachines.wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : (Lax822549.WideMachines.wideData (Univ A R P K dd)).AcceptsSpace := by
  rw [trackTape_initBack hmk hb] at hreach
  exact PR.table.acceptsSpace hR hall
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))
    hreach hstate (accept_table ha)

end Prog

end Draw

end Lax822549Proofs.DescriptiveComplexity


