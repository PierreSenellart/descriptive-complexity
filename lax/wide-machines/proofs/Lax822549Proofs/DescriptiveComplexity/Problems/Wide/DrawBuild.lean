/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSweep
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawBack
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

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' Q : Type}

variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

variable {PR : Prog A R' P' Q dt.SlotIx dt.KIx dt.dd}

variable {I : Type}

/-! ### Laying the file out -/

/-! ### Guessing the certificate -/

/-- **A program guesses its certificate onto a stretch.** From the background of
a state, the sweep reaches the background of the same state with its stage tracks
replaced by `σ`, provided `σ` agrees with them outside the stretch – the sweep
never goes there. -/
theorem reachesIn_guessTracks (F : LaidFile dt A R' P' I)
    (hR : PR.table.Reads) (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {t : dt.SlotIx} {m : I → Prop}
    {hdd : dt.dd0 ≤ dt.dd} {st : TapeSt dt A R' P' I}
    (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {ph : (Univ A R' P' dt.KIx dt.dd → Prop) → P'} {fc : (Univ A R' P' dt.KIx dt.dd → Prop) → Q → A}
    {s₀ s₁ : Univ A R' P' dt.KIx dt.dd → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (hout : ∀ (i : dt.d.B.ι) (r : Univ A R' P' dt.KIx dt.dd → Prop),
      WMSetLt Lax822549.WideMachines.WMLe r s₀ ∨ ¬WMSetLt Lax822549.WideMachines.WMLe r s₁ → (σ i r ↔ st.old i r))
    (hstep : ∀ s u : Univ A R' P' dt.KIx dt.dd → Prop, WMIncr Lax822549.WideMachines.WMLe s u →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe u s₁ →
      PR.HasRight (ph s) (fc s) (PR.passTracksAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one hdd st) m s) (ph u) (fc u)
        (PR.passTracksAt F.cell t
          (dt.ixBack F.toLayout PR.zero PR.one hdd { st with old := σ }) m s)) :
    (Lax822549.WideMachines.wideData (Univ A R' P' dt.KIx dt.dd)).ReachesIn (wideRank s₁ - wideRank s₀)
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

end Lax822549Proofs.DescriptiveComplexity


