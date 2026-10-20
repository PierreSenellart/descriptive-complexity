/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawName
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawTable
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.IxAddr
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Key
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.LowFile
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexOuter
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
export Lax822549.WideMachines (WMLe WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# What the clocked program's file-laying sweep writes

`DescriptiveComplexity.Draw.SweepSpec` leaves the write to the caller, because
what a cell of the file holds is a fact about the layout and not about the shape
of the loop. This file is that fact at the layout a clocked program uses
(`DescriptiveComplexity.Draw.Data.blkLaid`): the sweep writes, at the register
the pointer names, the **mark** of that register – it is a register, whether it
is the first or the last of the file, its block one-hot, its coordinates, and
that it is canonically padded – and the blank in every track.

The one theorem is that this *is* the background the file's run installs
(`DescriptiveComplexity.Draw.Data.buildWr_eq_ixBack`): slot by slot, the mark
the pointer can compute agrees with
`DescriptiveComplexity.Draw.Data.ixBack` at the register's cell, given that
the state's own tracks are clear – which they are, the file being laid before
anything is written to it.

What makes the agreement possible at all is that a register's contents depend on
its block and its named tuple and on nothing else, which is the point the whole
index parameter was introduced for: the pointer holds exactly those, the block in
the phase and the tuple in the control.

The pointer's advance is here too: `DescriptiveComplexity.Draw.Data.ptrNext`
writes the next register's tuple into the control's coordinate slots and leaves
every other slot alone, and
`DescriptiveComplexity.Draw.Data.buildSpec` is the whole
`DescriptiveComplexity.Draw.SweepSpec` the file-laying phase runs at. The
guessing phase's write is here as well
(`DescriptiveComplexity.Draw.Data.guessWr`): the cell it read with the stage
tracks holding the guessed value, and nothing else touched.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

section BuildSpec

variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Finite A] [Nonempty A] [Finite R'] [Finite P'] [Finite dt.KIx]

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable [Finite (Univ A R' P' dt.KIx dt.dd)]

variable {dt}

/-! ### The pointer's advance, and the specification it makes -/

variable (dt) in
/-- **The sweep that does nothing**: it writes nothing, moves no pointer and is
over at once. A program that is *handed* its file – the register channel of
`DescriptiveComplexity.WideRegAccept` hands one over – has nothing to lay, and
this is what it puts where a file-laying program puts
`DescriptiveComplexity.Draw.Data.buildSpec`: the site's rules still exist, and
the one that fires is the one whose guard is «rolled over and done», so the
phase costs a single step.

Being trivial it is definable at once (`uSweepSpecDef_nullSpec`), and it needs
no coordinate map – which is the point, a pointer wide enough to name a register
being what no wide machine's control can hold
(`DescriptiveComplexity.Problems.Wide.Limits`). -/
noncomputable def nullSpec (B : Type) : SweepSpec A dt.CtlIx dt.SlotIx B where
  wr _ _ g := g
  st _ f _ := f
  st0 f _ := f
  stRoll _ f _ := f
  nx := id
  Roll _ _ := True
  Done _ _ := True

end BuildSpec

section GuessSpec

/-! ### What the guessing sweep writes

The guessing phase runs the same sweep over the same stretch with the background
on *both* sides (`DescriptiveComplexity.Draw.Prog.reachesIn_guessTracks`): what
changes at a cell is the stage tracks and nothing else, so the write is the cell
it read with those tracks set to the guessed value, and the value is a *shape* –
one rule per assignment of the tracks – which is the program's only
nondeterminism. -/

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' Q : Type}

variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Finite A] [Nonempty A] [Finite dt.KIx]

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable {PR : Prog A R' P' Q dt.SlotIx dt.KIx dt.dd}

variable {I : Type}

variable (dt) in
/-- **What the guessing sweep writes**: the cell it read, with the stage tracks
holding the guessed value. -/
noncomputable def guessWr (zero one : A) (x : dt.d.B.ι → Bool) (g : dt.SlotIx → A) :
    dt.SlotIx → A
  | .old i => bitVal zero one (x i = true)
  | .reg => g .reg
  | .regFirst => g .regFirst
  | .regLast => g .regLast
  | .blk c => g (.blk c)
  | .name j => g (.name j)
  | .pdd => g .pdd
  | .mir => g .mir
  | .tgt => g .tgt
  | .sav => g .sav
  | .val => g .val
  | .wk => g .wk
  | .bot => g .bot
  | .ltp => g .ltp
  | .new i => g (.new i)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A] [Nonempty A]
  [Finite dt.KIx] [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The guess's write installs the guessed tracks**: at the cell under the
head, the background of the state with its stage tracks replaced – which is what
the guessing run asks of the rule, and all it asks. -/
theorem guessWr_eq_passTracks {zero one : A} {hdd : dt.dd0 ≤ dt.dd}
    {lay : Layout dt A R' P' I} {st : TapeSt dt A R' P' I}
    (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {t : dt.SlotIx} (hne : ∀ i : dt.d.B.ι, (Slot.old i : dt.SlotIx) ≠ t)
    {m : I → Prop} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (x : dt.d.B.ι → Bool) (hx : ∀ i, (σ i r ↔ x i = true)) :
    dt.guessWr zero one x
        (PR.passTracksAt lay.cell t (dt.ixBack lay zero one hdd st) m r) =
      PR.passTracksAt lay.cell t
        (dt.ixBack lay zero one hdd { st with old := σ }) m r := by
  funext sl
  cases sl with
  | old i =>
    rw [PR.passTracks_of_ne (hne i) m r]
    exact (bitVal_congr (hx i)).symm
  | _ => rfl

variable (dt) in
/-- **The region-wide guess, specified**: the same write as the file's, and a
pointer that never moves – a control holding `dd₀` coordinates cannot count the
region, so the walk carries no pointer at all. Every step is a *roll-over* that
stays in its own block phase, which is the one arm of the guess site whose guard
is then always true; the walk's end is the site's own stopping rule and not a
test on the control. -/
noncomputable def regionSpec (zero one : A) :
    GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool) where
  wr := fun _ x _ g => dt.guessWr zero one x g
  st := fun _ _ f _ => f
  stRoll := fun _ _ f _ => f
  nx := id
  Roll := fun _ _ => True
  Done := fun _ _ => False

end GuessSpec

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


