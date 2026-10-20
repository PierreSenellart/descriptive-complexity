/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexSpec
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawBuild
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
export Lax822549.WideMachines (WMLe WMSetLe WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The clocked program lays its file out

The file-laying phase, assembled: the run
(`DescriptiveComplexity.Draw.Prog.reachesIn_buildFile`) at the layout of
`DescriptiveComplexity.Draw.Data.blkLaid`, the write and the pointer of
`DescriptiveComplexity.Draw.Data.buildSpec`, and the rules of
`DescriptiveComplexity.Draw.Data.nexRule`.

What ties them is that a sweep of the file's stretch **is** a walk of the file:
every address the sweep stops at is some register's cell
(`DescriptiveComplexity.exists_ixSegCell_eq`), and the address it moves to is
the cell of the register the pointer moves to
(`DescriptiveComplexity.wmIncr_ixSegCell`). So the phase and the control at an
address are read off the register that address is – the block into the phase,
the tuple into the control – and the step the sweep asks for is one of the
three rules at that phase, chosen by whether the pointer's tuple is the last of
its block.

What the run asks of the tape outside the stretch is that it be **what the
background says** there, not that it be blank: the marker is planted before the
file is laid, and the marker's cell lies below the file.

The run is `DescriptiveComplexity.Draw.Data.reachesIn_buildBlkFile`, and what
it costs is the stretch: one step per register, which is
`(|K| + 1) · |A| ^ dd₀` of them (`DescriptiveComplexity.card_blkFile`).

The **guessing** phase is the same walk over the same registers, writing at each
the value the certificate has there
(`DescriptiveComplexity.Draw.Data.reachesIn_guessBlkTracks`); it exists for
every certificate, which is what makes it a guess. Only the write differs, so
the two share the pointer, the phase family and the step's case analysis.

After either sweep the machine stands one cell past the file: it steps back onto
the last register (`DescriptiveComplexity.Draw.Data.step_doneBack`) and walks
down to the marker (`reachesIn_homeAfterBuild`), which is
`DescriptiveComplexity.Draw.HomeKit`'s walk at the file's own top.

The three chain into `DescriptiveComplexity.Draw.Data.reachesIn_buildPhase`,
whose budget is `2 · card + base`: the stretch out and back, the turn-around,
and the descent from the file's foot to the marker.
`DescriptiveComplexity.Draw.Data.reachesIn_guessPhase` is the guess's copy of
that, at the same number – it is the same walk.

The three single steps that join the phases are here as well:
`DescriptiveComplexity.Draw.Data.step_startBuild` plants the marker and enters
the file, `step_homeBuildExit` turns round at the marker and re-enters it for
the guess, and `step_homeGuessExit` enters the evaluation. The whole opening is
those five legs, and `DescriptiveComplexity.TMData.reachesIn_five` adds them up:
twice a phase and three steps.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section BuildRun

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

/-! ### The step the sweep asks for, at a register -/

section Step

end Step

/-! ### The phase and the control at an address -/

section Families

end Families

/-! ### The written symbol -/

section Written

end Written

/-! ### The run -/

section Run

variable {SE PE G : Type} {ShE : SE → Type}

variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]

variable [LinearOrder (NexPh (Option dt.KIx) PE)] [Finite (NexPh (Option dt.KIx) PE)]

variable [Lax822549.WideMachines.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}

variable {coord : Fin dt.dd → dt.CtlIx} {f₀ : dt.CtlIx → A}

variable {γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) G}

variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}

variable {evalEntry : PE} {bot : Option dt.KIx}

variable {rEmb : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}

/-! ### The guessing sweep

The same walk over the same registers, with `DescriptiveComplexity.Draw.Data.guessSpec`
in place of `buildSpec`: what changes at a cell is the stage tracks, and which
value is written there is a *shape* of the rule, so the sweep is the program's
one nondeterministic phase. The steps below are the build's with the guessed
value carried along. -/

section Guess

end Guess

/-! ### The turn-around and the walk home -/

section Home

/-! ### The opening's steps, at any file

The five steps above read the file only through the *presentation* of the tape –
`Prog.trackTapeAt cell …` – so they hold at whatever cells a program's file has.
A program that is *handed* its file (`DescriptiveComplexity.WideRegAccept`) uses
them at the channel's cells, where a program that lays one uses them at
`DescriptiveComplexity.Draw.Data.blkLaid`. Nothing but the presentation
changes, and the two sweep sites the steps mention are parameters already. -/

section AnyFile

variable {I : Type} {cell : I → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop)}

variable {m : I → Prop}

variable {rest rest' :
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}

variable {f : dt.CtlIx → A} {botS : Option dt.KIx}

variable {rEmbS : ∀ i : NexSite SE, NexSh SE (Option dt.KIx) G ShE i → R'}

variable {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}

variable (hrulesS : ∀ (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) G ShE i),
  PR.rules (rEmbS i ρ) = dt.nexRule PR.one betaS γ ruleE evalEntry botS i ρ)

include hrulesS

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The opening step, at any file**: the machine plants the marker and the
bottom mark at the cell it starts on and moves right into the approach. -/
theorem step_startAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe v v')
    (hframe : ∀ r, r ≠ v → rest' r = rest r)
    (hwr : PR.passTracksAt cell Slot.mir rest' m v =
      Function.update (Function.update (PR.passTracksAt cell Slot.mir rest m v)
        Slot.wk PR.one) Slot.bot PR.one) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.start f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest' m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR h hvi hframe ?_
  rw [hwr]
  exact hasRight_start hrulesS f _

omit [Nonempty A] in
/-- **The approach walk, at any file**: the machine moves right in one phase,
writing nothing, as far as it likes. -/
theorem reachesIn_approachAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {s₀ s₁ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      (wideRank s₁ - wideRank s₀)
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₀,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl s₁,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  reachesIn_of_wideUp h hle fun _ _ hi _ _ =>
    Prog.step_move hR h hi (fun _ _ => rfl) (hasRight_approach hrulesS f _)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The approach's exit, at any file**: the machine stops walking and moves
right into the sweep's first phase. -/
theorem step_approachEnterAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {x y : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe x y) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.approachP f), Sum.inl x,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.buildP botS) f), Sum.inl y,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_approachExit hrulesS f _)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The dispatch out of the walk home, at any file**: at the marker the
machine turns round into the guessing phase, its pointer reset by the sweep's
own `st0`. -/
theorem step_homeBuildExitAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v s₀ : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe v s₀)
    (hex : dt.exitG PR.one (PR.passTracksAt cell Slot.mir rest m v)) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.guessP botS)
          (betaS.st0 f (PR.passTracksAt cell Slot.mir rest m v))),
        Sum.inl s₀,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeBuildExit hrulesS f _ hex)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The dispatch into the evaluation, at any file.** -/
theorem step_homeGuessExitAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe v v')
    (hex : dt.exitG PR.one (PR.passTracksAt cell Slot.mir rest m v)) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_move hR h hvi (fun _ _ => rfl) (hasRight_homeGuessExit hrulesS f _ hex)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **A sweep that is over at once, in one step**: when both of the sweep's
tests hold where it starts, the phase fires its exit rule – it writes what the
spec writes and leaves the pointer where the spec's roll-over leaves it, which
for `DescriptiveComplexity.Draw.Data.nullSpec` is nothing and the same
pointer. This is the whole of the file-laying phase of a program that is *handed*
its file. -/
theorem step_sweepDone (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe v v')
    (hroll : betaS.Roll botS f) (hdone : betaS.Done botS f)
    (hst : betaS.stRoll botS f (PR.passTracksAt cell Slot.mir rest m v) = f)
    (hwr : betaS.wr botS f (PR.passTracksAt cell Slot.mir rest m v) =
      PR.passTracksAt cell Slot.mir rest m v) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (NexPh.buildP botS) f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.buildDoneP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ := by
  refine Prog.step_move hR h hvi (fun _ _ => rfl) ?_
  have hstep := hasRight_buildLast (PR := PR) (rEmb := rEmbS) (β := betaS) (γ := γ)
    (ruleE := ruleE) (evalEntry := evalEntry) (bot := botS) hrulesS botS f
    (PR.passTracksAt cell Slot.mir rest m v) hroll hdone
  rw [hst, hwr] at hstep
  exact hstep

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The turn-around after a sweep, at any file**: in the done phase the
machine steps back one cell and its walk home begins there. It writes
nothing. -/
theorem step_doneBackAny (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {v v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi : WMIncr Lax822549.WideMachines.WMLe v v') :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt NexPh.buildDoneP f), Sum.inl v',
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt NexPh.homeBuildP f), Sum.inl v,
        wideTape (PR.trackTapeAt cell Slot.mir rest m) (PR.syElt PR.blank)⟩ :=
  Prog.step_moveBack hR h hvi (fun _ _ => rfl)
    (hasLeft_buildExit hrulesS f (PR.passTracksAt cell Slot.mir rest m v'))

end AnyFile

end Home

end Run

end BuildRun

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


