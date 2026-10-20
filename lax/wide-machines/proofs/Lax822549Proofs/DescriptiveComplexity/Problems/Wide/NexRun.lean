/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexBuild
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexGuess
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexDet
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawInit
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.NexEval
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawTable
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Roam
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
export Lax904597.Machines (Config IsLinOrd TMData)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The clocked program's whole run, and its clock

The two halves are counted separately – the opening and the evaluation
(`DescriptiveComplexity.Draw.Data.nexEval_reachesIn`) – and this file puts
them together and compares the sum with the clock.

The opening is `DescriptiveComplexity.Draw.Data.reachesIn_openingRegion`,
here: the approach walk up to the file's base, the file-laying sweep, and the
guess along the *region* below the file – one bit per address, which is what the
guessed relations are – for
`2·R + 2·base + (the guessed stretch out and back) + 4`, and `openingRegion_le`
bounds that
by the number of addresses.

Two things are worth naming. The **presentation bridge**: the opening is stated
with the tape walked along the mirror track and the evaluation along VAL, and
the two are the same tape whenever both marks are the background's own
(`DescriptiveComplexity.Draw.trackTape_of_back`), so the caller hands that
equality over rather than either run being restated. And the **arithmetic**:
the total is «opening + rounds × width», which is `mul_add_lt_two_pow`'s shape –
so what the clock asks is that the opening and each of the evaluation's two
factors fit the region, with one surplus block of slack for the additive term.
The opening is a bare number there
(`nexTotal_lt_two_pow`), so either shape of it is compared the same way.

The initial end is here as well, and it is three small facts.
`DescriptiveComplexity.Draw.Prog.trackTapeAt_initBack` says the all-blank tape is
the pass-layer presentation at *any* file – which a clocked program needs,
because its file does not exist at time zero – and
`DescriptiveComplexity.Draw.Data.startBack` with `startBack_frame` /
`startBack_wr` is the background the opening's first step leaves: the one it
started from with the marker planted, which is the frame condition and the write
that step asks for.

The forward direction lands here too (`nexProg_wideAccept`): an accepting run
of fewer than `2 ^ n` steps from the initial configuration is a yes-instance of
`DescriptiveComplexity.WideAccept`. Two of its hypotheses are `rfl` at the
assembled program, and that is the point of the program **declining the input
channel's marks**: with `mark` the blank, the tape is blank everywhere at time
zero and the channel's ruler is not there to be mistaken for a register
(`trackTape_blank_congr` for the presentations).

The backward direction's foundation is here as well: `nexProg_sepOn` – the
program separates at every post-guess phase, across sites by the owner map and
within a site by `nexSep_postGuess` – and `nexProg_uniqueFrom`, which is what a
reduction reads its certificate off an *arbitrary* accepting run with. The fact
it stands on – that the evaluation's rules never leave the post-guess phases –
is proved, not assumed:
`nexEvalRuleF_postGuess`, and under it a chain of «this machinery leaves only
into its own phases or its exit» lemmas, one per builder, down to the trips.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

section Total

end Total

section Bridge

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}

variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}

/-- **Two presentations of one tape**: a run stated along a track whose digits
the background already carries is the same tape as one stated along another such
track, so a leg walking the mirror composes with a leg walking VAL without
either being restated. -/
theorem trackTape_ixBack_congr {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} {t t' : dt.SlotIx} {m m' : I → Prop}
    (hm : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r t =
      bitVal PR.zero PR.one (bitAtOf F.cell m r))
    (hm' : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r t' =
      bitVal PR.zero PR.one (bitAtOf F.cell m' r)) :
    PR.trackTapeAt F.cell t
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m =
      PR.trackTapeAt F.cell t'
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) m' :=
  (trackTape_of_back F.toIxFile hm).trans (trackTape_of_back F.toIxFile hm').symm

/-- **The mirror and VAL presentations agree**: the opening walks the mirror and
the evaluation walks VAL, and both marks are the state's own, so the two runs
compose with no rewriting in between. -/
theorem trackTape_ixBack_mir_val {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} :
    PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir =
      PR.trackTapeAt F.cell Slot.val
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val :=
  trackTape_ixBack_congr (fun _ => rfl) (fun _ => rfl)

/-- **The opening leaves the tape the evaluation starts from**: the opening
walks the mirror at the empty mark, the evaluation walks VAL at the state's own,
and the state whose mirror is empty presents the same tape either way. This is
the one rewrite between `reachesIn_openingRegion` and
`DescriptiveComplexity.Draw.Data.nexIxEvalB_reachesIn`. -/
theorem trackTape_ixBack_mir_empty_val {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hmir : st.mir = fun _ => False) :
    PR.trackTapeAt F.cell Slot.mir
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) =
      PR.trackTapeAt F.cell Slot.val
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val := by
  rw [← hmir]
  exact trackTape_ixBack_mir_val

/-- **The opening's last configuration is the evaluation's first**: same phase,
same head, and the same tape – the opening presents it along the mirror at the
empty mark, the evaluation along VAL at the state's own, and a state whose
mirror is empty presents both the same way. This is the junction of the two
legs: with it the whole run is `hopen.trans heval`, and
`DescriptiveComplexity.Draw.Data.nexProg_wideAccept_of_legs` does the clock. -/
theorem config_openingEnd_eq_evalStart {F : LaidFile dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hmir : st.mir = fun _ => False)
    (p : P') (f : dt.CtlIx → A) (w : Univ A R' P' dt.KIx dt.dd → Prop) :
    (⟨Sum.inr (PR.stElt p f), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩ :
      Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A R' P' dt.KIx dt.dd))) =
      ⟨Sum.inr (PR.stElt p f), Sum.inl w,
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  rw [trackTape_ixBack_mir_empty_val hmir]

end Bridge

section Init

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}

variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

variable [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Lax822549.WideMachines.wide.Structure (Univ A R' P' dt.KIx dt.dd)] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **A tape walked along an empty track does not depend on which file presents
it**: the only cell-dependent part of the presentation is the bit at the walked
mark, and an empty mark has none. This is the bridge a program *handed* its file
needs, where `trackTape_blank_congr` is the one a program starting on a blank
tape needs: there the background is the blank, here it is the channel's own
marks, and neither is read by the presentation. -/
theorem trackTape_empty_congr {I' : Type}
    {cell : I → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {cell' : I' → (Univ A R' P' dt.KIx dt.dd → Prop)}
    {t : dt.SlotIx} {rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A} :
    PR.trackTapeAt cell t rest (fun _ => False) =
      PR.trackTapeAt cell' t rest (fun _ => False) := by
  classical
  refine funext fun r => ?_
  change PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf cell (fun _ => False) r) else rest r s) =
    PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf cell' (fun _ => False) r) else rest r s)
  refine congrArg _ (funext fun s => ?_)
  have hnone : ∀ {J : Type} (c : J → (Univ A R' P' dt.KIx dt.dd → Prop)),
      bitVal PR.zero PR.one (bitAtOf c (fun _ => False) r) = PR.zero := by
    intro J c
    exact bitVal_neg (fun hc => hc.choose_spec.2)
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, if_pos rfl, hnone, hnone]
  · rw [if_neg hs, if_neg hs]

end Init

/-! ### The opening, with the guess over the region -/

section Opening

variable {L : Language.{0, 0}} {dt : Data L} {A R' PE SE : Type}

variable {ShE : SE → Type}

variable [Fintype dt.CtlIx] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

variable [LinearOrder A] [LinearOrder R'] [Nonempty A] [Finite A] [Finite R']

variable [Finite dt.KIx]

variable [LinearOrder (NexPh (Option dt.KIx) PE)]

variable [Finite (NexPh (Option dt.KIx) PE)]

variable [Lax822549.WideMachines.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}

variable {coord : Fin dt.dd → dt.CtlIx} {f₀ : dt.CtlIx → A}

variable {ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE)}

variable {evalEntry : PE}

/-- **The background the opening's first step leaves**: the one it started from,
with the marker planted at the address the head is on. A clocked program starts
on a blank tape, so this – with `DescriptiveComplexity.Draw.Prog.initBack` for the
background – is what its opening runs from. -/
noncomputable def startBack
    (bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A)
    (one : A) (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A :=
  open Classical in
  fun r =>
    if r = v then Function.update (Function.update (bg r) Slot.wk one) Slot.bot one
    else bg r

omit [Fintype dt.CtlIx] [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R']
  [Nonempty A] [Finite A] [Finite R'] [Finite dt.KIx]
  [LinearOrder (NexPh (Option dt.KIx) PE)] [Finite (NexPh (Option dt.KIx) PE)]
  [Lax822549.WideMachines.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Planting the marker changes nothing elsewhere**: the frame condition of the
opening's first step. -/
theorem startBack_frame
    {bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {one : A} {v r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : r ≠ v) : dt.startBack bg one v r = bg r := by
  classical
  exact if_neg hr

omit [LinearOrder A] [LinearOrder R'] [Nonempty A] [Finite A] [Finite R']
  [Finite dt.KIx] [LinearOrder (NexPh (Option dt.KIx) PE)]
  [Finite (NexPh (Option dt.KIx) PE)]
  [Lax822549.WideMachines.wide.Structure (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]
  [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **Planting the two marks is the write the opening's first step makes**: at
the address the head is on, the presentation with them is the presentation
without them, updated at the marker slot and at the bottom mark's. -/
theorem startBack_wr
    {PR : Prog A R' (NexPh (Option dt.KIx) PE) dt.CtlIx dt.SlotIx dt.KIx dt.dd}
    {I : Type} (cell : I → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop))
    {bg : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    PR.passTracksAt cell Slot.mir (dt.startBack bg PR.one v) (fun _ => False) v =
      Function.update (Function.update
        (PR.passTracksAt cell Slot.mir bg (fun _ => False) v)
        Slot.wk PR.one) Slot.bot PR.one := by
  classical
  funext s
  have hbg : dt.startBack bg PR.one v v =
      Function.update (Function.update (bg v) Slot.wk PR.one) Slot.bot PR.one :=
    if_pos rfl
  by_cases hb : s = Slot.bot
  · subst hb
    rw [Function.update_self]
    change (if (Slot.bot : dt.SlotIx) = Slot.mir then _
      else dt.startBack bg PR.one v v Slot.bot) = PR.one
    rw [if_neg (by exact fun hc => nomatch hc), hbg, Function.update_self]
  · rw [Function.update_of_ne hb]
    by_cases hs : s = Slot.wk
    · subst hs
      rw [Function.update_self]
      change (if (Slot.wk : dt.SlotIx) = Slot.mir then _
        else dt.startBack bg PR.one v v Slot.wk) = PR.one
      rw [if_neg (by exact fun hc => nomatch hc), hbg,
        Function.update_of_ne (by exact fun hc => nomatch hc), Function.update_self]
    · rw [Function.update_of_ne hs]
      change (if s = (Slot.mir : dt.SlotIx) then _ else dt.startBack bg PR.one v v s) =
        if s = (Slot.mir : dt.SlotIx) then _ else bg v s
      by_cases hm : s = Slot.mir
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm, hbg, Function.update_of_ne hb,
          Function.update_of_ne hs]

/-! ### The state a clocked program starts in

Its first step plants the marker at the empty address and nothing else has been
written, so the state is clear but for the marker – and its background is the
blank tape everywhere off the file, which is what the opening's frame
hypotheses (`hbelow`, `habove`, `hwr`) ask of the caller. -/

variable (dt) in
/-- **The state a clocked program enters its opening in**: every register and
every track clear, the marker *and the bottom mark* at the address the head
stands on – the two the opening's first step writes, and the two the
evaluation's walks read. -/
noncomputable def nexEntrySt {I : Type}
    (v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    TapeSt dt A R' (NexPh (Option dt.KIx) PE) I where
  mir := fun _ => False
  tgt := fun _ => False
  sav := fun _ => False
  val := fun _ => False
  old := fun _ _ => False
  new := fun _ _ => False
  wk := fun r => r = v
  bot := fun r => r = v
  ltp := fun _ => False

/-! ### What the guess writes

The stage tracks a clocked program guesses are an assignment's, **restricted to
the stretch the guess sweeps** – the file's first register up to the end marker.
Restricting them is what makes the opening's frame condition true (outside that
stretch the tracks are the entry state's, which is empty), and it costs the
dictionary nothing, since every entry the evaluation reads is inside the stretch
(a track marks no empty address, `nonempty_of_trackOf`). -/

section Guessed

variable {L : Language.{0, 0}} {dt : Data L} {A R' PE : Type}

variable [LinearOrder A] [L.Structure A]

variable [Lax822549.WideMachines.wide.Structure
  (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)]

variable (dt) in
/-- **The tracks the guess writes**: an assignment's, inside the swept
stretch. -/
def guessTracks (zero one : A) (σ : dt.d.B.Assignment (dt.X.Map A))
    (bot top : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) :
    dt.d.B.ι → (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop :=
  fun iv r => trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ r ∧
    Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe bot r ∧ WMSetLt Lax822549.WideMachines.WMLe r top

/-- **Outside the swept stretch the guess writes nothing** – the opening's
`hout`, at tracks that are an assignment's inside it. -/
theorem not_guessTracks_out
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {bot top r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hr : WMSetLt Lax822549.WideMachines.WMLe r bot ∨ ¬WMSetLt Lax822549.WideMachines.WMLe r top) (iv : dt.d.B.ι) :
    ¬dt.guessTracks zero one σ bot top iv r := by
  rintro ⟨-, hlo, hhi⟩
  rcases hr with hr | hr
  · exact ((wmSetLt_iff _ _).mp hr).2
      ((isLinOrd_wmSetLe h).2.2.1 r bot ((wmSetLt_iff _ _).mp hr).1 hlo)
  · exact hr hhi

/-- **Below the guess's top the tracks are the assignment's, and nothing has to
be said about the bottom**: a track marks no empty address
(`nonempty_of_trackOf`), so an address it marks is at or above the marker's
neighbor by `wmSetLe_succ_bot_of_nonempty`, which is where the guess begins.
This is the `hdict` an evaluation asks for, and it asks of the *data* only what
`wmSetLt_ixStageTgt_logicalTop` already proves: that a dictionary address is
below the last logical one.

What it asks of the **reduction** is that every fixed-point variable have an
argument. A nullary one has the empty address for its entry, which is the
marker's own cell and below every stretch the machine writes; padding its
relation with a dummy argument costs nothing and is the intended reading. -/
theorem guessTracks_iff_of_lt
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {s₀ top s : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hs₀ : WMIncr Lax822549.WideMachines.WMLe (fun _ => False) s₀)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hhi : WMSetLt Lax822549.WideMachines.WMLe s top) (iv : dt.d.B.ι) :
    dt.guessTracks zero one σ s₀ top iv s ↔
      trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s :=
  ⟨fun hg => hg.1, fun hg =>
    ⟨hg, wmSetLe_succ_bot_of_nonempty h hs₀
      (nonempty_of_trackOf (dt.arOf_le_ko (some iv)) ⟨0, harity iv⟩ hg), hhi⟩⟩

/-- **The dictionary the evaluation reads, off a tape state**: the same reading
as `guessTracks_iff_of_lt`, at a state whose stage tracks are the guess's. Every
leg of the spine leaves them alone (`ixSpineStOfB_old`), so this is what the
evaluation's `hdict` is discharged by, at whatever program and whatever rule
names the reduction runs – nothing here mentions either. -/
theorem guessTracks_hdict_of_old {I : Type}
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {zero one : A} {σ : dt.d.B.Assignment (dt.X.Map A)}
    {s₀ top s : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    (hst : st.old = dt.guessTracks zero one σ s₀ top)
    (hs₀ : WMIncr Lax822549.WideMachines.WMLe (fun _ => False) s₀)
    (harity : ∀ iv : dt.d.B.ι, 0 < dt.d.B.arity iv)
    (hhi : WMSetLt Lax822549.WideMachines.WMLe s top) (iv : dt.d.B.ι) :
    st.old iv s ↔ trackOf dt.ly zero one (dt.arOf_le_ko (some iv)) σ s := by
  rw [hst]
  exact dt.guessTracks_iff_of_lt h hs₀ harity hhi iv

end Guessed

/-! ### The opening of a program that is handed its file

A program handed its file has nothing to lay: its file-laying phase is the two
steps of `nullSpec` and the rest of the opening is the same. So the whole
opening is stated here at an **arbitrary** file – the five steps of
`NexBuild`'s `AnyFile` section, the sweep that is over at once, the two walks
home and the guess, which was generic already. Nothing of the file is read but
its cells. -/

section Handed

variable {I : Type} {F : LaidFile dt A R' (NexPh (Option dt.KIx) PE) I}

variable {betaS : SweepSpec A dt.CtlIx dt.SlotIx (Option dt.KIx)}

variable {botS : Option dt.KIx}

omit [Nonempty A] in
/-- **The whole opening of a program that is handed its file**: plant the two
marks, walk up, run the sweep that lays nothing, turn round, walk home, guess
the certificate over the stretch, walk home again, and step into the
evaluation. Its cost is the two walks up and back, the guess's stretch out and
back, and six single steps. -/
theorem reachesIn_openingHanded (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    {v : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    {v₁ x y y' s₀ s₁ v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hvi₁ : WMIncr Lax822549.WideMachines.WMLe v v₁) (hwalk : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe v₁ x) (hxy : WMIncr Lax822549.WideMachines.WMLe x y)
    (hyy' : WMIncr Lax822549.WideMachines.WMLe y y') (hyv : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe v y)
    (hvs₀ : WMIncr Lax822549.WideMachines.WMLe v s₀) (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁) (hne₁ : ∃ z, s₁ z)
    (hvv' : WMIncr Lax822549.WideMachines.WMLe v v')
    {bg bg₀ : (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) →
      dt.SlotIx → A}
    (hframe : ∀ r, r ≠ v → bg₀ r = bg r)
    (hwr : PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v =
      Function.update (Function.update
        (PR.passTracksAt F.cell Slot.mir bg (fun _ => False) v) Slot.wk PR.one)
        Slot.bot PR.one)
    (hback : bg₀ = dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (f : dt.CtlIx → A)
    -- the sweep is over where it starts, and leaves nothing behind
    (hroll : betaS.Roll botS f) (hdone : betaS.Done botS f)
    (hstRoll : betaS.stRoll botS f (PR.passTracksAt F.cell Slot.mir bg₀
      (fun _ => False) y) = f)
    (hwrS : betaS.wr botS f (PR.passTracksAt F.cell Slot.mir bg₀
        (fun _ => False) y) =
      PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) y)
    -- the two exits, and the certificate the guess writes
    (hexB : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v))
    (σ : dt.d.B.ι →
      (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop) → Prop)
    (hout : ∀ (i : dt.d.B.ι)
        (r : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop),
      WMSetLt Lax822549.WideMachines.WMLe r s₀ ∨ ¬WMSetLt Lax822549.WideMachines.WMLe r s₁ → (σ i r ↔ st.old i r))
    (hexG : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
      (fun _ => False) v))
    {rEmbS : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrulesS : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          botS i ρ)
    {rHomeB rHomeG : HomeKit.HomeRule → R'}
    (hrulesHB : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeB ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeBuildP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ)
    (hrulesHG : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeG ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      ((wideRank x - wideRank v₁) + (wideRank y - wideRank v) +
        ((wideRank s₁ - wideRank s₀) + (wideRank s₁ - wideRank v)) + 7)
      ⟨Sum.inr (PR.stElt NexPh.start f), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir bg (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) (betaS.st0 f
          (PR.passTracksAt F.cell Slot.mir bg₀ (fun _ => False) v))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
          (fun _ => False)) (PR.syElt PR.blank)⟩ := by
  classical
  subst hback
  have hstart := dt.step_startAny (PR := PR) (cell := F.cell) (m := fun _ => False)
    (f := f) hrulesS hR h hvi₁ hframe hwr
  have hwalkR := dt.reachesIn_approachAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hwalk
  have henter := dt.step_approachEnterAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hxy
  have hsweep := dt.step_sweepDone (PR := PR) (cell := F.cell) (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hyy' hroll hdone hstRoll hwrS
  have hturn := dt.step_doneBackAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f) hrulesS hR h hyy'
  have hhome := HomeKit.reachesIn
    (κ := HomeKit.mk Slot.mir Slot.wk
      (NexPh.homeBuildP (B := Option dt.KIx) (PE := PE)))
    (rEmb := rHomeB) F.toIxFile hrulesHB hR h (fun hc => nomatch hc)
    (m := fun _ => False) (fc := f)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (fun r => by
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk = _
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hyv
  have hmid := dt.step_homeBuildExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hvs₀ hexB
  have hguess := reachesIn_guessRegionPhase (F := F) (m := fun _ => False)
    (f₀ := betaS.st0 f (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    (st := st) hrulesS hR h σ (fun i => by intro hc; exact nomatch hc)
    (by intro hc; exact nomatch hc) botS hwkS hle
    (wmSetLt_of_wmIncr_le h hvs₀ ((isLinOrd_wmSetLe h).1 _)) hne₁ hrulesHG hout
  have hexit := dt.step_homeGuessExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le { st with old := σ })
    (f := betaS.st0 f (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    hrulesS hR h hvv' hexG
  exact ((((((((TMData.reachesIn_of_step hstart).trans hwalkR).trans
    (TMData.reachesIn_of_step henter)).trans
    (TMData.reachesIn_of_step hsweep)).trans
    (TMData.reachesIn_of_step hturn)).trans hhome).trans
    (TMData.reachesIn_of_step hmid)).trans hguess).trans
    (TMData.reachesIn_of_step hexit) |>.mono (by omega)

omit [Nonempty A] [Finite (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)] in
/-- **The tail of the opening, from the walk home after the guess.** The whole
opening is a forward run, but a *backward* reading of an accepting run does not
get the opening: it gets the first configuration the machine cannot leave, which
is where the guess stopped and the walk home begins
(`DescriptiveComplexity.Draw.Data.exists_postGuess_shaped`). From there on the
run is forward again, and this is that piece: walk down to the marker from
wherever the guess stopped, and step into the evaluation.

Nothing of the guess is read here – the tracks are whatever the sweep left – so
the same lemma serves the forward opening's last two steps and the backward
reading's first. -/
theorem reachesIn_homeGuessTail (hR : PR.table.Reads)
    (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)))
    {st : TapeSt dt A R' (NexPh (Option dt.KIx) PE) I}
    {v y v' : Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd → Prop}
    (hwkS : st.wk = fun r => r = v)
    (hyv : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe v y) (hvv' : WMIncr Lax822549.WideMachines.WMLe v v')
    (f : dt.CtlIx → A)
    (hexG : dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False) v))
    {rEmbS : ∀ i : NexSite SE,
      NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i → R'}
    (hrulesS : ∀ (i : NexSite SE)
        (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i),
      PR.rules (rEmbS i ρ) =
        dt.nexRule PR.one betaS (dt.regionSpec PR.zero PR.one) ruleE evalEntry
          botS i ρ)
    {rHomeG : HomeKit.HomeRule → R'}
    (hrulesHG : ∀ ρ : HomeKit.HomeRule,
      PR.rules (rHomeG ρ) =
        (HomeKit.mk Slot.mir Slot.wk
          (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE))).rule PR.one ρ) :
    (Lax822549.WideMachines.wideData (Univ A R' (NexPh (Option dt.KIx) PE) dt.KIx dt.dd)).ReachesIn
      ((wideRank y - wideRank v) + 1)
      ⟨Sum.inr (PR.stElt NexPh.homeGuessP f), Sum.inl y,
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (NexPh.evalP evalEntry) f), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (fun _ => False))
          (PR.syElt PR.blank)⟩ := by
  have hhome := HomeKit.reachesIn
    (κ := HomeKit.mk Slot.mir Slot.wk
      (NexPh.homeGuessP (B := Option dt.KIx) (PE := PE)))
    (rEmb := rHomeG) F.toIxFile hrulesHG hR h (fun hc => nomatch hc)
    (m := fun _ => False) (fc := f)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
    (fun r => by
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk = _
      rw [show dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st r Slot.wk =
        bitVal PR.zero PR.one (st.wk r) from rfl, hwkS])
    hyv
  have hexit := dt.step_homeGuessExitAny (PR := PR) (cell := F.cell)
    (m := fun _ => False)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (f := f)
    hrulesS hR h hvv' hexG
  exact (hhome.tail hexit).mono (by omega)

end Handed

end Opening

section Clock

/-- **The clock comparison, with the opening at twice the region**: the shape a
program that lays a file *and* guesses over the region actually meets – its
opening is two sweeps, not a fraction of one. One working block is enough
(`1 ≤ k`), and the rest is `mul_add_lt_two_pow'`. -/
theorem nexTotal_lt_two_pow' {k j m o e a b : ℕ} (hk : 1 ≤ k) (hkj : k + 1 < j)
    (hm : 0 < m) (he : e ≤ a * b) (ha : a ≤ 2 ^ (k * m)) (hb : b ≤ 2 ^ (k * m))
    (hopen : o + 1 ≤ 2 ^ ((k + 1) * m)) :
    o + e + 1 < 2 ^ ((k + j) * m) := by
  have hsum : o + e + 1 ≤ a * b + (o + 1) := by omega
  exact lt_of_le_of_lt hsum (mul_add_lt_two_pow' hk hkj hm ha hb hopen)

end Clock

/-! ### The forward direction at the assembled program -/

section Accept

end Accept

/-! ### Determinism after the guess -/

section Unique

end Unique

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


