/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegFile
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
export Lax822549.WideMachines (WMDst WMLe WMRead WMRight WMSetLe WMSrc WMTr WMWrite wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Walking the register file

The phase a wide machine spends its life in. Its register file is one
recognizable cell per element of the instance (`DescriptiveComplexity.RegFile`),
and every register operation – read a bit, flip one, increment a mirror, compare
two – is the same walk:

> stand on the cell of `u`, write there, and scan right to the cell of the next
> element; repeat until the file is exhausted.

`DescriptiveComplexity.RegFile.reachesIn_regStep` is one such move and
`DescriptiveComplexity.RegFile.reachesIn_regWalk` is the whole traversal, the
latter being the only induction a program has to be given: the machine's state
and its tape are handed over *as functions of the element the pointer has
reached*, and what is discharged is a single move between an element and its
successor.

Both come in the other direction too
(`DescriptiveComplexity.RegFile.reachesIn_regStepBack`,
`DescriptiveComplexity.RegFile.reachesIn_regWalkBack`), and that reading is not a
convenience: the least significant digit of an address is the `WMLe`-**greatest**
element, so a program **incrementing its mirror** – clear the trailing digits, set
the first that is clear – walks the file from its last register towards its
first.

Getting *to* a register in the first place – the last one, to begin a downward
pass, and the first one, to come back from it – is
`DescriptiveComplexity.RegFile.reachesIn_toReg` and
`DescriptiveComplexity.RegFile.reachesIn_toRegBack`: one scan each, stopped by a
symbol the target register carries and the others do not. Only the two ends of
the file need such a symbol; in a file the input channel marks, those in between
are all the same one, and must be, since a symbol is an element and there are as
many registers as elements.

Two facts make a move between consecutive registers a single scan rather than a
search: consecutive elements have **no register between them**
(`DescriptiveComplexity.RegFile.gap`), so the scan cannot overshoot or stop
early; and the pointer lives in the machine's **control**, where a state may hold
an element of the instance, so no address arithmetic is involved in knowing which
register one is on.

## What a walk costs

Each statement comes in a budgeted form and an erased one. A move between
consecutive registers costs exactly the addresses lying between them, and a walk
of a stretch of the file costs the registers it crosses times whatever bound the
caller puts on one move. Which form a program uses is the whole difference
between the space-bounded wide problems and the clocked one: the file the input
channel marks is a geometric ruler in the top half of the tape, so walking it is
affordable only when nothing is counting.

Every statement is also given at `DescriptiveComplexity.wmSeg`, so that a program
written against the file of the input channel names no
`DescriptiveComplexity.RegFile` at all.

**What indexes the registers is a parameter.** Every proof here is about the
order the cells are laid out in and about nothing else, so each statement is
made at a `DescriptiveComplexity.IxFile` – a file over an arbitrary ordered
index – and the elementwise form is its diagonal
(`DescriptiveComplexity.RegFile.toIx`), one line each. The pointer is a function
of the index and the *states* stay elements of the instance, which is what makes
the generalization free: a walk never holds an index anywhere the machine can
see, only its caller does. Two linear orders separate in the general form – the
addresses' and the index's – and a statement that needs only one says so.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Walk

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-- **What a track shows at a cell**: its digit, if the cell is some element's
register; nothing at any other cell. A program's tape is a function of this and of
the address, and of nothing else about the track.

Stated at the *cells* rather than at a `DescriptiveComplexity.RegFile`, because a
program's tape is a **definition** and a file carries proofs: threading the whole
record through the definitions would make them depend on the linearity of the
order, which nothing about them does. The file appears in the theorems below,
where the proofs are wanted. -/
def bitAtOf {I : Type} (cell : I → (A → Prop)) (m : I → Prop) (r : A → Prop) : Prop :=
  ∃ u : I, r = cell u ∧ m u

omit [Lax822549.WideMachines.wide.Structure A] [Finite A] in
/-- **The coherence condition of the passes, discharged.** Two tracks agreeing
off one element show the same thing at every cell but that element's register –
whatever else the program keeps in its symbols, since they enter the tape only
through this.

A caller finishes with `congrArg`: its tape is some `g r (bitAtOf cell m r)`, and
this says the second argument does not move. -/
theorem bitAtOf_congr {I : Type} {cell : I → (A → Prop)} {m m' : I → Prop} {u : I}
    (hag : ∀ v : I, v ≠ u → (m v ↔ m' v)) {r : A → Prop} (hr : r ≠ cell u) :
    bitAtOf cell m r = bitAtOf cell m' r := by
  refine propext ⟨fun ⟨v, hv, hm⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, hm⟩ => ⟨v, hv, ?_⟩⟩
  · exact (hag v fun hc => hr (hc ▸ hv)).mp hm
  · exact (hag v fun hc => hr (hc ▸ hv)).mpr hm

namespace IxFile

variable {I : Type} [Finite I] {ile : I → I → Prop} (F : IxFile A I ile)

/-! ### One move of the walk -/

/-! ### The whole traversal -/

/-! ### Reaching a named register

Before a pass can start, and between one pass and the next, the head has to get
to a *particular* register – the last one to begin a downward pass, the first one
to come back from it, or the one a pointer in the control names. Each is a scan
whose stopping symbol is the name the register carries, and the two facts that
make it one scan are that the registers are ordered like their elements and that
a register's symbol names it. -/

/-! ### Walking the file the other way

The least significant digit of an address is the `WMLe`-**greatest** element
(`DescriptiveComplexity.Problems.Wide.Increment`), so a program incrementing its
mirror propagates the carry from the last register towards the first: the walk it
does is this one. -/

omit [Finite I] in
/-- **One move of a register walk, downwards.** In the state `q`, on the cell of
`u'`, the machine writes there and moves left; then it scans left over the cells
that are nobody's register and arrives on the cell of the element `u'`
succeeds. -/
theorem reachesIn_regStepBack (ha : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (h : Lax904597.Machines.IsLinOrd ile)
    {u u' : I} (hs : IxSucc ile u u')
    {q q' b : A} {f f' : (A → Prop) → A}
    (hwrite : ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (f (F.cell u')) ∧ Lax822549.WideMachines.WMDst τ q' ∧
      Lax822549.WideMachines.WMWrite τ (f' (F.cell u')) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ F.cell u' → f' r = f r)
    (hscan : ∀ r : A → Prop, (∃ x : I, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell x) r) → (∀ x : I, r ≠ F.cell x) →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q' ∧ Lax822549.WideMachines.WMRead τ (f' r) ∧ Lax822549.WideMachines.WMDst τ q' ∧ Lax822549.WideMachines.WMWrite τ (f' r) ∧
        ¬Lax822549.WideMachines.WMRight τ) :
    (Lax822549.WideMachines.wideData A).ReachesIn (wideRank (F.cell u') - wideRank (F.cell u))
      ⟨Sum.inr q, Sum.inl (F.cell u'), wideTape f b⟩
      ⟨Sum.inr q', Sum.inl (F.cell u), wideTape f' b⟩ := by
  have hlin := isLinOrd_wmSetLe ha
  have hlt : WMSetLt Lax822549.WideMachines.WMLe (F.cell u) (F.cell u') := F.strictMono u u' hs.1
  -- The cell of `u'` is not the first one, so the head can leave it downwards.
  obtain ⟨t, hi⟩ := exists_wmPred ha (s := F.cell u') (F.cell_nonempty u')
  -- The predecessor is at or above the cell the walk is going to.
  have hlb : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell u) t := (wmSetLt_iff_of_wmIncr ha hi (F.cell u)).mp hlt
  obtain ⟨τ, htr, hsrc, hread, hdst, hwr, hright⟩ := hwrite
  obtain ⟨t₀, ⟨x, rfl⟩, hle, hfirst, hrun⟩ :=
    reachesIn_scanBack_tape (b := b) (Stop := fun r => ∃ x : I, r = F.cell x) ha
      ⟨F.cell u, ⟨u, rfl⟩, hlb⟩ fun r hub hahead hstop =>
        hscan r (by obtain ⟨t, ⟨x, rfl⟩, hle⟩ := hahead; exact ⟨x, hle⟩)
          fun y hc => hstop ⟨y, hc⟩
  -- It stops at the cell of `u`: no register lies between the two.
  have hxu : F.cell x = F.cell u := by
    have hge : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell u) (F.cell x) := by
      rcases hlin.2.2.2 (F.cell x) (F.cell u) with hc | hc
      · rcases eq_or_ne (F.cell x) (F.cell u) with he | hne
        · exact he ▸ hlin.1 _
        · exact absurd ⟨u, rfl⟩ (hfirst (F.cell u) ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩) hlb)
      · exact hc
    rcases eq_or_ne (F.cell x) (F.cell u) with he | hne
    · exact he
    · refine absurd rfl (F.gap h hs ((wmSetLt_iff _ _).mpr ⟨hge, fun hc => hne hc.symm⟩)
        ((wmSetLt_iff _ _).mpr ⟨hlin.2.1 _ _ _ hle (wmSetLe_of_wmIncr hi), fun hc => ?_⟩) x)
      exact ne_of_wmIncr hi (hlin.2.2.1 _ _ (wmSetLe_of_wmIncr hi) (hc ▸ hle))
  -- The step off the cell of `u'` and the scan add up to the gap between the two.
  have hbud : wideRank t - wideRank (F.cell u) + 1 =
      wideRank (F.cell u') - wideRank (F.cell u) := by
    have h1 : wideRank (F.cell u') = wideRank t + 1 := wideRank_incr ha hi
    have h2 : wideRank (F.cell u) ≤ wideRank t := wideRank_mono ha hlb
    omega
  rw [← hbud]
  exact TMData.ReachesIn.head
    (step_wideTape_left ha hi htr hsrc hread hdst hwr hright hagree) (hxu ▸ hrun)

omit [Finite A] in
/-- **A register walk, downwards**: the mirror of
`DescriptiveComplexity.RegFile.reachesIn_regWalk`, from the top of a stretch of
the file to any element of it. This is the shape of a mirror increment – clear the
trailing digits, set the first that is clear – so it is the walk a program does
most. -/
theorem reachesIn_regWalkBack (h : Lax904597.Machines.IsLinOrd ile) {b : A} {st : I → A}
    {tp : I → (A → Prop) → A} {u₁ : I} {w : ℕ}
    (hmove : ∀ u u' : I, IxSucc ile u u' → ile u' u₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn w ⟨Sum.inr (st u'), Sum.inl (F.cell u'), wideTape (tp u') b⟩
        ⟨Sum.inr (st u), Sum.inl (F.cell u), wideTape (tp u) b⟩) :
    ∀ u : I, ile u u₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn ((ixRank ile u₁ - ixRank ile u) * w)
        ⟨Sum.inr (st u₁), Sum.inl (F.cell u₁), wideTape (tp u₁) b⟩
        ⟨Sum.inr (st u), Sum.inl (F.cell u), wideTape (tp u) b⟩ := by
  have key : ∀ k : ℕ, ∀ u : I, ixRank ile u₁ - ixRank ile u = k → ile u u₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn ((ixRank ile u₁ - ixRank ile u) * w)
        ⟨Sum.inr (st u₁), Sum.inl (F.cell u₁), wideTape (tp u₁) b⟩
        ⟨Sum.inr (st u), Sum.inl (F.cell u), wideTape (tp u) b⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hrank hle
      rcases eq_or_ne u u₁ with rfl | hne
      · rw [Nat.sub_self, Nat.zero_mul]
        exact TMData.reachesIn_refl
      · have hlt : WMLt ile u u₁ := ⟨hle, fun hc => hne (h.2.2.1 u u₁ hle hc)⟩
        obtain ⟨u', hsucc⟩ := exists_ixSucc ile h ⟨u₁, hlt⟩
        have hu' : ile u' u₁ := hsucc.2 u₁ hlt
        have h1 : ixRank ile u' = ixRank ile u + 1 := ixRank_succ ile h hsucc
        have h2 : ixRank ile u' ≤ ixRank ile u₁ := ixRank_le_of_le ile h hu'
        have hbud : (ixRank ile u₁ - ixRank ile u) * w =
            (ixRank ile u₁ - ixRank ile u') * w + w := by
          rw [show ixRank ile u₁ - ixRank ile u = ixRank ile u₁ - ixRank ile u' + 1 by omega,
            Nat.succ_mul]
        rw [hbud]
        exact (ih (ixRank ile u₁ - ixRank ile u') (by omega) u' rfl hu').trans
          (hmove u u' hsucc hu')
  exact fun u hle => key _ u rfl hle

/-! ### A track over the register file

The passes of `DescriptiveComplexity.Problems.Wide.Mirror` and
`DescriptiveComplexity.Problems.Wide.Test` take the tape as a function of *one
track*, `tapeOf m`, and each asks for the same coherence condition: changing the
track at one element changes the tape at that element's cell and nowhere else. A
program does not verify that by hand. It builds its tape by reading the track
through `DescriptiveComplexity.RegFile.bitAt` – the track's digit at a register
cell, nothing anywhere else – and
`DescriptiveComplexity.RegFile.bitAt_congr` is the condition, discharged once for
every program and every alphabet. -/

omit [Finite I] in
/-- What a track shows at a cell of a given file. -/
@[reducible] def bitAt (m : I → Prop) (r : A → Prop) : Prop := bitAtOf F.cell m r

omit [Finite A] [Finite I] in
@[simp]
theorem bitAt_cell (h : Lax904597.Machines.IsLinOrd ile) (m : I → Prop) (u : I) :
    F.bitAt m (F.cell u) ↔ m u := by
  constructor
  · rintro ⟨v, hv, hm⟩
    rwa [F.injective h hv]
  · exact fun hm => ⟨u, rfl, hm⟩

end IxFile

namespace RegFile

variable (F : RegFile A)

/-! ### One move of the walk -/

/-! ### The whole traversal -/

/-! ### Reaching a named register

Before a pass can start, and between one pass and the next, the head has to get
to a *particular* register – the last one to begin a downward pass, the first one
to come back from it, or the one a pointer in the control names. Each is a scan
whose stopping symbol is the name the register carries, and the two facts that
make it one scan are that the registers are ordered like their elements and that
a register's symbol names it. -/

/-! ### Walking the file the other way

The least significant digit of an address is the `WMLe`-**greatest** element
(`DescriptiveComplexity.Problems.Wide.Increment`), so a program incrementing its
mirror propagates the carry from the last register towards the first: the walk it
does is this one. -/

/-! ### A track over the register file

The passes of `DescriptiveComplexity.Problems.Wide.Mirror` and
`DescriptiveComplexity.Problems.Wide.Test` take the tape as a function of *one
track*, `tapeOf m`, and each asks for the same coherence condition: changing the
track at one element changes the tape at that element's cell and nowhere else. A
program does not verify that by hand. It builds its tape by reading the track
through `DescriptiveComplexity.RegFile.bitAt` – the track's digit at a register
cell, nothing anywhere else – and
`DescriptiveComplexity.RegFile.bitAt_congr` is the condition, discharged once for
every program and every alphabet. -/

/-- What a track shows at a cell of a given file. -/
@[reducible] def bitAt (m : A → Prop) (r : A → Prop) : Prop := F.toIx.bitAt m r

omit [Finite A] in
@[simp]
theorem bitAt_cell (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (m : A → Prop) (u : A) :
    F.bitAt m (F.cell u) ↔ m u :=
  F.toIx.bitAt_cell h m u

end RegFile

/-! ### The same, at the file the input channel marks

Every statement above, read at `DescriptiveComplexity.wmSegFile`: this is the
register file a space-bounded program uses, and these are the names its phases
cite. -/

/-- **What a track shows at a cell** of the file the input channel marks. -/
def regBit (m : A → Prop) (r : A → Prop) : Prop := bitAtOf wmSeg m r

@[simp]
theorem regBit_wmSeg (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) (m : A → Prop) (u : A) :
    regBit m (wmSeg u) ↔ m u :=
  (wmSegFile h).bitAt_cell h m u

/-! ### The accumulator of a downward pass

A pass down the register file carries one bit of information in its control:
whether everything it has seen so far behaved. Since it walks downwards, “so far”
is “at every register above the one it is on”, and the two states of the pass are
therefore a *function of the suffix*. Both subroutines built on the walk – the
mirror increment (`DescriptiveComplexity.Problems.Wide.Mirror`) and the file
tests (`DescriptiveComplexity.Problems.Wide.Test`) – are that shape, so it is
settled here. -/

open Classical in
/-- **The state a downward pass is in on arriving at the register of `w`**: the
first state exactly when the property holds at every register strictly above. -/
noncomputable def accState {I : Type} (ile : I → I → Prop) (P : I → Prop) (qy qn : A)
    (w : I) : A :=
  if ∀ v : I, WMLt ile w v → P v then qy else qn

open Classical in
/-- **The state a downward pass is in on leaving the register of `w`**: the same
with `w` itself taken into account. -/
noncomputable def accStateAfter {I : Type} (ile : I → I → Prop) (P : I → Prop) (qy qn : A)
    (w : I) : A :=
  if ∀ v : I, ile w v → P v then qy else qn

variable {I : Type} {ile : I → I → Prop} {P : I → Prop} {qy qn : A}

omit [Finite A] [Lax822549.WideMachines.wide.Structure A] in
/-- **Leaving one register is arriving at the next one down.** -/
theorem accStateAfter_succ (h : Lax904597.Machines.IsLinOrd ile) {u u' : I} (hs : IxSucc ile u u') :
    accStateAfter ile P qy qn u' = accState ile P qy qn u := by
  have hiff : (∀ v : I, ile u' v → P v) ↔ ∀ v : I, WMLt ile u v → P v :=
    ⟨fun hall v hlt => hall v (hs.2 v hlt),
      fun hall v hle => hall v ⟨h.2.1 u u' v hs.1.1 hle, fun hc => hs.1.2 (h.2.1 u' v u hle hc)⟩⟩
  unfold accStateAfter accState
  by_cases hc : ∀ v : I, WMLt ile u v → P v
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

omit [Finite A] [Lax822549.WideMachines.wide.Structure A] in
/-- **At the last register nothing has been seen yet**, so the pass starts in the
first state. -/
theorem accState_top {top : I} (htop : ∀ v : I, ile v top) : accState ile P qy qn top = qy :=
  if_pos fun v hlt => absurd (htop v) hlt.2

omit [Finite A] [Lax822549.WideMachines.wide.Structure A] in
/-- A pass is in one of its two states, whatever it has seen. -/
theorem accState_cases (w : I) : accState ile P qy qn w = qy ∨ accState ile P qy qn w = qn := by
  unfold accState
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Finite A] [Lax822549.WideMachines.wide.Structure A] in
/-- **A pass that saw a failure ends in the second state.** -/
theorem accStateAfter_bot_neg {bot : I} (hbot : ∀ v : I, ile bot v) {u : I} (hu : ¬P u) :
    accStateAfter ile P qy qn bot = qn :=
  if_neg fun hall => hu (hall u (hbot u))

omit [Finite A] [Lax822549.WideMachines.wide.Structure A] in
/-- **A pass that saw no failure ends in the first state.** -/
theorem accStateAfter_bot_pos {bot : I} (hall : ∀ u : I, P u) :
    accStateAfter ile P qy qn bot = qy :=
  if_pos fun v _ => hall v

end Walk

end Lax822549Proofs.DescriptiveComplexity


