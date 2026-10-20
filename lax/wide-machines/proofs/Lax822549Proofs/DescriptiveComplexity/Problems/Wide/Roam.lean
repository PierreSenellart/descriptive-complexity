/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Step
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMLe WMRead WMRight WMSetLe WMSrc WMStart WMTr WMWrite WPoint wideData wpMark)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax799700.Common (bitRank)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# Roaming: what a wide machine may do between its phases

`DescriptiveComplexity.WideAcceptSpace` and
`DescriptiveComplexity.DWideAcceptSpace` put no bound on the length of a run:
acceptance is `Relation.ReflTransGen` of the step relation, with no count
anywhere. So their programs may **roam** – sweep up, sweep back down, and start
again, as often as they like. `DescriptiveComplexity.WideAccept` counts its steps
against the number of addresses, so its programs roam on a budget: as many phases
as they like, provided the lengths add up to less than the number of addresses.

That is a different, and much larger, programming model than a single sweep, and
this file is its interface. Every phase is stated **twice** – once with a budget
(`DescriptiveComplexity.TMData.ReachesIn`, which composes by adding) and once
without (`Relation.ReflTransGen`, its erasure) – so that the clocked and the
space-bounded programs share their phases and differ only in whether the sum is
taken:

* a phase sweeping up a stretch of addresses –
  `DescriptiveComplexity.reachesIn_of_wideUp`, erased as
  `DescriptiveComplexity.reaches_of_wideUp`;
* a phase sweeping back down one –
  `DescriptiveComplexity.reachesIn_of_wideDown`, erased as
  `DescriptiveComplexity.reaches_of_wideDown`;
* a phase running a whole subroutine per address –
  `DescriptiveComplexity.reachesIn_of_wideRounds`, erased as
  `DescriptiveComplexity.reaches_of_wideRounds`;
* a run that ends accepting – `DescriptiveComplexity.accepts_of_wideRoam`, erased
  as `DescriptiveComplexity.acceptsSpace_of_wideRoam`.

The third is the one an outer loop is written with, and the one whose two
readings differ most: the budgeted form charges a round `w` steps and the whole
phase the product of `w` with the number of addresses crossed, while the erased
form charges nothing, which is what lets a space-bounded program iterate a fixed
point through exponentially many stages.

On top of them sits the primitive a roaming program actually spends its time
on – the **scan**, `DescriptiveComplexity.reaches_scanRight` and
`DescriptiveComplexity.reaches_scanLeft`: hold the state, rewrite every symbol
by itself, and walk until the cell where the scanning transition is no longer
offered. A scan leaves the tape exactly as it found it, which is why its
statement mentions one tape and not two, and it is how a program that cannot
read the digits of its own address nevertheless finds its way back to a cell it
has marked.

A program does not know *which* cell will stop its scan, only that one will, so
the form it uses is `DescriptiveComplexity.reaches_scanRight_least` (and
`DescriptiveComplexity.reaches_scanLeft_greatest`): the machine arrives at the
first stopping cell and learns, on arrival, that nothing it passed was one. The
extremum is taken there, once, so no phase of a program has to name the address
a mark sits at.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Roam

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] [Finite A]

/-! ### The rank of an address

Every phase below is stated twice: once with a budget
(`DescriptiveComplexity.TMData.ReachesIn`), which is what a clocked program needs,
and once without (`Relation.ReflTransGen`), which is the erasure a space-bounded
one uses. The budgets are all differences of *ranks*: the number of addresses
strictly below a given one, which is exactly the number of steps a machine
stepping once per increment spends reaching it from the empty address. -/

/-- **The rank of an address**: how many addresses lie strictly below it. -/
noncomputable def wideRank (s : A → Prop) : ℕ :=
  Lax799700.Common.bitRank (Lax822549.WideMachines.wideData A).Le (Lax822549.WideMachines.wideData A).Posn (Sum.inl s : Lax822549.WideMachines.WPoint A)

/-- The empty address has rank zero: a program starts with nothing spent. -/
theorem wideRank_bot (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) : wideRank (fun _ : A => False) = 0 :=
  bitRank_eq_zero_of_minPos (isLinOrd_wpLe h) (minPos_wpLe h)

/-- Rank increases by one along an increment, which is what makes a difference of
ranks a step count. -/
theorem wideRank_incr (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop} (hi : WMIncr Lax822549.WideMachines.WMLe s t) :
    wideRank t = wideRank s + 1 :=
  bitRank_succPos (isLinOrd_wpLe h) ((succPos_wpLe_iff h s t).mpr hi)

/-- Rank is monotone along the address order: a budget stated at one address
covers every address below it, which is how a phase whose stopping cell is
unknown is charged against a known ceiling. -/
theorem wideRank_mono (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {s t : A → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t) :
    wideRank s ≤ wideRank t :=
  TMData.bitRank_le_of_le (M := Lax822549.WideMachines.wideData A) (isLinOrd_wpLe h) trivial hle

/-- **Rank is below the clock**: the machine's step bound counts the addresses,
so a program that sweeps the whole tape once is affordable and the arithmetic
never leaves `ℕ`. -/
theorem wideRank_lt_card (s : A → Prop) :
    wideRank s < Nat.card {p : Lax822549.WideMachines.WPoint A // (Lax822549.WideMachines.wideData A).Posn p} :=
  bitRank_lt_card (p := (Sum.inl s : Lax822549.WideMachines.WPoint A)) trivial

/-- **The addresses are the subsets of the instance.** -/
def wideAddrEquiv : {p : Lax822549.WideMachines.WPoint A // (Lax822549.WideMachines.wideData A).Posn p} ≃ (A → Prop) where
  toFun p :=
    match p with
    | ⟨Sum.inl s, _⟩ => s
    | ⟨Sum.inr _, h⟩ => False.elim h
  invFun s := ⟨Sum.inl s, trivial⟩
  left_inv := by
    rintro ⟨s | x, h⟩
    · rfl
    · exact False.elim h
  right_inv _ := rfl

/-- **The clock of a wide machine is `2 ^ n`.** The whole arithmetic of the
model: a reduction buys itself `2 ^ (|Tag| · nᵈ)` steps by choosing the tags and
the dimension of its interpretation, and nothing else it does changes the
figure. -/
theorem card_wideAddr :
    Nat.card {p : Lax822549.WideMachines.WPoint A // (Lax822549.WideMachines.wideData A).Posn p} = 2 ^ Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_congr wideAddrEquiv]
  simp [Nat.card_eq_fintype_card]

/-! ### The size of a region

A clocked program keeps its data in the least significant blocks, so every
address it visits is empty above a fixed set of positions. Such a *region* is
much smaller than the tape, and the budget of every phase run inside it has to
be charged against the region and not against the number of addresses – a bound
by `card_wideAddr` is a bound by the clock itself, which proves nothing. The two
lemmas here are what charges it: the addresses supported on a set of positions
are that set's subsets, so an address supported there has rank below `2 ^` its
size. -/

omit [Lax822549.WideMachines.wide.Structure A] in
/-- **The addresses supported on a set of positions are its subsets.** -/
theorem card_addr_supported (Q : A → Prop) :
    Nat.card {s : A → Prop // ∀ x, s x → Q x} = 2 ^ Nat.card {x : A // Q x} := by
  classical
  have := Fintype.ofFinite A
  have e : {s : A → Prop // ∀ x, s x → Q x} ≃ ({x : A // Q x} → Prop) :=
    { toFun := fun s x => s.1 x.1
      invFun := fun f => ⟨fun x => ∃ h : Q x, f ⟨x, h⟩, fun _ hx => hx.1⟩
      left_inv := by
        rintro ⟨t, ht⟩
        exact Subtype.ext (funext fun x =>
          propext ⟨fun hx => hx.2, fun hx => ⟨ht x hx, hx⟩⟩)
      right_inv := by
        intro f
        funext x
        refine propext ⟨fun hx => ?_, fun hx => ⟨x.2, ?_⟩⟩
        · have hxx : (⟨x.1, hx.1⟩ : {x : A // Q x}) = x := Subtype.ext rfl
          exact hxx ▸ hx.2
        · have hxx : (⟨x.1, x.2⟩ : {x : A // Q x}) = x := Subtype.ext rfl
          exact hxx ▸ hx }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

/-- **An address of a region has rank below the region's size**: if every
address at or below `s` is empty off `Q`, then fewer than `2 ^ #Q` addresses lie
below `s`, since they are distinct subsets of `Q` and `s` is one more. This is
the bound a clocked phase is charged against. -/
theorem wideRank_lt_two_pow_supported (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {Q s : A → Prop}
    (hclosed : ∀ t : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s → ∀ x, t x → Q x) :
    wideRank s < 2 ^ Nat.card {x : A // Q x} := by
  classical
  -- The addresses strictly below `s`, and those supported on `Q`.
  have himg : {q : Lax822549.WideMachines.WPoint A | (Lax822549.WideMachines.wideData A).Posn q ∧ (Lax822549.WideMachines.wideData A).Le q (Sum.inl s) ∧
      q ≠ Sum.inl s} = Sum.inl '' {t : A → Prop | Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s ∧ t ≠ s} := by
    ext q
    rcases q with t | x
    · exact ⟨fun hq => ⟨t, ⟨hq.2.1, fun hc => hq.2.2 (by rw [hc])⟩, rfl⟩,
        fun ⟨t', ht', he⟩ => by
          cases he
          exact ⟨trivial, ht'.1, fun hc => ht'.2 (Sum.inl_injective hc)⟩⟩
    · exact ⟨fun hq => hq.1.elim, fun ⟨_, _, he⟩ => nomatch he⟩
  have hlt : ({t : A → Prop | Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s ∧ t ≠ s} : Set (A → Prop)).ncard <
      ({t : A → Prop | ∀ x, t x → Q x} : Set (A → Prop)).ncard := by
    refine Set.ncard_lt_ncard ⟨fun t ht => hclosed t ht.1, fun hsub => ?_⟩ (Set.toFinite _)
    exact (hsub (hclosed s ((isLinOrd_wmSetLe h).1 s))).2 rfl
  have hcard : ({t : A → Prop | ∀ x, t x → Q x} : Set (A → Prop)).ncard =
      2 ^ Nat.card {x : A // Q x} := by
    rw [← Nat.card_coe_set_eq]
    exact card_addr_supported Q
  rw [wideRank, Lax799700.Common.bitRank, himg, Set.ncard_image_of_injective _ Sum.inl_injective]
  omega

/-- A family of configurations indexed by the addresses, read on the whole
universe of the machine. Off the addresses the value is irrelevant – a phase
never looks – so it repeats the one at the empty address. -/
def wideLift (conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)) : Lax822549.WideMachines.WPoint A → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)
  | Sum.inl s => conf s
  | Sum.inr _ => conf fun _ => False

omit [Lax822549.WideMachines.wide.Structure A] [Finite A] in
@[simp]
theorem wideLift_addr (conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)) (s : A → Prop) :
    wideLift conf (Sum.inl s) = conf s :=
  rfl

/-! ### The two directions of a phase -/

/-- **A phase sweeping up.** Give the intended configuration at each address of
a stretch and one step between each address of it and its increment; the machine
then runs from the bottom of the stretch to the top.

This is `DescriptiveComplexity.stepsIn_of_wideSweep` with the count relaxed to a
budget and the stretch bounded at both ends: a roaming program's phases stop
where the next one begins, and the transitions carrying them need not exist
beyond. -/
theorem reachesIn_of_wideUp (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    {conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)} {s₀ s₁ : A → Prop}
    (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr Lax822549.WideMachines.WMLe s t → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s₁ →
      (Lax822549.WideMachines.wideData A).Step (conf s) (conf t)) :
    (Lax822549.WideMachines.wideData A).ReachesIn (wideRank s₁ - wideRank s₀) (conf s₀) (conf s₁) := by
  have hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment (M := Lax822549.WideMachines.wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : Lax822549.WideMachines.WPoint A)) (p₁ := (Sum.inl s₁ : Lax822549.WideMachines.WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₁) trivial hle (hlin.1 _)
  · exact hrun.reachesIn
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-- **A phase sweeping back down.** The mirror of
`DescriptiveComplexity.reachesIn_of_wideUp`: each address of the stretch carries a
step *from* its increment, and the machine runs from the top of the stretch to
the bottom, for the same price. -/
theorem reachesIn_of_wideDown (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    {conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)} {s₀ s₁ : A → Prop}
    (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s₁)
    (hstep : ∀ s t : A → Prop, WMIncr Lax822549.WideMachines.WMLe s t → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s₁ →
      (Lax822549.WideMachines.wideData A).Step (conf t) (conf s)) :
    (Lax822549.WideMachines.wideData A).ReachesIn (wideRank s₁ - wideRank s₀) (conf s₁) (conf s₀) := by
  have hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.wideData A).Le := isLinOrd_wpLe h
  have hrun := TMData.stepsIn_of_segment_down (M := Lax822549.WideMachines.wideData A) hlin (conf := wideLift conf)
    (p₀ := (Sum.inl s₀ : Lax822549.WideMachines.WPoint A)) (p₁ := (Sum.inl s₁ : Lax822549.WideMachines.WPoint A)) trivial
    (fun p q hsucc _ hub => ?_) (Sum.inl s₀) trivial (hlin.1 _) hle
  · exact hrun.reachesIn
  · obtain ⟨s, t, rfl, rfl, hi⟩ := step_ends_wide h hsucc
    exact hstep s t hi (by assumption) hub

/-! ### A phase that does work at every address

`DescriptiveComplexity.reaches_of_wideUp` asks for **one** step per address,
which is all a scan needs and all a machine on a clock can afford. A roaming
program's outer loops are not like that: at each address it runs a whole
subroutine – walk to the register file, increment the mirror, walk back – and
only then moves on. So the round, not the step, is the unit. -/

/-- **A phase that runs a subroutine at every address.** Give the intended
configuration at each address of a stretch and, between each address and its
increment, a *run* of at most `w` steps rather than a single step; the machine
then gets from the bottom of the stretch to the top, and pays `w` for each
address it crossed.

This is the shape of every outer loop of a wide program – seeking an address,
sweeping a stage of a fixed-point iteration, comparing two tracks of the tape –
and the product is what a clock reads: a program is affordable when the rounds it
runs, times the width of one, stays below the number of addresses. A space-bounded
program ignores the product (`DescriptiveComplexity.reaches_of_wideRounds`), which
is what lets it iterate a fixed point. -/
theorem reachesIn_of_wideRounds (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    {conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)} {s₀ s₁ : A → Prop} {w : ℕ}
    (hround : ∀ s t : A → Prop, WMIncr Lax822549.WideMachines.WMLe s t → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn w (conf s) (conf t)) :
    ∀ s : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn ((wideRank s - wideRank s₀) * w) (conf s₀) (conf s) := by
  have hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop, wideRank s = k →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ →
      (Lax822549.WideMachines.wideData A).ReachesIn ((wideRank s - wideRank s₀) * w) (conf s₀) (conf s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · rw [Nat.sub_self, Nat.zero_mul]
        exact TMData.reachesIn_refl
      · -- Above the bottom of the stretch, so not the empty address: it has a predecessor.
        have hlt : WMSetLt Lax822549.WideMachines.WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : wideRank s = wideRank p + 1 := wideRank_incr h hp
        have hlow : wideRank s₀ ≤ wideRank p := wideRank_mono h hpl
        have heq : (wideRank s - wideRank s₀) * w =
            (wideRank p - wideRank s₀) * w + w := by
          rw [show wideRank s - wideRank s₀ = (wideRank p - wideRank s₀) + 1 by omega,
            Nat.succ_mul]
        rw [heq]
        exact (ih _ (by omega) p rfl hpl hpu).trans (hround p s hp hpl hub)
  exact fun s hlb hub => key _ s rfl hlb hub

/-- **A phase that runs a subroutine at every address**, the budget forgotten:
each round is a run of any length whatever, which is what only a space-bounded
program can afford. -/
theorem reaches_of_wideRounds (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    {conf : (A → Prop) → Lax904597.Machines.Config (Lax822549.WideMachines.WPoint A)} {s₀ s₁ : A → Prop}
    (hround : ∀ s t : A → Prop, WMIncr Lax822549.WideMachines.WMLe s t → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s₁ →
      Relation.ReflTransGen (Lax822549.WideMachines.wideData A).Step (conf s) (conf t)) :
    ∀ s : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ →
      Relation.ReflTransGen (Lax822549.WideMachines.wideData A).Step (conf s₀) (conf s) := by
  have hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop, wideRank s = k →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ →
      Relation.ReflTransGen (Lax822549.WideMachines.wideData A).Step (conf s₀) (conf s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · exact Relation.ReflTransGen.refl
      · have hlt : WMSetLt Lax822549.WideMachines.WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : wideRank s = wideRank p + 1 := wideRank_incr h hp
        exact (ih _ (by omega) p rfl hpl hpu).trans (hround p s hp hpl hub)
  exact fun s hlb hub => key _ s rfl hlb hub

/-- **What a sweep leaves behind, address by address.** The semantic twin of
`DescriptiveComplexity.reaches_of_wideRounds`, at the same measure and the same
stretch: a property of the addresses that holds at the bottom and is carried
across each increment holds everywhere the sweep has been.

`reaches_of_wideRounds` says the machine *gets* to every address of the stretch;
this says what is *true* when it does – the two are used together, the run
theorem consuming the round's machine hypothesis and this one the round's tape
hypothesis. -/
theorem holds_of_wideRounds (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    {Q : (A → Prop) → Prop} {s₀ s₁ : A → Prop} (hbase : Q s₀)
    (hround : ∀ s t : A → Prop, WMIncr Lax822549.WideMachines.WMLe s t → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s₁ → Q s → Q t) :
    ∀ s : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ → Q s := by
  have hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.wideData A).Le := isLinOrd_wpLe h
  have hset := isLinOrd_wmSetLe h
  have key : ∀ k : ℕ, ∀ s : A → Prop,
      Lax799700.Common.bitRank (Lax822549.WideMachines.wideData A).Le (Lax822549.WideMachines.wideData A).Posn (Sum.inl s : Lax822549.WideMachines.WPoint A) = k →
      Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ s → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s s₁ → Q s := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hrank hlb hub
      rcases eq_or_ne s₀ s with rfl | hne
      · exact hbase
      · -- above the bottom of the stretch, so not the empty address
        have hlt : WMSetLt Lax822549.WideMachines.WMLe s₀ s := (wmSetLt_iff _ _).mpr ⟨hlb, hne⟩
        have hsome : ∃ x, s x := by
          by_contra hc
          exact hne (hset.2.2.1 s₀ s hlb
            (wmSetLe_of_empty h (fun x hx => hc ⟨x, hx⟩) s₀))
        obtain ⟨p, hp⟩ := exists_wmPred h hsome
        have hpl : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s₀ p := (wmSetLt_iff_of_wmIncr h hp s₀).mp hlt
        have hpu : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe p s₁ := hset.2.1 p s s₁ (wmSetLe_of_wmIncr hp) hub
        have hb : Lax799700.Common.bitRank (Lax822549.WideMachines.wideData A).Le (Lax822549.WideMachines.wideData A).Posn (Sum.inl s : Lax822549.WideMachines.WPoint A) =
            Lax799700.Common.bitRank (Lax822549.WideMachines.wideData A).Le (Lax822549.WideMachines.wideData A).Posn (Sum.inl p : Lax822549.WideMachines.WPoint A) + 1 :=
          bitRank_succPos hlin ((succPos_wpLe_iff h p s).mpr hp)
        exact hround p s hp hpl hub (ih _ (by omega) p rfl hpl hpu)
  exact fun s hlb hub => key _ s rfl hlb hub

/-! ### The accumulator of a sweep

A sweep that is asking a question of every address – *do these two tracks agree
everywhere?* – carries one bit across exponentially many rounds, and since it
sweeps *upwards* that bit is a function of the **prefix**: of the addresses
strictly below the one it has reached. This is the address-scale twin of
`DescriptiveComplexity.accState`, which does the same for a walk of the register
file, and it is what the comparison sweep of a fixed-point program is written
with. -/

open Classical in
/-- **The state a sweep is in on arriving at an address**: the first state exactly
when the property holds at every address strictly below. -/
noncomputable def sweepState (P : (A → Prop) → Prop) (qy qn : A) (w : A → Prop) : A :=
  if ∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe r w → P r then qy else qn

open Classical in
/-- **The state a sweep is in on leaving an address**: the same with that address
taken into account. -/
noncomputable def sweepStateAfter (P : (A → Prop) → Prop) (qy qn : A) (w : A → Prop) : A :=
  if ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r w → P r then qy else qn

variable {P : (A → Prop) → Prop} {qy qn : A}

/-- **Leaving one address is arriving at the next**, which is what makes the two
definitions one accumulator. -/
theorem sweepStateAfter_succ (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {w w' : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe w w') : sweepStateAfter P qy qn w = sweepState P qy qn w' := by
  have hiff : (∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r w → P r) ↔
      ∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe r w' → P r :=
    ⟨fun hall r hlt => hall r ((wmSetLt_iff_of_wmIncr h hi r).mp hlt),
      fun hall r hle => hall r ((wmSetLt_iff_of_wmIncr h hi r).mpr hle)⟩
  unfold sweepStateAfter sweepState
  by_cases hc : ∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe r w' → P r
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

omit [Finite A] in
/-- **A sweep that saw no failure ends in the first state.** -/
theorem sweepStateAfter_pos {w : A → Prop} (hall : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r w → P r) :
    sweepStateAfter P qy qn w = qy :=
  if_pos hall

omit [Finite A] in
/-- **A sweep that saw a failure ends in the second state.** -/
theorem sweepStateAfter_neg {w r : A → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r w) (hP : ¬P r) :
    sweepStateAfter P qy qn w = qn :=
  if_neg fun hall => hP (hall r hle)

/-! ### The scan -/

/-- An address whose increment is at or below a bound is strictly below it: the
side condition a rightward scan step needs. -/
theorem wmSetLt_of_wmIncr_le (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {r r' t : A → Prop}
    (hi : WMIncr Lax822549.WideMachines.WMLe r r') (hub : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r' t) : WMSetLt Lax822549.WideMachines.WMLe r t := by
  have hlin := isLinOrd_wmSetLe h
  refine (wmSetLt_iff r t).mpr ⟨hlin.2.1 r r' t (wmSetLe_of_wmIncr hi) hub, fun hc => ?_⟩
  exact ne_of_wmIncr hi (hlin.2.2.1 r r' (wmSetLe_of_wmIncr hi) (hc ▸ hub))

/-- An address at or below one whose increment is taken is strictly below that
increment: the side condition a leftward scan step needs. -/
theorem wmSetLt_of_le_wmIncr (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {t r r' : A → Prop}
    (hlb : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t r) (hi : WMIncr Lax822549.WideMachines.WMLe r r') : WMSetLt Lax822549.WideMachines.WMLe t r' := by
  have hlin := isLinOrd_wmSetLe h
  refine (wmSetLt_iff t r').mpr ⟨hlin.2.1 t r r' hlb (wmSetLe_of_wmIncr hi), fun hc => ?_⟩
  exact ne_of_wmIncr hi (hlin.2.2.1 r r' (wmSetLe_of_wmIncr hi) (hc ▸ hlb))

/-- **Scanning right.** In a fixed state, at every cell from `s` up to but not
including `t`, some transition of the instance rewrites the symbol by itself and
moves right; the machine then walks from `s` to `t`, leaving state and tape as it
found them.

This is how a program navigates: it cannot read the digits of the address it is
on, so it writes a marker in the cell it means to come back to and scans until
the scanning transition is withheld – at the marker, which is the only symbol the
hypothesis is not asked about. -/
theorem reachesIn_scanRight (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q : A}
    {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A} {s t : A → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t)
    (hstep : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r → WMSetLt Lax822549.WideMachines.WMLe r t →
      ∃ τ a : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ a ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ a ∧ Lax822549.WideMachines.WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    (Lax822549.WideMachines.wideData A).ReachesIn (wideRank t - wideRank s)
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reachesIn_of_wideUp (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r hlb (wmSetLt_of_wmIncr_le h hi hub)
      exact step_wide_right h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-- **Scanning left**, the same reading downwards: the transitions move left, and
the machine walks from `s` down to `t`. -/
theorem reachesIn_scanLeft (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q : A}
    {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A} {s t : A → Prop} (hle : Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s)
    (hstep : ∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe t r → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s →
      ∃ τ a : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ a ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ a ∧ ¬Lax822549.WideMachines.WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    (Lax822549.WideMachines.wideData A).ReachesIn (wideRank s - wideRank t)
      ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ :=
  reachesIn_of_wideDown (conf := fun r => ⟨Sum.inr q, Sum.inl r, tp⟩) h hle
    fun r r' hi hlb hub => by
      obtain ⟨τ, a, htr, hsrc, hread, hdst, hwrite, hright, hcur⟩ :=
        hstep r' (wmSetLt_of_le_wmIncr h hlb hi) hub
      exact step_wide_left h hi htr hsrc hread hdst hwrite hright hcur hcur fun _ _ => rfl

/-! ### Scanning to the first cell that stops the scan

The form a program uses in practice: it does not know *which* cell will stop its
scan, only that some cell will, and it needs the arrival to come with the promise
that nothing before it stopped. -/

/-- **A rightward scan arrives at the first cell that stops it.** Given that some
cell at or above `s` stops the scan, and that every cell at or above `s` which
does not stop it offers the scanning transition, the machine reaches the *least*
stopping cell – and learns, on arrival, that no cell it passed was one.

The caller never constructs that cell: this is where the extremum is taken, once,
so a program's phases are stated about the marks they look for and not about the
addresses those marks sit at. The budget is stated at the cell reached, and a
caller that knows a ceiling for its marks charges the scan against that ceiling
by `DescriptiveComplexity.wideRank_mono` and
`DescriptiveComplexity.TMData.ReachesIn.mono`. -/
theorem reachesIn_scanRight_least (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q : A}
    {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t)
    (hstep : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r →
      (∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r t) → ¬Stop r →
      ∃ τ a : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ a ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ a ∧ Lax822549.WideMachines.WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t ∧
      (∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r → WMSetLt Lax822549.WideMachines.WMLe r t → ¬Stop r) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn (wideRank t - wideRank s)
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hge⟩, hmin⟩ :=
    exists_least (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s t) hex
  have hfirst : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe s r → WMSetLt Lax822549.WideMachines.WMLe r t → ¬Stop r := fun r hlb hlt hc =>
    ((wmSetLt_iff r t).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 r t
      ((wmSetLt_iff r t).mp hlt).1 (hmin r ⟨hc, hlb⟩))
  exact ⟨t, hstop, hge, hfirst,
    reachesIn_scanRight h hge fun r hlb hlt =>
      hstep r hlb ⟨t, hstop, ((wmSetLt_iff r t).mp hlt).1⟩ (hfirst r hlb hlt)⟩

/-- **A leftward scan arrives at the first cell that stops it**, the same reading
downwards: the *greatest* stopping cell at or below `s`. -/
theorem reachesIn_scanLeft_greatest (h : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {q : A}
    {tp : Lax822549.WideMachines.WPoint A → Lax822549.WideMachines.WPoint A} {Stop : (A → Prop) → Prop} {s : A → Prop}
    (hex : ∃ t, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s)
    (hstep : ∀ r : A → Prop, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s →
      (∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t r) → ¬Stop r →
      ∃ τ a : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ a ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ a ∧ ¬Lax822549.WideMachines.WMRight τ ∧
        tp (Sum.inl r) = Sum.inr a) :
    ∃ t : A → Prop, Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s ∧
      (∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe t r → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s → ¬Stop r) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn (wideRank s - wideRank t)
        ⟨Sum.inr q, Sum.inl s, tp⟩ ⟨Sum.inr q, Sum.inl t, tp⟩ := by
  obtain ⟨t, ⟨hstop, hle⟩, hmax⟩ :=
    exists_greatest (isLinOrd_wmSetLe h) (P := fun t => Stop t ∧ Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe t s) hex
  have hfirst : ∀ r : A → Prop, WMSetLt Lax822549.WideMachines.WMLe t r → Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe r s → ¬Stop r := fun r hlt hub hc =>
    ((wmSetLt_iff t r).mp hlt).2 ((isLinOrd_wmSetLe h).2.2.1 t r
      ((wmSetLt_iff t r).mp hlt).1 (hmax r ⟨hc, hub⟩))
  exact ⟨t, hstop, hle, hfirst,
    reachesIn_scanLeft h hle fun r hlt hub =>
      hstep r hub ⟨t, hstop, ((wmSetLt_iff t r).mp hlt).1⟩ (hfirst r hlt hub)⟩

/-! ### A run that accepts -/

end Roam

end Lax822549Proofs.DescriptiveComplexity


