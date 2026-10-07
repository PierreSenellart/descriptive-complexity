/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Walk
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
# Incrementing the mirror

The first real subroutine of a wide machine, and the one every address
computation goes through. A program keeps a **mirror** of the address it is
working on – one bit per element, in a track over its register file
(`DescriptiveComplexity.IxFile`) – because the head cannot read the digits of its
own address. Moving the working cell one to the right means adding one to the
mirror, and adding one is:

> walk the register file **downwards**, clearing the digits that are set; at the
> first digit that is clear, set it and stop clearing.

That is the binary increment of `DescriptiveComplexity.Problems.Wide.Increment`,
whose least significant digit is the `WMLe`-*greatest* element – which is why the
walk runs downwards – and `DescriptiveComplexity.IxFile.reachesIn_mirrorIncr`
says the program computes it: from the last register in the carrying state with
the mirror at `s`, the machine arrives below the first register in the stopped
state with the mirror at `t`, for the unique `t` with `WMIncr WMLe s t`. It costs
one move per register plus the step off the file, so a caller that is counting
bounds the moves and gets the product.

## What a caller supplies

The tape is given as a function **of the mirror**, `tapeOf m`, with one coherence
condition: changing the mirror at one element changes the tape at that element's
cell and nowhere else. Everything else a program keeps on its tape is therefore
carried along untouched, and no track discipline has to be fixed here. Three
transition families do the work – clear a set digit and keep carrying, set a
clear digit and stop, rewrite anything once stopped – plus the scanning
transitions that carry the head between consecutive registers.

The states are the caller's: `qc` for carrying, and a *family* `qd` for stopped.
The family is the point – the machine ends in `qd u₀` where `u₀` is the **carry
position**, the digit the increment set, and the conclusion says so along with its
characterization. A state may hold an element, so reporting the carry costs
nothing in the control, and it is what the fold of
`DescriptiveComplexity.Problems.Wide.Fold` needs: which block rolled over decides
which accumulators reset. So the caller reads both “the increment is finished” and
“here is where it carried” off the state, and neither off the tape.

## The other writing pass

`DescriptiveComplexity.IxFile.reachesIn_fileWrite` is the same walk with nothing
accumulated: one state throughout, and every register simply given its new digit.
Copying the mirror into a spare register, clearing a track and loading a computed
value are all that pass. Together with the read-only pass of
`DescriptiveComplexity.Problems.Wide.Test` these are the three shapes a program's
register work comes in – write with an accumulator, write without one, read with
one – and nothing below them is ever a case split again.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Mirror

variable {A : Type} [Lax822549.WideMachines.wide.Structure A] {I : Type} {ile : I → I → Prop}

/-! ### The mirror during the walk -/

/-- The mirror as it stands when the walk has come down to `u`: incremented
strictly above `u`, untouched at `u` and below. -/
private def midMirror (ile : I → I → Prop) (s t : I → Prop) (u v : I) : Prop :=
  (WMLt ile u v ∧ t v) ∨ (¬WMLt ile u v ∧ s v)

variable {s t : I → Prop}

/-- At the last register nothing has been touched yet. -/
private theorem midMirror_top {m : I} (hm : ∀ v : I, ile v m) : midMirror ile s t m = s :=
  funext fun v => propext
    ⟨fun hc => hc.elim (fun hc' => absurd (hm v) hc'.1.2) fun hc' => hc'.2,
      fun hs => Or.inr ⟨fun hlt => hlt.2 (hm v), hs⟩⟩

/-- Off the register just processed, the mirror does not change. -/
private theorem midMirror_agree (h : Lax904597.Machines.IsLinOrd ile) {u u' : I} (hs : IxSucc ile u u')
    {v : I} (hv : v ≠ u') : midMirror ile s t u v ↔ midMirror ile s t u' v := by
  have hiff : WMLt ile u v ↔ WMLt ile u' v := by
    refine ⟨fun hlt => ⟨hs.2 v hlt, fun hc => hv (h.2.2.1 v u' hc (hs.2 v hlt))⟩,
      fun hlt => ⟨h.2.1 u u' v hs.1.1 hlt.1, fun hc => hs.1.2 (h.2.1 u' v u hlt.1 hc)⟩⟩
  unfold midMirror
  rw [hiff]

/-- At the register just processed the mirror holds its new digit. -/
private theorem midMirror_at {u u' : I} (hs : IxSucc ile u u') :
    midMirror ile s t u u' ↔ t u' :=
  ⟨fun hc => hc.elim (fun hc' => hc'.2) fun hc' => absurd hs.1 hc'.1,
    fun ht => Or.inl ⟨hs.1, ht⟩⟩

/-- At the register about to be processed the mirror still holds its old
digit. -/
private theorem midMirror_at' (h : Lax904597.Machines.IsLinOrd ile) {u : I} :
    midMirror ile s t u u ↔ s u :=
  ⟨fun hc => hc.elim (fun hc' => absurd (h.1 u) hc'.1.2) fun hc' => hc'.2,
    fun hs => Or.inr ⟨fun hlt => hlt.2 (h.1 u), hs⟩⟩

/-! ### What the increment does to a digit -/

/-- Above the carry position every digit of the increment is clear. -/
private theorem not_incr_of_lt (h : Lax904597.Machines.IsLinOrd ile) (hi : WMIncr ile s t) {u₀ : I}
    (hu₀ : ¬s u₀) (hab : ∀ v : I, WMLt ile u₀ v → s v) {v : I} (hlt : WMLt ile u₀ v) :
    ¬t v := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  refine fun hc => ((ht v).mp hc).elim (fun he => hlt.2 ?_) fun hc' => hc'.2 hlt
  rw [he]
  exact h.1 u₀

/-- Below the carry position the increment leaves every digit alone. -/
private theorem incr_iff_of_lt (h : Lax904597.Machines.IsLinOrd ile) (hi : WMIncr ile s t) {u₀ : I}
    (hu₀ : ¬s u₀) (hab : ∀ v : I, WMLt ile u₀ v → s v) {v : I} (hlt : WMLt ile v u₀) :
    t v ↔ s v := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  refine (ht v).trans ⟨fun hc => hc.elim (fun he => absurd ?_ hlt.2) fun hc' => hc'.1,
    fun hsv => Or.inr ⟨hsv, fun hc => hlt.2 hc.1⟩⟩
  rw [← he]
  exact h.1 v

/-- At the carry position the increment sets the digit. -/
private theorem incr_carry (h : Lax904597.Machines.IsLinOrd ile) (hi : WMIncr ile s t) {u₀ : I}
    (hu₀ : ¬s u₀) (hab : ∀ v : I, WMLt ile u₀ v → s v) : t u₀ := by
  obtain ⟨w, hw, haw, ht⟩ := hi
  rw [wmIncr_carry_unique h hw haw hu₀ hab] at ht
  exact (ht u₀).mpr (Or.inl rfl)

/-! ### Processing one register

The whole case analysis of the subroutine happens here, once: what the machine
does at the register of `w` depends only on whether every digit above `w` is set
and on whether the digit at `w` is. Everything after this is bookkeeping, and
none of it is a case split. -/

/-- The mirror after the register of `w` has been processed. -/
private def procMirror (ile : I → I → Prop) (s t : I → Prop) (w : I) : I → Prop :=
  fun v => (v = w ∧ t v) ∨ (v ≠ w ∧ midMirror ile s t w v)

variable {qc : A} {qd : I → A}

/-- The mirror after processing one register is the mirror on arriving at the
next one down. -/
private theorem procMirror_succ (h : Lax904597.Machines.IsLinOrd ile) {u u' : I} (hs : IxSucc ile u u') :
    procMirror ile s t u' = midMirror ile s t u := by
  refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
  · rcases hc with ⟨rfl, ht⟩ | ⟨hne, hm⟩
    · exact (midMirror_at hs).mpr ht
    · exact (midMirror_agree h hs hne).mpr hm
  · rcases eq_or_ne v u' with rfl | hne
    · exact Or.inl ⟨rfl, (midMirror_at hs).mp hc⟩
    · exact Or.inr ⟨hne, (midMirror_agree h hs hne).mp hc⟩

/-- Processing the first register finishes the increment. -/
private theorem procMirror_bot (h : Lax904597.Machines.IsLinOrd ile) {l : I} (hl : ∀ v : I, ile l v) :
    procMirror ile s t l = t := by
  refine funext fun v => propext ⟨fun hc => ?_, fun ht => ?_⟩
  · rcases hc with ⟨-, ht⟩ | ⟨hne, hm⟩
    · exact ht
    · exact (hm.resolve_right fun hc' => hc'.1 ⟨hl v, fun hcon => hne (h.2.2.1 v l hcon (hl v))⟩).2
  · rcases eq_or_ne v l with rfl | hne
    · exact Or.inl ⟨rfl, ht⟩
    · exact Or.inr ⟨hne, Or.inl ⟨⟨hl v, fun hcon => hne (h.2.2.1 v l hcon (hl v))⟩, ht⟩⟩

variable {g : (I → Prop) → I → A}

/-- **What the machine does at one register.** Reading the mirror's digit at `w`
in the state it arrived in, it writes the digit the increment puts there, moves
left, and goes to the state it leaves in. The three transition families of the
caller cover the three cases, and this is the only place they are distinguished:
carry on through a set digit, stop at a clear one, and rewrite once stopped. -/
private theorem incr_process (h : Lax904597.Machines.IsLinOrd ile) (hi : WMIncr ile s t)
    {u₀ : I} (hu₀ : ¬s u₀) (hab : ∀ v : I, WMLt ile u₀ v → s v)
    (hone : ∀ (m : I → Prop) (u : I), m u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qc ∧
      Lax822549.WideMachines.WMRead τ (g m u) ∧ Lax822549.WideMachines.WMDst τ qc ∧
      Lax822549.WideMachines.WMWrite τ (g (fun v => m v ∧ v ≠ u) u) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hzero : ∀ (m : I → Prop) (u : I), ¬m u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qc ∧
      Lax822549.WideMachines.WMRead τ (g m u) ∧ Lax822549.WideMachines.WMDst τ (qd u) ∧
      Lax822549.WideMachines.WMWrite τ (g (fun v => m v ∨ v = u) u) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hkeep : ∀ (u : I) (m : I → Prop) (w : I), ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ (qd u) ∧
      Lax822549.WideMachines.WMRead τ (g m w) ∧ Lax822549.WideMachines.WMDst τ (qd u) ∧ Lax822549.WideMachines.WMWrite τ (g m w) ∧
      ¬Lax822549.WideMachines.WMRight τ)
    (w : I) :
    ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ (accState ile s qc (qd u₀) w) ∧
      Lax822549.WideMachines.WMRead τ (g (midMirror ile s t w) w) ∧ Lax822549.WideMachines.WMDst τ (accStateAfter ile s qc (qd u₀) w) ∧
      Lax822549.WideMachines.WMWrite τ (g (procMirror ile s t w) w) ∧ ¬Lax822549.WideMachines.WMRight τ := by
  by_cases hcar : ∀ v : I, WMLt ile w v → s v
  · rw [accState, if_pos hcar]
    by_cases hbit : s w
    · -- a set digit: clear it and carry on
      have hge : ∀ v : I, ile w v → s v := fun v hle => by
        rcases eq_or_ne w v with rfl | hne
        · exact hbit
        · exact hcar v ⟨hle, fun hc => hne (h.2.2.1 w v hle hc)⟩
      have hlt : WMLt ile u₀ w := by
        refine ⟨(h.2.2.2 u₀ w).resolve_right fun hc => hu₀ (hge u₀ hc), fun hc => hu₀ ?_⟩
        exact hge u₀ hc
      have heq : procMirror ile s t w = fun v => midMirror ile s t w v ∧ v ≠ w := by
        refine funext fun v => propext ⟨fun hc => ?_, fun hc => Or.inr ⟨hc.2, hc.1⟩⟩
        rcases hc with ⟨rfl, ht⟩ | ⟨hne, hm⟩
        · exact absurd ht (not_incr_of_lt h hi hu₀ hab hlt)
        · exact ⟨hm, hne⟩
      rw [accStateAfter, if_pos hge, heq]
      exact hone _ w ((midMirror_at' h).mpr hbit)
    · -- a clear digit: set it and stop
      have hw : w = u₀ := wmIncr_carry_unique h hbit hcar hu₀ hab
      have heq : procMirror ile s t w = fun v => midMirror ile s t w v ∨ v = w := by
        refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
        · exact hc.elim (fun hc' => Or.inr hc'.1) fun hc' => Or.inl hc'.2
        · rcases eq_or_ne v w with rfl | hne
          · exact Or.inl ⟨rfl, hw ▸ incr_carry h hi hu₀ hab⟩
          · exact Or.inr ⟨hne, hc.resolve_right hne⟩
      rw [accStateAfter, if_neg fun hall => hbit (hall w (h.1 w)), heq, ← hw]
      exact hzero _ w fun hc => hbit ((midMirror_at' h).mp hc)
  · -- already stopped: rewrite the symbol and walk on
    obtain ⟨v₀, hv₀⟩ : ∃ v : I, ¬(WMLt ile w v → s v) := by
      by_contra hc
      exact hcar fun v hlt => not_not.mp fun hcon => hc ⟨v, fun hi' => hcon (hi' hlt)⟩
    have hlt : WMLt ile w u₀ := by
      have hwv : WMLt ile w v₀ := (Classical.not_imp.mp hv₀).1
      have hnv : ¬s v₀ := (Classical.not_imp.mp hv₀).2
      have hvu : ile v₀ u₀ := by
        by_contra hc
        exact hnv (hab v₀ ⟨(h.2.2.2 u₀ v₀).resolve_right hc, hc⟩)
      exact ⟨h.2.1 w v₀ u₀ hwv.1 hvu, fun hc => hwv.2 (h.2.1 v₀ u₀ w hvu hc)⟩
    have heq : procMirror ile s t w = midMirror ile s t w := by
      refine funext fun v => propext ⟨fun hc => ?_, fun hc => ?_⟩
      · rcases hc with ⟨rfl, ht⟩ | ⟨-, hm⟩
        · exact (midMirror_at' h).mpr ((incr_iff_of_lt h hi hu₀ hab hlt).mp ht)
        · exact hm
      · rcases eq_or_ne v w with rfl | hne
        · exact Or.inl ⟨rfl, (incr_iff_of_lt h hi hu₀ hab hlt).mpr ((midMirror_at' h).mp hc)⟩
        · exact Or.inr ⟨hne, hc⟩
    rw [accState, if_neg hcar, accStateAfter,
      if_neg fun hall => hcar fun v hvlt => hall v hvlt.1, heq]
    exact hkeep u₀ _ _

/-! ### The subroutine -/

variable [Finite A]

namespace IxFile

variable [Finite I] (F : IxFile A I ile)

/-- **The mirror increment.** From the last register of the file, carrying, with
the mirror at `s`, the machine walks down the file and arrives just below the
first register, stopped, with the mirror at the increment of `s`.

The three transition families do the arithmetic and the scanning ones carry the
head between consecutive registers; the coherence condition `hcoh` is what says
the rest of the tape – whatever else the program keeps there – comes through
untouched. The cost is one move per register, each bounded by `w`, plus the step
off the file. -/
theorem reachesIn_mirrorIncr (h : Lax904597.Machines.IsLinOrd ile) (ha : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A)))
    (hi : WMIncr ile s t)
    {b : A} {w : ℕ} {tapeOf : (I → Prop) → (A → Prop) → A}
    (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    (hcoh : ∀ (m m' : I → Prop) (u : I), (∀ v : I, v ≠ u → (m v ↔ m' v)) →
      ∀ r : A → Prop, r ≠ F.cell u → tapeOf m r = tapeOf m' r)
    (hone : ∀ (m : I → Prop) (u : I), m u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qc ∧
      Lax822549.WideMachines.WMRead τ (tapeOf m (F.cell u)) ∧ Lax822549.WideMachines.WMDst τ qc ∧
      Lax822549.WideMachines.WMWrite τ (tapeOf (fun v => m v ∧ v ≠ u) (F.cell u)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hzero : ∀ (m : I → Prop) (u : I), ¬m u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qc ∧
      Lax822549.WideMachines.WMRead τ (tapeOf m (F.cell u)) ∧ Lax822549.WideMachines.WMDst τ (qd u) ∧
      Lax822549.WideMachines.WMWrite τ (tapeOf (fun v => m v ∨ v = u) (F.cell u)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hkeep : ∀ (u : I) (m : I → Prop) (v : I), ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ (qd u) ∧
      Lax822549.WideMachines.WMRead τ (tapeOf m (F.cell v)) ∧ Lax822549.WideMachines.WMDst τ (qd u) ∧ Lax822549.WideMachines.WMWrite τ (tapeOf m (F.cell v)) ∧
      ¬Lax822549.WideMachines.WMRight τ)
    (hskip : ∀ q : A, (q = qc ∨ ∃ u : I, q = qd u) → ∀ (m : I → Prop) (r : A → Prop),
      (∃ x : I, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell x) r) → (∀ x : I, r ≠ F.cell x) →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (tapeOf m r) ∧ Lax822549.WideMachines.WMDst τ q ∧
        Lax822549.WideMachines.WMWrite τ (tapeOf m r) ∧ ¬Lax822549.WideMachines.WMRight τ)
    {top bot : I} (htop : ∀ v : I, ile v top) (hbot : ∀ v : I, ile bot v) :
    ∃ (u₀ : I) (p : A → Prop), (¬s u₀ ∧ ∀ v : I, WMLt ile u₀ v → s v) ∧
      WMIncr Lax822549.WideMachines.WMLe p (F.cell bot) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr qc, Sum.inl (F.cell top), wideTape (tapeOf s) b⟩
        ⟨Sum.inr (qd u₀), Sum.inl p, wideTape (tapeOf t) b⟩ := by
  obtain ⟨u₀, hu₀, hab, -⟩ := id hi
  -- The walk down the file, one register at a time.
  have hwalk := F.reachesIn_regWalkBack h (b := b) (st := accState ile s qc (qd u₀))
    (tp := fun u => tapeOf (midMirror ile s t u)) (u₁ := top) (w := w)
    (fun u u' hs _ => ?_) bot (hbot top)
  · -- The last write, at the first register, and the step off the file.
    obtain ⟨p, hp⟩ := exists_wmPred ha (s := F.cell bot) (F.cell_nonempty bot)
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      incr_process (g := fun m u => tapeOf m (F.cell u)) h hi hu₀ hab hone hzero hkeep bot
    rw [accStateAfter_bot_neg hbot hu₀] at hdst
    rw [procMirror_bot h hbot] at hwrite
    refine ⟨u₀, p, ⟨hu₀, hab⟩, hp, TMData.ReachesIn.tail ?_
      (step_wideTape_left ha hp htr hsrc hread hdst hwrite hright fun r hr =>
        hcoh t (midMirror ile s t bot) bot (fun v hv => ?_) r hr)⟩
    · rw [show accState ile s qc (qd u₀) top = qc from accState_top htop,
        show midMirror ile s t top = s from midMirror_top htop] at hwalk
      exact hwalk
    · exact ⟨fun ht => Or.inl ⟨⟨hbot v, fun hc => hv (h.2.2.1 v bot hc (hbot v))⟩, ht⟩,
        fun hm => (hm.resolve_right fun hc =>
          hc.1 ⟨hbot v, fun hc' => hv (h.2.2.1 v bot hc' (hbot v))⟩).2⟩
  · -- One register: what to write is the case analysis, where to go next is the walk.
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      incr_process (g := fun m u => tapeOf m (F.cell u)) h hi hu₀ hab hone hzero hkeep u'
    rw [accStateAfter_succ h hs] at hdst
    rw [procMirror_succ h hs] at hwrite
    refine TMData.ReachesIn.mono (hgap u u' hs)
      (F.reachesIn_regStepBack ha h hs ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩
        (fun r hr => hcoh _ _ u' (fun v hv => midMirror_agree h hs hv) r hr) fun r hbnd hr => ?_)
    exact hskip _ ((accState_cases u).imp id fun hc => ⟨u₀, hc⟩) _ r hbnd hr

/-! ### Overwriting a track

The same walk with nothing accumulated: the state never changes, and every
register is simply given its new digit. Copying the mirror into a spare register,
clearing a track and loading a computed value are all this pass. -/

/-- **Overwriting a track.** A pass down the file in a single state, replacing the
track's digit at every register: the machine starts at the last register with the
track at `s` and arrives just below the first register with it at `t`.

Since nothing is accumulated, `t` is arbitrary – the caller's transitions say what
to write at each register, and may read the old digit to decide. -/
theorem reachesIn_fileWrite (h : Lax904597.Machines.IsLinOrd ile) (ha : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b q : A}
    {w : ℕ}
    {tapeOf : (I → Prop) → (A → Prop) → A}
    (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    (hcoh : ∀ (m m' : I → Prop) (u : I), (∀ v : I, v ≠ u → (m v ↔ m' v)) →
      ∀ r : A → Prop, r ≠ F.cell u → tapeOf m r = tapeOf m' r)
    (hstep : ∀ (m : I → Prop) (u : I), ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧
      Lax822549.WideMachines.WMRead τ (tapeOf m (F.cell u)) ∧ Lax822549.WideMachines.WMDst τ q ∧
      Lax822549.WideMachines.WMWrite τ (tapeOf (fun v => (v = u ∧ t v) ∨ (v ≠ u ∧ m v)) (F.cell u)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hskip : ∀ (m : I → Prop) (r : A → Prop), (∃ x : I, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell x) r) →
      (∀ x : I, r ≠ F.cell x) →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (tapeOf m r) ∧ Lax822549.WideMachines.WMDst τ q ∧
        Lax822549.WideMachines.WMWrite τ (tapeOf m r) ∧ ¬Lax822549.WideMachines.WMRight τ)
    {top bot : I} (htop : ∀ v : I, ile v top) (hbot : ∀ v : I, ile bot v) :
    ∃ p : A → Prop, WMIncr Lax822549.WideMachines.WMLe p (F.cell bot) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr q, Sum.inl (F.cell top), wideTape (tapeOf s) b⟩
        ⟨Sum.inr q, Sum.inl p, wideTape (tapeOf t) b⟩ := by
  have hwalk := F.reachesIn_regWalkBack h (b := b) (st := fun _ => q)
    (tp := fun u => tapeOf (midMirror ile s t u)) (u₁ := top) (w := w)
    (fun u u' hs _ => ?_) bot (hbot top)
  · obtain ⟨p, hp⟩ := exists_wmPred ha (s := F.cell bot) (F.cell_nonempty bot)
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep (midMirror ile s t bot) bot
    rw [show (fun v => (v = bot ∧ t v) ∨ (v ≠ bot ∧ midMirror ile s t bot v)) = t from
      procMirror_bot h hbot] at hwrite
    refine ⟨p, hp, TMData.ReachesIn.tail ?_
      (step_wideTape_left ha hp htr hsrc hread hdst hwrite hright fun r hr =>
        hcoh t (midMirror ile s t bot) bot (fun v hv => ?_) r hr)⟩
    · rw [show midMirror ile s t top = s from midMirror_top htop] at hwalk
      exact hwalk
    · exact ⟨fun ht => Or.inl ⟨⟨hbot v, fun hc => hv (h.2.2.1 v bot hc (hbot v))⟩, ht⟩,
        fun hm => (hm.resolve_right fun hc =>
          hc.1 ⟨hbot v, fun hc' => hv (h.2.2.1 v bot hc' (hbot v))⟩).2⟩
  · obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ := hstep (midMirror ile s t u') u'
    rw [show (fun v => (v = u' ∧ t v) ∨ (v ≠ u' ∧ midMirror ile s t u' v)) =
        midMirror ile s t u from
      procMirror_succ h hs] at hwrite
    exact TMData.ReachesIn.mono (hgap u u' hs)
      (F.reachesIn_regStepBack ha h hs ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩
        (fun r hr => hcoh _ _ u' (fun v hv => midMirror_agree h hs hv) r hr)
        fun r hbnd hr => hskip _ r hbnd hr)

end IxFile

/-! ### The same, at the file the input channel marks -/

section Marked

end Marked

end Mirror

end Lax822549Proofs.DescriptiveComplexity


