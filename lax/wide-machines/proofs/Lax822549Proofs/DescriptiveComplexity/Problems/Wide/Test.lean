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
# Testing the register file

The read-only half of what a wide machine does with its registers. A program has
to ask questions about a whole register before it can act on it – *is the mirror
equal to the target?*, *is it zero?*, *has the working cell reached the end of the
tape?* – and each of them is one pass:

> walk the file downwards in the passing state; at the first register that fails
> the test, drop into the failing state and stay there.

`DescriptiveComplexity.IxFile.reachesIn_fileTest` is that pass, at an arbitrary
property `P` of the registers. It writes nothing – the tape it ends with is the
tape it started with – so a program may run as many tests as it likes between two
computations and disturb neither.

The verdict comes back in the **state**, as
`DescriptiveComplexity.accStateAfter WMLe P qy qn bot`, which
`DescriptiveComplexity.accStateAfter_bot_pos` and
`DescriptiveComplexity.accStateAfter_bot_neg` read as the two cases: the passing
state exactly when every register passes. A caller instantiates `P` with whatever
it is asking – two tracks agree, a track is clear, a track is set – and the
transitions it supplies say how to see that in one symbol.

A pass costs one move per register plus the step off the file, so a caller that
is counting bounds the moves – the addresses between consecutive registers – and
gets the product.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Test

variable {A : Type} [Lax822549.WideMachines.wide.Structure A]

variable {I : Type} {ile : I → I → Prop} {P : I → Prop} {qy qn : A}

/-- **What a test does at one register**: in the passing state it stays there if
the register passes and drops to the failing state if not; in the failing state
it stays. The symbol is rewritten by itself in every case, which is why a test
leaves the tape alone.

This is the whole case analysis of a test, and – as in
`DescriptiveComplexity.Problems.Wide.Mirror` – it happens once. The symbols are
given as a function `g` of the element whose register the head is on, so no
register file is named here. -/
private theorem test_process (h : Lax904597.Machines.IsLinOrd ile) {g : I → A}
    (hpass : ∀ u : I, P u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qy ∧ Lax822549.WideMachines.WMRead τ (g u) ∧
      Lax822549.WideMachines.WMDst τ qy ∧ Lax822549.WideMachines.WMWrite τ (g u) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hfail : ∀ u : I, ¬P u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qy ∧ Lax822549.WideMachines.WMRead τ (g u) ∧
      Lax822549.WideMachines.WMDst τ qn ∧ Lax822549.WideMachines.WMWrite τ (g u) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hkeep : ∀ w : I, ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qn ∧ Lax822549.WideMachines.WMRead τ (g w) ∧ Lax822549.WideMachines.WMDst τ qn ∧
      Lax822549.WideMachines.WMWrite τ (g w) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (w : I) :
    ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ (accState ile P qy qn w) ∧ Lax822549.WideMachines.WMRead τ (g w) ∧
      Lax822549.WideMachines.WMDst τ (accStateAfter ile P qy qn w) ∧ Lax822549.WideMachines.WMWrite τ (g w) ∧ ¬Lax822549.WideMachines.WMRight τ := by
  by_cases hcar : ∀ v : I, WMLt ile w v → P v
  · rw [accState, if_pos hcar]
    by_cases hw : P w
    · have hge : ∀ v : I, ile w v → P v := fun v hle => by
        rcases eq_or_ne w v with rfl | hne
        · exact hw
        · exact hcar v ⟨hle, fun hc => hne (h.2.2.1 w v hle hc)⟩
      rw [accStateAfter, if_pos hge]
      exact hpass w hw
    · rw [accStateAfter, if_neg fun hall => hw (hall w (h.1 w))]
      exact hfail w hw
  · rw [accState, if_neg hcar, accStateAfter,
      if_neg fun hall => hcar fun v hlt => hall v hlt.1]
    exact hkeep _

variable [Finite A]

namespace IxFile

variable [Finite I] (F : IxFile A I ile) {f : (A → Prop) → A}

/-- **A test of the register file.** From the last register in the passing state,
the machine walks down the file and arrives just below the first register in the
state the verdict names: passing exactly when every register passed
(`DescriptiveComplexity.accStateAfter_bot_pos`,
`DescriptiveComplexity.accStateAfter_bot_neg`). The tape is untouched throughout.

Instantiate `P` with the question: *these two tracks agree at this register*,
*this track is clear here*, *this track is set here*. The transitions the caller
supplies are then a single symbol comparison each. The cost is one move per
register, each bounded by `w`, plus the step off the file. -/
theorem reachesIn_fileTest (h : Lax904597.Machines.IsLinOrd ile) (ha : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := A))) {b : A} {w : ℕ}
    (hgap : ∀ u u' : I, IxSucc ile u u' →
      wideRank (F.cell u') - wideRank (F.cell u) ≤ w)
    (hpass : ∀ u : I, P u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qy ∧ Lax822549.WideMachines.WMRead τ (f (F.cell u)) ∧
      Lax822549.WideMachines.WMDst τ qy ∧ Lax822549.WideMachines.WMWrite τ (f (F.cell u)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hfail : ∀ u : I, ¬P u → ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qy ∧ Lax822549.WideMachines.WMRead τ (f (F.cell u)) ∧
      Lax822549.WideMachines.WMDst τ qn ∧ Lax822549.WideMachines.WMWrite τ (f (F.cell u)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hkeep : ∀ v : I, ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ qn ∧ Lax822549.WideMachines.WMRead τ (f (F.cell v)) ∧ Lax822549.WideMachines.WMDst τ qn ∧
      Lax822549.WideMachines.WMWrite τ (f (F.cell v)) ∧ ¬Lax822549.WideMachines.WMRight τ)
    (hskip : ∀ q : A, (q = qy ∨ q = qn) → ∀ r : A → Prop,
      (∃ x : I, Lax822549.WideMachines.WMSetLe Lax822549.WideMachines.WMLe (F.cell x) r) → (∀ x : I, r ≠ F.cell x) →
      ∃ τ : A, Lax822549.WideMachines.WMTr τ ∧ Lax822549.WideMachines.WMSrc τ q ∧ Lax822549.WideMachines.WMRead τ (f r) ∧ Lax822549.WideMachines.WMDst τ q ∧ Lax822549.WideMachines.WMWrite τ (f r) ∧ ¬Lax822549.WideMachines.WMRight τ)
    {top bot : I} (htop : ∀ v : I, ile v top) (hbot : ∀ v : I, ile bot v) :
    ∃ p : A → Prop, WMIncr Lax822549.WideMachines.WMLe p (F.cell bot) ∧
      (Lax822549.WideMachines.wideData A).ReachesIn ((ixRank ile top - ixRank ile bot) * w + 1)
        ⟨Sum.inr qy, Sum.inl (F.cell top), wideTape f b⟩
        ⟨Sum.inr (accStateAfter ile P qy qn bot), Sum.inl p, wideTape f b⟩ := by
  have hwalk := F.reachesIn_regWalkBack h (b := b) (st := accState ile P qy qn) (tp := fun _ => f)
    (u₁ := top) (w := w) (fun u u' hs _ => ?_) bot (hbot top)
  · -- The last register, and the step off the file.
    obtain ⟨p, hp⟩ := exists_wmPred ha (s := F.cell bot) (F.cell_nonempty bot)
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      test_process h hpass hfail hkeep bot
    refine ⟨p, hp, TMData.ReachesIn.tail ?_
      (step_wideTape_left ha hp htr hsrc hread hdst hwrite hright fun _ _ => rfl)⟩
    rw [show accState ile P qy qn top = qy from accState_top htop] at hwalk
    exact hwalk
  · -- One register: the test's verdict so far is the state, and nothing is written.
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      test_process h hpass hfail hkeep u'
    rw [accStateAfter_succ h hs] at hdst
    exact ((F.reachesIn_regStepBack ha h hs ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩
      (fun _ _ => rfl) fun r hbnd hr =>
        hskip _ (accState_cases u) r hbnd hr).mono (hgap u u' hs))

end IxFile

section Marked

end Marked

end Test

end Lax822549Proofs.DescriptiveComplexity


