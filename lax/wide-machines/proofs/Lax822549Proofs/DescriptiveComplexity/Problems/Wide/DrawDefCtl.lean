/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawDefLoop
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawAccCtl
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

/-!
# The control's reads and writes are definable

Everything the program keeps in its control is a **bit** – a flag, an
accumulator, a verdict – and every write of one is
`DescriptiveComplexity.Draw.Data.putVec` or its one-slot special case
`setCtl`: the named slots take the bits of a family, and every other slot rides
along. So one lemma per shape settles the whole control layer, given that the
questions behind the bits are definable.

Reading is the same statement one step simpler:
`DescriptiveComplexity.Draw.Data.readVec` is an existential over the levels of
a slot family, and `ctlBit` is a single atom.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

namespace Data

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : Data L} [Fintype dt.SlotIx]

/-! ### Reading -/

/-- **A control slot, read as a bit.** -/
theorem uGDefinable_ctlBit (q : dt.CtlIx) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.ctlBit e.one f q :=
  (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) q).congr fun _ _ _ => Iff.rfl

/-- **A vector of control slots, read at a level**: one atom below the length,
and nothing above it – a decision the formula is built with. -/
theorem uGDefinable_readVec {m : ℕ} (accs : Fin m → dt.CtlIx) (j : ℕ) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.readVec e.one accs f j := by
  by_cases hj : j < m
  · exact (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (accs ⟨j, hj⟩)).congr
      fun _ _ _ => ⟨fun hc => hc.elim fun _ hp => hp, fun hc => ⟨hj, hc⟩⟩
  · exact (uGDefinable_false (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun _ _ _ => ⟨fun hc => hc.elim fun hp _ => hj hp, False.elim⟩

/-- **A sub-fold's accumulator, read at a level.** -/
theorem uGDefinable_readSac (j : ℕ) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.readSac e.one f j :=
  uGDefinable_readVec dt.sacC j

/-! ### Writing -/

/-- **A vector of control slots, written**: the named slots take the bits of
the family, and every other slot rides along – so the whole write is definable
as soon as each of the family's questions is. -/
theorem uStDefinable_putVec {m : ℕ} {accs : Fin m → dt.CtlIx}
    (hinj : Function.Injective accs)
    {b : ∀ e : Env L, Fin m → (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : ∀ j : Fin m, UGDefinable fun e f g => b e j f g) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.putVec e.zero e.one accs f fun j => b e j f g := by
  classical
  intro q
  by_cases hq : ∃ j : Fin m, q = accs j
  · obtain ⟨j, rfl⟩ := hq
    refine (uSlotDefinable_bitVal (hb j)).congr fun e f g => ?_
    have hex : ∃ j' : Fin m, accs j = accs j' := ⟨j, rfl⟩
    change (if h : ∃ j' : Fin m, accs j = accs j' then
      bitVal e.zero e.one (b e h.choose f g) else f (accs j)) = _
    rw [dif_pos hex, hinj hex.choose_spec.symm]
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun _ _ _ => ?_
    exact putVec_of_not_mem fun j hc => hq ⟨j, hc⟩

/-- **One control slot, written.** -/
theorem uStDefinable_setCtl (q : dt.CtlIx)
    {b : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.setCtl e.zero e.one q (b e f g) f :=
  uStDefinable_id.update q (uSlotDefinable_bitVal hb)

/-- **The inner fold's accumulator vector, written.** -/
theorem uStDefinable_putAcc
    {b : ∀ e : Env L, Fin dt.naDim → (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : ∀ j : Fin dt.naDim, UGDefinable fun e f g => b e j f g) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.putAcc e.zero e.one f fun j => b e j f g :=
  uStDefinable_putVec dt.accC_injective hb

/-- **The leaf flag, stored.** -/
theorem uStDefinable_setLeaf
    {b : ∀ e : Env L, (dt.CtlIx → e.α) → (dt.SlotIx → e.α) → Prop}
    (hb : UGDefinable b) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e f g =>
      dt.setLeaf e.zero e.one (b e f g) f :=
  uStDefinable_setCtl dt.leafC hb

/-- **The folds at the empty valuation**: every accumulator the polarity's
unit, which is a question the formula is built from. -/
theorem uStDefinable_initAcc (pol : ℕ → Bool) :
    UStDefinable (L := L) (W := dt.SlotIx) fun e (f : dt.CtlIx → e.α) _ =>
      dt.initAcc e.zero e.one pol f :=
  uStDefinable_putAcc fun j => uGDefinable_const (pol (j : ℕ) = false)

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


