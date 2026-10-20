/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawTable
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
# Payloads by name, and the tape they present

`DescriptiveComplexity.Draw.Table` gives a state, a symbol and a transition each a
payload `Fin c → A`, and `DescriptiveComplexity.Draw.pad` makes that payload the
element's only spelling. Nothing so far says what the coordinates *are*, and a
program that had to count them would be unreadable. This file names them:

> the payload is a function of a finite **slot** type, and a slot that carries a
> bit holds one of the two designated elements.

`DescriptiveComplexity.Draw.slotPl` is the naming – a payload is `f ∘ e.symm` for
the canonical enumeration `e` of the slots, so two payloads are equal exactly
when the functions are – and `DescriptiveComplexity.Draw.bitVal` is the bit, read
back by `DescriptiveComplexity.Draw.bitVal_iff` from the two designated elements
being distinct. Between them, the distinctness obligations a transition table
owes (`DescriptiveComplexity.Draw.Table.Sep`) become statements about *named*
fields.

Which slots there are is not decided here.
`DescriptiveComplexity.Problems.Wide.DrawRules` splits them into the **control**
slots a state uses and the **track** slots a symbol uses, and builds the tape a
register pass runs over on top of the two.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### Bits -/

section Bits

variable {A : Type}

open Classical in
/-- **The element a bit is written as**: the designated `one` when it is set, the
designated `zero` when it is clear. -/
noncomputable def bitVal (zero one : A) (P : Prop) : A := if P then one else zero

variable {zero one : A} {P Q : Prop}

@[simp]
theorem bitVal_pos (hP : P) : bitVal zero one P = one := by simp [bitVal, hP]

@[simp]
theorem bitVal_neg (hP : ¬P) : bitVal zero one P = zero := by simp [bitVal, hP]

/-- **A bit reads back**, the two designated elements being distinct. -/
theorem bitVal_iff (hne : zero ≠ one) : bitVal zero one P = one ↔ P := by
  by_cases hp : P
  · exact iff_of_true (bitVal_pos hp) hp
  · exact iff_of_false (by rw [bitVal_neg hp]; exact hne) hp

/-- Bits that agree are the same element. -/
theorem bitVal_congr (h : P ↔ Q) : bitVal zero one P = bitVal zero one Q := by
  by_cases hp : P
  · rw [bitVal_pos hp, bitVal_pos (h.mp hp)]
  · rw [bitVal_neg hp, bitVal_neg fun hc => hp (h.mpr hc)]

end Bits

/-! ### Payloads by name -/

section Slots

variable {A S : Type} [Fintype S]

/-- **A payload, named**: the value of each slot, read through the canonical
enumeration of the slot type. A program writes `slotPl fun s => …` and never
mentions a coordinate number. -/
noncomputable def slotPl (f : S → A) : Fin (Fintype.card S) → A :=
  fun i => f ((Fintype.equivFin S).symm i)

@[simp]
theorem slotPl_apply (f : S → A) (s : S) : slotPl f (Fintype.equivFin S s) = f s := by
  rw [slotPl, Equiv.symm_apply_apply]

/-- **A payload is determined by its slots**, so a distinctness obligation about
elements is one about the fields a program named. -/
theorem slotPl_injective : Function.Injective (slotPl (S := S) (A := A)) := by
  intro f g h
  refine funext fun s => ?_
  have := congrFun h (Fintype.equivFin S s)
  rwa [slotPl_apply, slotPl_apply] at this

/-- **Reading a payload by name**: the value a coordinate holds, addressed by its
slot. This is what a rule's guard and its written symbol are written with – the
rule's data arrives as a tuple and every field of it is `unslot`. -/
noncomputable def unslot (w : Fin (Fintype.card S) → A) : S → A :=
  fun s => w (Fintype.equivFin S s)

@[simp]
theorem unslot_slotPl (f : S → A) : unslot (slotPl f) = f :=
  funext fun s => slotPl_apply f s

@[simp]
theorem slotPl_unslot (w : Fin (Fintype.card S) → A) : slotPl (unslot w) = w :=
  funext fun i => by rw [slotPl, unslot, Equiv.apply_symm_apply]

end Slots

end Draw

end Lax822549Proofs.DescriptiveComplexity


