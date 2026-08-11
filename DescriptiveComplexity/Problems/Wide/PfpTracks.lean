/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTable

/-!
# Payloads by name, and the tape they present

`DescriptiveComplexity.Pfp.Table` gives a state, a symbol and a transition each a
payload `Fin c → A`, and `DescriptiveComplexity.Pfp.pad` makes that payload the
element's only spelling. Nothing so far says what the coordinates *are*, and a
program that had to count them would be unreadable. This file names them:

> the payload is a function of a finite **slot** type, and a slot that carries a
> bit holds one of the two designated elements.

`DescriptiveComplexity.Pfp.slotPl` is the naming – a payload is `f ∘ e.symm` for
the canonical enumeration `e` of the slots, so two payloads are equal exactly
when the functions are – and `DescriptiveComplexity.Pfp.bitVal` is the bit, read
back by `DescriptiveComplexity.Pfp.bitVal_iff` from the two designated elements
being distinct. Between them, the distinctness obligations a transition table
owes (`DescriptiveComplexity.Pfp.Table.Sep`) become statements about *named*
fields.

Which slots there are is not decided here.
`DescriptiveComplexity.Problems.Wide.PfpRules` splits them into the **control**
slots a state uses and the **track** slots a symbol uses, and builds the tape a
register pass runs over on top of the two.
-/

namespace DescriptiveComplexity

namespace Pfp

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

/-- **Two bits are the same element only if they are the same bit.** This is what
a distinctness obligation of the transition table is discharged from: two rules
told apart by a single track read different symbols. -/
theorem bitVal_inj (hne : zero ≠ one) (h : bitVal zero one P = bitVal zero one Q) : P ↔ Q :=
  ((bitVal_iff hne).symm.trans (by rw [h])).trans (bitVal_iff hne)

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

/-- Payloads agreeing slot by slot are equal. -/
theorem slotPl_congr {f g : S → A} (h : ∀ s, f s = g s) : slotPl f = slotPl g :=
  congrArg _ (funext h)

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

end Pfp

end DescriptiveComplexity
