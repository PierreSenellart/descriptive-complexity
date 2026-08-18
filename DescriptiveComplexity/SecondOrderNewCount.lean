/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card

/-!
# Surjectivity from a flip

A sentence can say that a guessed family of sets contains the empty set and is
closed under flipping a single element, and it can say that the guess is
injective. It cannot say that the guess is **onto**: quantifying over all sets
is second order, and a first-order kernel over an extended universe has no way
to reach them.

This file is what buys surjectivity anyway, and it is a counting argument in
Lean rather than a condition in the logic. A family containing the empty set and
closed under one-element flips is *everything*
(`DescriptiveComplexity.eq_of_flipClosed`), because every finite set is reached
from the empty one by flipping its elements in one at a time; so an injective
guess into it is a bijection (`DescriptiveComplexity.bijective_of_flipClosed`,
and its set-valued reading `DescriptiveComplexity.bijective_of_flipClosedP`).

That is the shape the exponential rung of value invention needs: *invent
exponentially many* is not a condition a sentence states, it is a bound the
definition carries, and this is where the bound is spent.
-/

namespace DescriptiveComplexity

variable {α ι : Type}

/-- Flipping one element of a finite set: in if it was out, out if it was in. -/
def flipAt [DecidableEq α] (T : Finset α) (a : α) : Finset α :=
  if a ∈ T then T.erase a else insert a T

theorem flipAt_of_notMem [DecidableEq α] {T : Finset α} {a : α} (ha : a ∉ T) :
    flipAt T a = insert a T := by
  rw [flipAt, if_neg ha]

/-- **A family containing the empty set and closed under one-element flips is
everything**: every finite set is reached from the empty one by flipping its
elements in, one at a time. -/
theorem eq_of_flipClosed [DecidableEq α] {S : Finset α → Prop} (h0 : S ∅)
    (hflip : ∀ (T : Finset α) (a : α), S T → S (flipAt T a)) : ∀ T : Finset α, S T := by
  intro T
  induction T using Finset.induction_on with
  | empty => exact h0
  | insert a T ha ih => exact flipAt_of_notMem ha ▸ hflip T a ih

/-- **An injective guess into a flip-closed family is a bijection**: the family
is everything, so an injection into it is onto. -/
theorem bijective_of_flipClosed [DecidableEq α] (f : ι → Finset α)
    (hinj : Function.Injective f) (h0 : ∃ i, f i = ∅)
    (hflip : ∀ (i : ι) (a : α), ∃ j, f j = flipAt (f i) a) : Function.Bijective f := by
  refine ⟨hinj, ?_⟩
  refine eq_of_flipClosed (S := fun T => ∃ i, f i = T) h0 ?_
  rintro T a ⟨i, rfl⟩
  exact hflip i a

/-! ### The same, read at set-valued guesses -/

open Classical in
/-- The family a guess names, as finite sets. -/
noncomputable def toFinsetOf [Fintype α] (f : ι → α → Prop) (i : ι) : Finset α :=
  Finset.univ.filter (f i)

open Classical in
theorem mem_toFinsetOf [Fintype α] (f : ι → α → Prop) (i : ι) (x : α) :
    x ∈ toFinsetOf f i ↔ f i x := by
  simp [toFinsetOf]

open Classical in
/-- **An injective set-valued guess, flip-closed, is a bijection.** This is the
form a guessed meaning relation takes: one set of `α` per invented value. -/
theorem bijective_of_flipClosedP [Finite α] (f : ι → α → Prop)
    (hinj : Function.Injective f) (h0 : ∃ i, ∀ x, ¬f i x)
    (hflip : ∀ (i : ι) (a : α), ∃ j, ∀ x, f j x ↔ Xor (f i x) (x = a)) :
    Function.Bijective f := by
  classical
  let := Fintype.ofFinite α
  have hfin : Function.Bijective (toFinsetOf f) := by
    refine bijective_of_flipClosed _ ?_ ?_ ?_
    · intro i j h
      refine hinj (funext fun x => propext ?_)
      exact (mem_toFinsetOf f i x).symm.trans (h ▸ (mem_toFinsetOf f j x))
    · obtain ⟨i, hi⟩ := h0
      exact ⟨i, Finset.eq_empty_of_forall_notMem fun x hx => hi x ((mem_toFinsetOf f i x).mp hx)⟩
    · intro i a
      obtain ⟨j, hj⟩ := hflip i a
      refine ⟨j, Finset.ext fun x => ?_⟩
      rw [mem_toFinsetOf, hj x, flipAt]
      by_cases ha : a ∈ toFinsetOf f i
      · rw [if_pos ha, Finset.mem_erase, mem_toFinsetOf]
        have hai : f i a := (mem_toFinsetOf f i a).mp ha
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨h2, h1⟩
          · exact absurd (h1 ▸ hai) h2
        · rintro ⟨h1, h2⟩
          exact Or.inl ⟨h2, h1⟩
      · rw [if_neg ha, Finset.mem_insert, mem_toFinsetOf]
        have hai : ¬f i a := fun hc => ha ((mem_toFinsetOf f i a).mpr hc)
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inr h1
          · exact Or.inl h1
        · rintro (h1 | h1)
          · exact Or.inr ⟨h1, h1 ▸ hai⟩
          · exact Or.inl ⟨h1, fun hc => hai (hc ▸ h1)⟩
  refine ⟨hinj, fun T => ?_⟩
  obtain ⟨i, hi⟩ := hfin.2 (Finset.univ.filter T)
  refine ⟨i, funext fun x => propext ?_⟩
  have hx := congrArg (fun s => x ∈ s) hi
  simp only [mem_toFinsetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact iff_of_eq hx

end DescriptiveComplexity
