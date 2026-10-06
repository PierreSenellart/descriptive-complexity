/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Defs

/-!
# The cyclic successor on a finite set

`DescriptiveComplexity.cycNext S a` is the least element of the finite set
`S` above `a`, or the least element of `S` when there is none: the successor
along `S` read as a cycle. What a track gadget needs of it: it maps `S` to
itself injectively (`DescriptiveComplexity.cycNext_injOn`), and a subset of
`S` closed under it whose complement in `S` is closed too is empty or all of
`S` (`DescriptiveComplexity.eq_empty_or_eq_of_cycNext_closed`), so that a
cycle through `S` is used entirely or not at all.
-/

namespace DescriptiveComplexity

open Finset

variable {α : Type} [LinearOrder α]

/-- The elements of `S` above `a`. -/
def above (S : Finset α) (a : α) : Finset α :=
  S.filter (a < ·)

theorem mem_above {S : Finset α} {a b : α} : b ∈ above S a ↔ b ∈ S ∧ a < b :=
  mem_filter

/-- **The cyclic successor** of `a` along `S`: the least element of `S` above
`a`, or the least element of `S` when `a` is the greatest. -/
noncomputable def cycNext (S : Finset α) (a : α) : α :=
  if h : (above S a).Nonempty then (above S a).min' h
  else if h' : S.Nonempty then S.min' h' else a

theorem cycNext_of_nonempty {S : Finset α} {a : α} (h : (above S a).Nonempty) :
    cycNext S a = (above S a).min' h := by
  rw [cycNext, dif_pos h]

theorem cycNext_of_not_nonempty {S : Finset α} {a : α} (h : ¬(above S a).Nonempty)
    (h' : S.Nonempty) : cycNext S a = S.min' h' := by
  rw [cycNext, dif_neg h, dif_pos h']

theorem cycNext_mem {S : Finset α} (hS : S.Nonempty) (a : α) : cycNext S a ∈ S := by
  by_cases h : (above S a).Nonempty
  · rw [cycNext_of_nonempty h]
    exact (mem_above.mp (min'_mem _ h)).1
  · rw [cycNext_of_not_nonempty h hS]
    exact min'_mem _ hS

/-- Nothing of `S` lies strictly between `a` and its successor. -/
theorem not_between_cycNext {S : Finset α} {a b : α} (hb : b ∈ S) (hab : a < b) :
    cycNext S a ≤ b := by
  have h : (above S a).Nonempty := ⟨b, mem_above.mpr ⟨hb, hab⟩⟩
  rw [cycNext_of_nonempty h]
  exact min'_le _ _ (mem_above.mpr ⟨hb, hab⟩)

theorem lt_cycNext_of_above {S : Finset α} {a : α} (h : (above S a).Nonempty) :
    a < cycNext S a := by
  rw [cycNext_of_nonempty h]
  exact (mem_above.mp (min'_mem _ h)).2

theorem cycNext_le_of_not_above {S : Finset α} {a : α} (ha : a ∈ S)
    (h : ¬(above S a).Nonempty) : cycNext S a ≤ a := by
  rw [cycNext_of_not_nonempty h ⟨a, ha⟩]
  exact min'_le _ _ ha

/-- An element is the greatest of `S` iff nothing of `S` is above it. -/
theorem not_above_iff {S : Finset α} {a : α} :
    ¬(above S a).Nonempty ↔ ∀ b ∈ S, b ≤ a := by
  rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact ⟨fun h b hb => not_lt.mp fun hab => h b (mem_above.mpr ⟨hb, hab⟩),
    fun h b hb => (h b (mem_above.mp hb).1).not_gt (mem_above.mp hb).2⟩

/-- The cyclic successor is injective on `S`. -/
theorem cycNext_injOn (S : Finset α) : Set.InjOn (cycNext S) S := by
  intro a ha b hb hab
  by_contra hne
  wlog hlt : a < b generalizing a b
  · exact this hb ha hab.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  have hna : (above S a).Nonempty := ⟨b, mem_above.mpr ⟨hb, hlt⟩⟩
  have h1 : cycNext S a ≤ b := not_between_cycNext hb hlt
  by_cases hnb : (above S b).Nonempty
  · exact absurd (hab ▸ lt_cycNext_of_above hnb) (not_lt.mpr h1)
  · have h2 : cycNext S b ≤ a := by
      rw [cycNext_of_not_nonempty hnb ⟨a, ha⟩]
      exact min'_le _ _ ha
    exact absurd (hab ▸ lt_cycNext_of_above hna) (not_lt.mpr h2)

/-- A subset of `S` closed under the cyclic successor cannot start below its
complement in `S`: the greatest element of `S` below the least element of the
complement is in the subset, and its successor is that least element. -/
theorem not_min_lt_of_cycNext_closed {S T : Finset α} (hTS : T ⊆ S)
    (hT : ∀ a ∈ T, cycNext S a ∈ T) (h₁ : T.Nonempty) (h₂ : (S \ T).Nonempty) :
    ¬T.min' h₁ < (S \ T).min' h₂ := by
  intro hlt
  have hbelow : (S.filter (· < (S \ T).min' h₂)).Nonempty :=
    ⟨T.min' h₁, mem_filter.mpr ⟨hTS (min'_mem _ h₁), hlt⟩⟩
  have hpS : (S.filter (· < (S \ T).min' h₂)).max' hbelow ∈ S :=
    (mem_filter.mp (max'_mem _ hbelow)).1
  have hplt : (S.filter (· < (S \ T).min' h₂)).max' hbelow < (S \ T).min' h₂ :=
    (mem_filter.mp (max'_mem _ hbelow)).2
  have hpT : (S.filter (· < (S \ T).min' h₂)).max' hbelow ∈ T := by
    by_contra hpT
    exact (not_le.mpr hplt) (min'_le _ _ (mem_sdiff.mpr ⟨hpS, hpT⟩))
  have hm₂ : (S \ T).min' h₂ ∈ S := (mem_sdiff.mp (min'_mem _ h₂)).1
  have hnext : cycNext S ((S.filter (· < (S \ T).min' h₂)).max' hbelow) = (S \ T).min' h₂ := by
    refine le_antisymm (not_between_cycNext hm₂ hplt) ?_
    have hna : (above S _).Nonempty := ⟨_, mem_above.mpr ⟨hm₂, hplt⟩⟩
    rw [cycNext_of_nonempty hna]
    refine le_min' _ _ _ fun b hb => ?_
    obtain ⟨hbS, hpb⟩ := mem_above.mp hb
    by_contra hlt'
    rw [not_le] at hlt'
    exact (not_lt.mpr (le_max' _ b (mem_filter.mpr ⟨hbS, hlt'⟩))) hpb
  exact (mem_sdiff.mp (min'_mem _ h₂)).2 (hnext ▸ hT _ hpT)

/-- **A subset of `S` closed under the cyclic successor, whose complement in
`S` is closed too, is empty or all of `S`.** -/
theorem eq_empty_or_eq_of_cycNext_closed {S T : Finset α} (hTS : T ⊆ S)
    (hT : ∀ a ∈ T, cycNext S a ∈ T) (hT' : ∀ a ∈ S, a ∉ T → cycNext S a ∉ T) :
    T = ∅ ∨ T = S := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hne, hnS⟩ := h
  have h₁ : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have h₂ : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h' => hnS (Finset.Subset.antisymm hTS h')
  have hcl : ∀ a ∈ S \ T, cycNext S a ∈ S \ T := fun a ha =>
    mem_sdiff.mpr ⟨cycNext_mem ⟨a, (mem_sdiff.mp ha).1⟩ a,
      hT' a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2⟩
  have h₁' : (S \ (S \ T)).Nonempty := by
    rw [Finset.sdiff_sdiff_eq_self hTS]
    exact h₁
  have hne' : T.min' h₁ ≠ (S \ T).min' h₂ := fun h =>
    (mem_sdiff.mp (min'_mem _ h₂)).2 (h ▸ min'_mem _ h₁)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact not_min_lt_of_cycNext_closed hTS hT h₁ h₂ hlt
  · refine not_min_lt_of_cycNext_closed Finset.sdiff_subset hcl h₂ h₁' ?_
    convert hlt using 2
    exact Finset.sdiff_sdiff_eq_self hTS

end DescriptiveComplexity
