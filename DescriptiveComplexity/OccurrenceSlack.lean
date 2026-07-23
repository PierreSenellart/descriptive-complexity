/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceFormulas
import Mathlib.Data.Set.Card

/-!
# Slack occurrences of a clause

Semantic layer shared by the two gadgets that ask a digit block to split in
half: Partition (`DescriptiveComplexity.Problems.Partition.Hardness`) and job
sequencing (`DescriptiveComplexity.Problems.JobSequencing.Hardness`). Both give a
clause of width `w` one item per occurrence *plus* one per **slack
occurrence** (`DescriptiveComplexity.SatOcc.Mid`) – an occurrence that is neither
the first nor the last one, of which there are `w − 2`. The block then totals
`w + (w − 2)`, an even number, and a balanced split takes between `1` and
`w − 1` true literals, which is exactly not-all-equal satisfaction.

Besides the predicate and its formula (`DescriptiveComplexity.SatOcc.midF`), this
file holds the two cardinality facts both gadgets need: a clause with an
occurrence has strictly fewer slack occurrences than occurrences
(`DescriptiveComplexity.SatOcc.card_midSet_lt`), and one with at least two
occurrences has exactly two fewer
(`DescriptiveComplexity.SatOcc.card_midSet_add_two`) – its first and its last.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

/-! ### Slack occurrences -/

section Mid

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- A *slack occurrence* of a clause: an occurrence that is neither the first
nor the last one. A clause of width `w ≥ 1` has `w − 2` of them (or none, if
`w = 1`), which is exactly the slack a balanced split needs. -/
def Mid (c x : A) (s : Bool) : Prop := Chained c x s ∧ ¬MaxOcc c x s

theorem Mid.occIn {c x : A} {s : Bool} (h : Mid c x s) : OccIn c x s := h.1.1

/-- A slack occurrence of `c`, as a formula. -/
noncomputable def midF {α : Type} (s : Bool) (c x : α) : satOrd.Formula α :=
  chainedF s c x ⊓ ∼(maxOccF s c x)

@[simp]
theorem realize_midF {α : Type} {v : α → A} {s : Bool} {c x : α} :
    (midF s c x).Realize v ↔ Mid (v c) (v x) s := by
  simp [midF, Mid]

end Mid

/-! ### The occurrences of a clause, and its slack -/

section Occurrences

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] {c : A}

/-- The occurrences of a clause, as a set of signed positions. -/
def OccSet (c : A) : Set (A × Bool) := {p | OccIn c p.1 p.2}

/-- The slack occurrences of a clause. -/
def MidSet (c : A) : Set (A × Bool) := {p | Mid c p.1 p.2}

omit [Finite A] in
theorem midSet_subset : MidSet c ⊆ OccSet c := fun _ hp => hp.occIn

omit [Finite A] in
/-- The first occurrence of a clause is unique. -/
theorem minOcc_unique {x y : A} {s t : Bool} (h : MinOcc c x s) (h' : MinOcc c y t) :
    (x, s) = (y, t) := by
  rcases occLt_trichotomy x s y t with hlt | ⟨hx, hs⟩ | hlt
  · exact absurd hlt (h'.2 x s h.1)
  · exact Prod.ext hx hs
  · exact absurd hlt (h.2 y t h'.1)

omit [Finite A] in
/-- The last occurrence of a clause is unique. -/
theorem maxOcc_unique {x y : A} {s t : Bool} (h : MaxOcc c x s) (h' : MaxOcc c y t) :
    (x, s) = (y, t) := by
  rcases occLt_trichotomy x s y t with hlt | ⟨hx, hs⟩ | hlt
  · exact absurd hlt (h.2 y t h'.1)
  · exact Prod.ext hx hs
  · exact absurd hlt (h'.2 x s h.1)

/-- A clause with an occurrence has strictly fewer slack occurrences than
occurrences: its first one is not one of them. -/
theorem card_midSet_lt (hne : (OccSet c).Nonempty) : (MidSet c).ncard < (OccSet c).ncard := by
  obtain ⟨⟨x, s⟩, hp⟩ := hne
  obtain ⟨y, t, hmin⟩ := exists_minOcc ⟨x, s, hp⟩
  refine Set.ncard_lt_ncard ⟨midSet_subset, fun hsub => ?_⟩ (Set.toFinite _)
  exact (hsub (show (y, t) ∈ OccSet c from hmin.1)).1.2 hmin

/-- A clause with at least two occurrences has exactly two fewer slack
occurrences: its first and its last one. -/
theorem card_midSet_add_two (h2 : 2 ≤ (OccSet c).ncard) :
    (MidSet c).ncard + 2 = (OccSet c).ncard := by
  have hne : (OccSet c).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  obtain ⟨⟨x, s⟩, hp⟩ := hne
  obtain ⟨y, t, hmin⟩ := exists_minOcc ⟨x, s, hp⟩
  obtain ⟨z, u, hmax⟩ := exists_maxOcc ⟨x, s, hp⟩
  have hne' : ((y, t) : A × Bool) ≠ (z, u) := by
    intro heq
    have hy : y = z := congrArg Prod.fst heq
    have ht : t = u := congrArg Prod.snd heq
    subst hy
    subst ht
    have hsingle : OccSet c = {(y, t)} := by
      ext ⟨v, r⟩
      simp only [OccSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
      refine ⟨fun hv => eq_of_minOcc_of_maxOcc hmin hmax hv, ?_⟩
      rintro ⟨rfl, rfl⟩
      exact hmin.1
    rw [hsingle, Set.ncard_singleton] at h2
    omega
  have hpair : ({(y, t), (z, u)} : Set (A × Bool)) ⊆ OccSet c := by
    rintro ⟨v, r⟩ hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmin.1
    · exact hmax.1
  have hdiff : MidSet c = OccSet c \ {(y, t), (z, u)} := by
    ext ⟨v, r⟩
    simp only [MidSet, OccSet, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    constructor
    · rintro ⟨⟨hocc, hmin'⟩, hmax'⟩
      refine ⟨hocc, ?_, ?_⟩
      · rintro ⟨rfl, rfl⟩
        exact hmin' hmin
      · rintro ⟨rfl, rfl⟩
        exact hmax' hmax
    · rintro ⟨hocc, hn1, hn2⟩
      refine ⟨⟨hocc, fun hmin' => hn1 ⟨congrArg Prod.fst (minOcc_unique hmin' hmin),
        congrArg Prod.snd (minOcc_unique hmin' hmin)⟩⟩,
        fun hmax' => hn2 ⟨congrArg Prod.fst (maxOcc_unique hmax' hmax),
          congrArg Prod.snd (maxOcc_unique hmax' hmax)⟩⟩
  rw [hdiff, Set.ncard_sdiff hpair (Set.toFinite _), Set.ncard_pair hne']
  omega

end Occurrences

end SatOcc

end DescriptiveComplexity
