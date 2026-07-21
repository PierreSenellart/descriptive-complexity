/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Literal occurrences of a CNF structure, ordered

Semantic layer for the reduction from SAT to 3-colorability: literal
*occurrences* of a `Language.sat`-structure, and their traversal along a
linear order of the universe.

An occurrence of a clause `c` is a pair `(x, s)` with `x` an element and
`s : Bool` a sign, such that `x` occurs in `c` with sign `s` (`OccIn`).
Occurrences are ordered lexicographically (variable first, then sign,
`false < true`): `occLt`. On a finite universe every clause with at least one
occurrence has a first (`MinOcc`) and last (`MaxOcc`) occurrence, and every
occurrence that is not first has an immediate predecessor (`SuccOcc`,
`exists_succOcc`). These are the facts needed to thread an OR-gadget chain
along the occurrences of each clause.

Everything in this file is first-order definable over
`Language.sat.sum Language.order`; the corresponding formulas and their
realization lemmas are in `FOReduction.SatToThreeCol`.
-/

namespace FirstOrder

namespace SatToCol

open Language Structure

variable {A : Type} [Language.sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses, so that stray
`posIn`/`negIn` facts on non-clause elements do not create gadgets. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

@[simp] theorem occIn_true {c x : A} : OccIn c x true ↔ IsCl c ∧ PosIn c x := Iff.rfl

@[simp] theorem occIn_false {c x : A} : OccIn c x false ↔ IsCl c ∧ NegIn c x := Iff.rfl

theorem OccIn.isCl {c x : A} {s : Bool} (h : OccIn c x s) : IsCl c := h.1

/-- `c` is a clause with no literal: an unsatisfiable clause. -/
def EmptyCl (c : A) : Prop := IsCl c ∧ ∀ x s, ¬OccIn c x s

section Order

variable [LinearOrder A]

/-- Strict lexicographic order on occurrence positions: variable first, then
sign (with `false < true`). -/
def occLt (x : A) (s : Bool) (y : A) (t : Bool) : Prop :=
  x < y ∨ (x = y ∧ s < t)

omit [Language.sat.Structure A] in
theorem occLt_irrefl (x : A) (s : Bool) : ¬occLt x s x s := by
  simp [occLt]

omit [Language.sat.Structure A] in
theorem occLt_trans {x y z : A} {s t u : Bool} (h₁ : occLt x s y t) (h₂ : occLt y t z u) :
    occLt x s z u := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl h₁
  · exact Or.inl h₂
  · exact Or.inr ⟨rfl, h₁.trans h₂⟩

omit [Language.sat.Structure A] in
theorem occLt_asymm {x y : A} {s t : Bool} (h : occLt x s y t) : ¬occLt y t x s :=
  fun h' => occLt_irrefl x s (occLt_trans h h')

omit [Language.sat.Structure A] in
theorem occLt_trichotomy (x : A) (s : Bool) (y : A) (t : Bool) :
    occLt x s y t ∨ (x = y ∧ s = t) ∨ occLt y t x s := by
  rcases lt_trichotomy x y with h | rfl | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy s t with h | rfl | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- `(x, s)` is the first occurrence of the clause `c`. -/
def MinOcc (c x : A) (s : Bool) : Prop :=
  OccIn c x s ∧ ∀ y t, OccIn c y t → ¬occLt y t x s

/-- `(x, s)` is the last occurrence of the clause `c`. -/
def MaxOcc (c x : A) (s : Bool) : Prop :=
  OccIn c x s ∧ ∀ y t, OccIn c y t → ¬occLt x s y t

/-- `(x, s)` is an occurrence of `c` immediately preceded by the occurrence
`(y, t)`. -/
def SuccOcc (c y : A) (t : Bool) (x : A) (s : Bool) : Prop :=
  OccIn c y t ∧ OccIn c x s ∧ occLt y t x s ∧
    ∀ z u, OccIn c z u → ¬(occLt y t z u ∧ occLt z u x s)

/-- `(x, s)` is an occurrence of `c` that is not the first one: an OR-gate of
the chain of `c` sits on it. -/
def Chained (c x : A) (s : Bool) : Prop := OccIn c x s ∧ ¬MinOcc c x s

theorem MinOcc.occIn {c x : A} {s : Bool} (h : MinOcc c x s) : OccIn c x s := h.1

theorem MaxOcc.occIn {c x : A} {s : Bool} (h : MaxOcc c x s) : OccIn c x s := h.1

theorem Chained.occIn {c x : A} {s : Bool} (h : Chained c x s) : OccIn c x s := h.1

/-- If `(x, s)` is both the first and last occurrence of `c`, it is the only
one. -/
theorem eq_of_minOcc_of_maxOcc {c x z : A} {s u : Bool} (hmin : MinOcc c x s)
    (hmax : MaxOcc c x s) (hz : OccIn c z u) : z = x ∧ u = s := by
  rcases occLt_trichotomy z u x s with h | h | h
  · exact absurd h (hmin.2 z u hz)
  · exact h
  · exact absurd h (hmax.2 z u hz)

/-- Occurrences up to the immediate predecessor `(y, t)` of `(x, s)` are
exactly the occurrences strictly before `(x, s)`. -/
theorem succOcc_occLt_iff {c y x z : A} {t s u : Bool} (hsucc : SuccOcc c y t x s)
    (hz : OccIn c z u) : occLt z u x s ↔ occLt z u y t ∨ (z = y ∧ u = t) := by
  constructor
  · intro h
    rcases occLt_trichotomy z u y t with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd ⟨h', h⟩ (hsucc.2.2.2 z u hz)
  · rintro (h | ⟨rfl, rfl⟩)
    · exact occLt_trans h hsucc.2.2.1
    · exact hsucc.2.2.1

variable [Finite A]

/-- A clause with an occurrence has a first occurrence. -/
theorem exists_minOcc {c : A} (h : ∃ x s, OccIn c x s) : ∃ x s, MinOcc c x s := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    Set.exists_min_image {x : A | ∃ s, OccIn c x s} id (Set.toFinite _)
      (by obtain ⟨x, s, hxs⟩ := h; exact ⟨x, s, hxs⟩)
  by_cases h0 : OccIn c x₀ false
  · refine ⟨x₀, false, h0, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin y ⟨t, hyt⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀⟩ := hx₀
    have hs₀' : s₀ = true := by
      cases s₀ with
      | false => exact absurd hs₀ h0
      | true => rfl
    subst hs₀'
    refine ⟨x₀, true, hs₀, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmin y ⟨t, hyt⟩) (not_le.mpr hlt)
    · have ht : t = false := by
        cases t with
        | false => rfl
        | true => exact absurd hlt (by simp)
      exact h0 (ht ▸ hyt)

/-- A clause with an occurrence has a last occurrence. -/
theorem exists_maxOcc {c : A} (h : ∃ x s, OccIn c x s) : ∃ x s, MaxOcc c x s := by
  obtain ⟨x₀, hx₀, hmax⟩ :=
    Set.exists_max_image {x : A | ∃ s, OccIn c x s} id (Set.toFinite _)
      (by obtain ⟨x, s, hxs⟩ := h; exact ⟨x, s, hxs⟩)
  by_cases h1 : OccIn c x₀ true
  · refine ⟨x₀, true, h1, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax y ⟨t, hyt⟩) (not_le.mpr hlt)
    · exact absurd hlt (by simp)
  · obtain ⟨s₀, hs₀⟩ := hx₀
    have hs₀' : s₀ = false := by
      cases s₀ with
      | false => rfl
      | true => exact absurd hs₀ h1
    subst hs₀'
    refine ⟨x₀, false, hs₀, fun y t hyt => ?_⟩
    rintro (hlt | ⟨rfl, hlt⟩)
    · exact absurd (hmax y ⟨t, hyt⟩) (not_le.mpr hlt)
    · have ht : t = true := by
        cases t with
        | false => exact absurd hlt (by simp)
        | true => rfl
      exact h1 (ht ▸ hyt)

/-- A non-first occurrence has an immediate predecessor. -/
theorem exists_succOcc {c x : A} {s : Bool} (h : Chained c x s) :
    ∃ y t, SuccOcc c y t x s := by
  have hne : ∃ y, ∃ t, OccIn c y t ∧ occLt y t x s := by
    by_contra hne
    push Not at hne
    exact h.2 ⟨h.1, fun y t hyt hlt => hne y t hyt hlt⟩
  obtain ⟨y₀, hy₀, hmax⟩ :=
    Set.exists_max_image {y : A | ∃ t, OccIn c y t ∧ occLt y t x s} id (Set.toFinite _) hne
  by_cases h1 : OccIn c y₀ true ∧ occLt y₀ true x s
  · refine ⟨y₀, true, h1.1, h.1, h1.2, fun z u hz => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax z ⟨u, hz, hlt₂⟩) (not_le.mpr hlt₁)
    · exact absurd hlt₁ (by simp)
  · obtain ⟨t₀, ht₀, hlt₀⟩ := hy₀
    have ht₀' : t₀ = false := by
      cases t₀ with
      | false => rfl
      | true => exact absurd ⟨ht₀, hlt₀⟩ h1
    subst ht₀'
    refine ⟨y₀, false, ht₀, h.1, hlt₀, fun z u hz => ?_⟩
    rintro ⟨hlt₁ | ⟨rfl, hlt₁⟩, hlt₂⟩
    · exact absurd (hmax z ⟨u, hz, hlt₂⟩) (not_le.mpr hlt₁)
    · have hu : u = true := by
        cases u with
        | false => exact absurd hlt₁ (by simp)
        | true => rfl
      subst hu
      exact h1 ⟨hz, hlt₂⟩

end Order

end SatToCol

end FirstOrder
