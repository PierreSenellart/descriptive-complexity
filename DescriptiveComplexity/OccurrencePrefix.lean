/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceOrder

/-!
# Prefix valuations: the chain of a clause, with determined links

Splitting a wide clause `ℓ₁ ∨ ⋯ ∨ ℓₖ` into clauses of bounded width threads
fresh variables along the linear order of its literal occurrences
(`DescriptiveComplexity.OccurrenceOrder`). The plain chain of the decision reduction
leaves those variables free whenever the clause is satisfied early, which a
reduction that must preserve the *number* of solutions cannot afford.

This file isolates the determined variant, independently of any
interpretation. A **prefix valuation** (`DescriptiveComplexity.SatOcc.PrefixVal`) gives
each occurrence `(x, s)` of each clause `c` a truth value `Z c x s` such that

* `Z c x s` holds iff the literal `(x, s)` is true or `Z` holds at the
  immediately preceding occurrence – three clauses of width at most three;
* `Z` holds at the last occurrence of every clause – a unit clause;
* there is no empty clause.

Such a `Z` is then forced to be the truth of the prefix disjunction
(`DescriptiveComplexity.SatOcc.PrefixVal.iff_prefixOr`), so it carries no information
beyond the assignment; an assignment has a prefix valuation exactly when it
satisfies every clause (`DescriptiveComplexity.SatOcc.PrefixVal.exists_litTrue`,
`DescriptiveComplexity.SatOcc.prefixVal_prefixOr`).
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- An occurrence has at most one immediate predecessor. -/
theorem succOcc_left_unique {c y₁ y₂ x : A} {t₁ t₂ s : Bool}
    (h₁ : SuccOcc c y₁ t₁ x s) (h₂ : SuccOcc c y₂ t₂ x s) : y₁ = y₂ ∧ t₁ = t₂ := by
  rcases occLt_trichotomy y₁ t₁ y₂ t₂ with h | h | h
  · exact absurd ⟨h, h₂.2.2.1⟩ (h₁.2.2.2 y₂ t₂ h₂.1)
  · exact h
  · exact absurd ⟨h, h₁.2.2.1⟩ (h₂.2.2.2 y₁ t₁ h₁.1)

/-- A **prefix valuation** of the assignment `ν`: a truth value for each
occurrence of each clause, true exactly when the literal is true or the value
at the preceding occurrence is, and true at the last occurrence of every
clause; and there is no empty clause. -/
structure PrefixVal (ν : A → Prop) (Z : A → A → Bool → Prop) : Prop where
  /-- The value at an occurrence is the literal or the value before it. -/
  step : ∀ c x s, OccIn c x s →
    (Z c x s ↔ LitTrue ν x s ∨ ∃ y t, SuccOcc c y t x s ∧ Z c y t)
  /-- The value at the last occurrence of a clause is true. -/
  last : ∀ c x s, MaxOcc c x s → Z c x s
  /-- No clause is empty. -/
  nonempty : ∀ c : A, ¬EmptyCl c

variable [Finite A]

/-- **A prefix valuation is the truth of the prefix disjunctions.** -/
theorem PrefixVal.iff_prefixOr {ν : A → Prop} {Z : A → A → Bool → Prop} (h : PrefixVal ν Z)
    (c : A) : ∀ x s, OccIn c x s → (Z c x s ↔ PrefixOr ν c x s) := by
  -- one occurrence, given the claim at its predecessor (if any)
  have one : ∀ x s, OccIn c x s →
      (∀ y t, SuccOcc c y t x s → (Z c y t ↔ PrefixOr ν c y t)) →
      (Z c x s ↔ PrefixOr ν c x s) := by
    intro x s hxs IH
    rw [h.step c x s hxs, prefixOr_iff hxs, or_comm]
    refine or_congr_left ⟨?_, fun hp => ?_⟩
    · rintro ⟨y, t, hsucc, hz⟩
      exact (prefixOrStrict_succ hsucc).mpr ((IH y t hsucc).mp hz)
    · have hch : Chained c x s := ⟨hxs, fun hmin => not_prefixOrStrict_min hmin hp⟩
      obtain ⟨y, t, hsucc⟩ := exists_succOcc hch
      exact ⟨y, t, hsucc, (IH y t hsucc).mpr ((prefixOrStrict_succ hsucc).mp hp)⟩
  intro x
  refine wellFounded_lt.induction
    (C := fun x => ∀ s, OccIn c x s → (Z c x s ↔ PrefixOr ν c x s)) x ?_
  intro x IH
  have hfalse : OccIn c x false → (Z c x false ↔ PrefixOr ν c x false) := by
    intro hx
    refine one x false hx fun y t hsucc => ?_
    rcases hsucc.2.2.1 with hlt | ⟨-, hlt⟩
    · exact IH y hlt t hsucc.1
    · simp [Bool.lt_iff] at hlt
  intro s hxs
  cases s with
  | false => exact hfalse hxs
  | true =>
    refine one x true hxs fun y t hsucc => ?_
    rcases hsucc.2.2.1 with hlt | ⟨heq, hlt⟩
    · exact IH y hlt t hsucc.1
    · rw [Bool.lt_iff] at hlt
      obtain ⟨rfl, -⟩ := hlt
      subst heq
      exact hfalse hsucc.1

/-- **An assignment with a prefix valuation satisfies every clause.** -/
theorem PrefixVal.exists_litTrue {ν : A → Prop} {Z : A → A → Bool → Prop}
    (h : PrefixVal ν Z) {c : A} (hc : IsCl c) : ∃ x s, OccIn c x s ∧ LitTrue ν x s := by
  by_cases hocc : ∃ z u, OccIn c z u
  · obtain ⟨x, s, hmax⟩ := exists_maxOcc hocc
    obtain ⟨y, t, hy, -, hT⟩ :=
      (h.iff_prefixOr c x s hmax.occIn).mp (h.last c x s hmax)
    exact ⟨y, t, hy, hT⟩
  · exact absurd ⟨hc, fun z u hz => hocc ⟨z, u, hz⟩⟩ (h.nonempty c)

/-- **A satisfying assignment has a prefix valuation**: the prefix
disjunctions themselves. -/
theorem prefixVal_prefixOr {ν : A → Prop}
    (hν : ∀ c, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s) :
    PrefixVal ν (PrefixOr ν) where
  step c x s hxs := by
    rw [prefixOr_iff hxs, or_comm]
    refine or_congr_right ⟨fun hp => ?_, ?_⟩
    · have hch : Chained c x s := ⟨hxs, fun hmin => not_prefixOrStrict_min hmin hp⟩
      obtain ⟨y, t, hsucc⟩ := exists_succOcc hch
      exact ⟨y, t, hsucc, (prefixOrStrict_succ hsucc).mp hp⟩
    · rintro ⟨y, t, hsucc, hz⟩
      exact (prefixOrStrict_succ hsucc).mpr hz
  last c x s hmax := by
    obtain ⟨y, t, hy, hT⟩ := hν c hmax.occIn.isCl
    exact prefixOr_of_max hmax hy hT
  nonempty c hemp := by
    obtain ⟨y, t, hy, -⟩ := hν c hemp.1
    exact hemp.2 y t hy

end SatOcc

end DescriptiveComplexity
