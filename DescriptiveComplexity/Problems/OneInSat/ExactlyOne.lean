/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Defs

/-!
# Exactly one true literal, clause by clause

`DescriptiveComplexity.OneInProper` asks every clause to have exactly one true literal.
A reduction into 1-in-SAT knows the literals of each clause it builds: a short
explicit list of distinct elements with their signs. The lemmas here turn
“exactly one true literal of this clause” (`DescriptiveComplexity.SatOcc.OneInAt`) into
the propositional statement about the truth values of those literals, for
clauses of zero to four literals, so that a correctness proof is left with
propositional reasoning only.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {M : Type} [Language.sat.Structure M]

/-- The clause `K` has exactly one true literal under `μ`. -/
def OneInAt (μ : M → Prop) (K : M) : Prop :=
  ∃ x s, OccIn K x s ∧ LitTrue μ x s ∧ ∀ y t, OccIn K y t → LitTrue μ y t → y = x ∧ t = s

theorem oneInProper_iff {μ : M → Prop} : OneInProper μ ↔ ∀ c : M, IsCl c → OneInAt μ c :=
  Iff.rfl

variable {μ : M → Prop} {K e₁ e₂ e₃ e₄ : M} {s₁ s₂ s₃ s₄ : Bool}

/-- A clause with no literal has no true one. -/
theorem not_oneInAt_of_empty (hocc : ∀ e sg, ¬OccIn K e sg) : ¬OneInAt μ K := by
  rintro ⟨x, s, hx, -⟩
  exact hocc x s hx

/-- A clause with one literal. -/
theorem oneInAt_one (hocc : ∀ e sg, OccIn K e sg ↔ e = e₁ ∧ sg = s₁) :
    OneInAt μ K ↔ LitTrue μ e₁ s₁ := by
  constructor
  · rintro ⟨x, s, hx, hT, -⟩
    obtain ⟨hxe, hse⟩ := (hocc x s).mp hx
    rw [hxe, hse] at hT
    exact hT
  · intro h
    refine ⟨e₁, s₁, (hocc _ _).mpr ⟨rfl, rfl⟩, h, fun y t hy _ => (hocc y t).mp hy⟩

/-- A clause with two literals, on distinct elements. -/
theorem oneInAt_two
    (hocc : ∀ e sg, OccIn K e sg ↔ (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂))
    (h₁₂ : e₁ ≠ e₂) :
    OneInAt μ K ↔
      (LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂) ∨ (¬LitTrue μ e₁ s₁ ∧ LitTrue μ e₂ s₂) := by
  have o₁ : OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr ⟨rfl, rfl⟩)
  constructor
  · rintro ⟨x, s, hx, hT, hu⟩
    rcases (hocc x s).mp hx with ⟨hxe, hse⟩ | ⟨hxe, hse⟩ <;> rw [hxe, hse] at hT hu
    · exact Or.inl ⟨hT, fun h => h₁₂ (hu _ _ o₂ h).1.symm⟩
    · exact Or.inr ⟨fun h => h₁₂ (hu _ _ o₁ h).1, hT⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨e₁, s₁, o₁, h1, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with h | ⟨hye, hte⟩
      · exact h
      · rw [hye, hte] at hT
        exact absurd hT h2
    · refine ⟨e₂, s₂, o₂, h2, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | h
      · rw [hye, hte] at hT
        exact absurd hT h1
      · exact h

/-- A clause with three literals, on distinct elements. -/
theorem oneInAt_three
    (hocc : ∀ e sg, OccIn K e sg ↔
      (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂) ∨ (e = e₃ ∧ sg = s₃))
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    OneInAt μ K ↔
      (LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂ ∧ ¬LitTrue μ e₃ s₃) ∨
      (¬LitTrue μ e₁ s₁ ∧ LitTrue μ e₂ s₂ ∧ ¬LitTrue μ e₃ s₃) ∨
      (¬LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂ ∧ LitTrue μ e₃ s₃) := by
  have o₁ : OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have o₃ : OccIn K e₃ s₃ := (hocc _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  constructor
  · rintro ⟨x, s, hx, hT, hu⟩
    rcases (hocc x s).mp hx with ⟨hxe, hse⟩ | ⟨hxe, hse⟩ | ⟨hxe, hse⟩ <;>
      rw [hxe, hse] at hT hu
    · exact Or.inl ⟨hT, fun h => h₁₂ (hu _ _ o₂ h).1.symm, fun h => h₁₃ (hu _ _ o₃ h).1.symm⟩
    · exact Or.inr (Or.inl ⟨fun h => h₁₂ (hu _ _ o₁ h).1, hT,
        fun h => h₂₃ (hu _ _ o₃ h).1.symm⟩)
    · exact Or.inr (Or.inr ⟨fun h => h₁₃ (hu _ _ o₁ h).1, fun h => h₂₃ (hu _ _ o₂ h).1, hT⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨e₁, s₁, o₁, h1, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with h | ⟨hye, hte⟩ | ⟨hye, hte⟩
      · exact h
      · rw [hye, hte] at hT
        exact absurd hT h2
      · rw [hye, hte] at hT
        exact absurd hT h3
    · refine ⟨e₂, s₂, o₂, h2, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | h | ⟨hye, hte⟩
      · rw [hye, hte] at hT
        exact absurd hT h1
      · exact h
      · rw [hye, hte] at hT
        exact absurd hT h3
    · refine ⟨e₃, s₃, o₃, h3, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | ⟨hye, hte⟩ | h
      · rw [hye, hte] at hT
        exact absurd hT h1
      · rw [hye, hte] at hT
        exact absurd hT h2
      · exact h

/-- A clause with four literals, on distinct elements. -/
theorem oneInAt_four
    (hocc : ∀ e sg, OccIn K e sg ↔
      (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂) ∨ (e = e₃ ∧ sg = s₃) ∨ (e = e₄ ∧ sg = s₄))
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₁₄ : e₁ ≠ e₄) (h₂₃ : e₂ ≠ e₃) (h₂₄ : e₂ ≠ e₄)
    (h₃₄ : e₃ ≠ e₄) :
    OneInAt μ K ↔
      (LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂ ∧ ¬LitTrue μ e₃ s₃ ∧ ¬LitTrue μ e₄ s₄) ∨
      (¬LitTrue μ e₁ s₁ ∧ LitTrue μ e₂ s₂ ∧ ¬LitTrue μ e₃ s₃ ∧ ¬LitTrue μ e₄ s₄) ∨
      (¬LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂ ∧ LitTrue μ e₃ s₃ ∧ ¬LitTrue μ e₄ s₄) ∨
      (¬LitTrue μ e₁ s₁ ∧ ¬LitTrue μ e₂ s₂ ∧ ¬LitTrue μ e₃ s₃ ∧ LitTrue μ e₄ s₄) := by
  have o₁ : OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have o₃ : OccIn K e₃ s₃ := (hocc _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have o₄ : OccIn K e₄ s₄ := (hocc _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  constructor
  · rintro ⟨x, s, hx, hT, hu⟩
    rcases (hocc x s).mp hx with ⟨hxe, hse⟩ | ⟨hxe, hse⟩ | ⟨hxe, hse⟩ | ⟨hxe, hse⟩ <;>
      rw [hxe, hse] at hT hu
    · exact Or.inl ⟨hT, fun h => h₁₂ (hu _ _ o₂ h).1.symm, fun h => h₁₃ (hu _ _ o₃ h).1.symm,
        fun h => h₁₄ (hu _ _ o₄ h).1.symm⟩
    · exact Or.inr (Or.inl ⟨fun h => h₁₂ (hu _ _ o₁ h).1, hT,
        fun h => h₂₃ (hu _ _ o₃ h).1.symm, fun h => h₂₄ (hu _ _ o₄ h).1.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨fun h => h₁₃ (hu _ _ o₁ h).1,
        fun h => h₂₃ (hu _ _ o₂ h).1, hT, fun h => h₃₄ (hu _ _ o₄ h).1.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨fun h => h₁₄ (hu _ _ o₁ h).1,
        fun h => h₂₄ (hu _ _ o₂ h).1, fun h => h₃₄ (hu _ _ o₃ h).1, hT⟩))
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨e₁, s₁, o₁, h1, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with h | ⟨hye, hte⟩ | ⟨hye, hte⟩ | ⟨hye, hte⟩
      · exact h
      all_goals rw [hye, hte] at hT
      exacts [absurd hT h2, absurd hT h3, absurd hT h4]
    · refine ⟨e₂, s₂, o₂, h2, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | h | ⟨hye, hte⟩ | ⟨hye, hte⟩
      · rw [hye, hte] at hT
        exact absurd hT h1
      · exact h
      all_goals rw [hye, hte] at hT
      exacts [absurd hT h3, absurd hT h4]
    · refine ⟨e₃, s₃, o₃, h3, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | ⟨hye, hte⟩ | h | ⟨hye, hte⟩
      · rw [hye, hte] at hT
        exact absurd hT h1
      · rw [hye, hte] at hT
        exact absurd hT h2
      · exact h
      · rw [hye, hte] at hT
        exact absurd hT h4
    · refine ⟨e₄, s₄, o₄, h4, fun y t hy hT => ?_⟩
      rcases (hocc y t).mp hy with ⟨hye, hte⟩ | ⟨hye, hte⟩ | ⟨hye, hte⟩ | h
      · rw [hye, hte] at hT
        exact absurd hT h1
      · rw [hye, hte] at hT
        exact absurd hT h2
      · rw [hye, hte] at hT
        exact absurd hT h3
      · exact h

end SatOcc

end DescriptiveComplexity
