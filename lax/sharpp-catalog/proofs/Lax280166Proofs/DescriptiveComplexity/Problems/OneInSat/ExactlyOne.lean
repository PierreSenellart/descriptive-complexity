/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.Defs
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.OneInSat
end Lax799700.OneInSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.OneInSat (OneInProper)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

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

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {M : Type} [Lax904597.Sat.sat.Structure M]

/-- The clause `K` has exactly one true literal under `μ`. -/
def OneInAt (μ : M → Prop) (K : M) : Prop :=
  ∃ x s, Lax799700.Common.SatOcc.OccIn K x s ∧ Lax799700.Common.SatOcc.LitTrue μ x s ∧ ∀ y t, Lax799700.Common.SatOcc.OccIn K y t → Lax799700.Common.SatOcc.LitTrue μ y t → y = x ∧ t = s

theorem oneInProper_iff {μ : M → Prop} : Lax799700.OneInSat.OneInProper μ ↔ ∀ c : M, Lax799700.Common.SatOcc.IsCl c → OneInAt μ c :=
  Iff.rfl

variable {μ : M → Prop} {K e₁ e₂ e₃ e₄ : M} {s₁ s₂ s₃ s₄ : Bool}

/-- A clause with no literal has no true one. -/
theorem not_oneInAt_of_empty (hocc : ∀ e sg, ¬Lax799700.Common.SatOcc.OccIn K e sg) : ¬OneInAt μ K := by
  rintro ⟨x, s, hx, -⟩
  exact hocc x s hx

/-- A clause with one literal. -/
theorem oneInAt_one (hocc : ∀ e sg, Lax799700.Common.SatOcc.OccIn K e sg ↔ e = e₁ ∧ sg = s₁) :
    OneInAt μ K ↔ Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ := by
  constructor
  · rintro ⟨x, s, hx, hT, -⟩
    obtain ⟨hxe, hse⟩ := (hocc x s).mp hx
    rw [hxe, hse] at hT
    exact hT
  · intro h
    refine ⟨e₁, s₁, (hocc _ _).mpr ⟨rfl, rfl⟩, h, fun y t hy _ => (hocc y t).mp hy⟩

/-- A clause with two literals, on distinct elements. -/
theorem oneInAt_two
    (hocc : ∀ e sg, Lax799700.Common.SatOcc.OccIn K e sg ↔ (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂))
    (h₁₂ : e₁ ≠ e₂) :
    OneInAt μ K ↔
      (Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂) ∨ (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ Lax799700.Common.SatOcc.LitTrue μ e₂ s₂) := by
  have o₁ : Lax799700.Common.SatOcc.OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : Lax799700.Common.SatOcc.OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr ⟨rfl, rfl⟩)
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
    (hocc : ∀ e sg, Lax799700.Common.SatOcc.OccIn K e sg ↔
      (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂) ∨ (e = e₃ ∧ sg = s₃))
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    OneInAt μ K ↔
      (Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₃ s₃) ∨
      (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₃ s₃) ∨
      (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ Lax799700.Common.SatOcc.LitTrue μ e₃ s₃) := by
  have o₁ : Lax799700.Common.SatOcc.OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : Lax799700.Common.SatOcc.OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have o₃ : Lax799700.Common.SatOcc.OccIn K e₃ s₃ := (hocc _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
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
    (hocc : ∀ e sg, Lax799700.Common.SatOcc.OccIn K e sg ↔
      (e = e₁ ∧ sg = s₁) ∨ (e = e₂ ∧ sg = s₂) ∨ (e = e₃ ∧ sg = s₃) ∨ (e = e₄ ∧ sg = s₄))
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₁₄ : e₁ ≠ e₄) (h₂₃ : e₂ ≠ e₃) (h₂₄ : e₂ ≠ e₄)
    (h₃₄ : e₃ ≠ e₄) :
    OneInAt μ K ↔
      (Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₃ s₃ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₄ s₄) ∨
      (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₃ s₃ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₄ s₄) ∨
      (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ Lax799700.Common.SatOcc.LitTrue μ e₃ s₃ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₄ s₄) ∨
      (¬Lax799700.Common.SatOcc.LitTrue μ e₁ s₁ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₂ s₂ ∧ ¬Lax799700.Common.SatOcc.LitTrue μ e₃ s₃ ∧ Lax799700.Common.SatOcc.LitTrue μ e₄ s₄) := by
  have o₁ : Lax799700.Common.SatOcc.OccIn K e₁ s₁ := (hocc _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  have o₂ : Lax799700.Common.SatOcc.OccIn K e₂ s₂ := (hocc _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have o₃ : Lax799700.Common.SatOcc.OccIn K e₃ s₃ := (hocc _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have o₄ : Lax799700.Common.SatOcc.OccIn K e₄ s₄ := (hocc _ _).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
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

end Lax280166Proofs.DescriptiveComplexity


