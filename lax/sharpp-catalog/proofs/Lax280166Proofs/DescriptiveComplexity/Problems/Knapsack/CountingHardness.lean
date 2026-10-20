/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.Hardness
import Lax280166Proofs.DescriptiveComplexity.Problems.ExactCoverCounting
import Lax280166Proofs.DescriptiveComplexity.Counting.Subtractive
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

namespace Lax280166.CountingKnapsacks
end Lax280166.CountingKnapsacks

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingKnapsacks (KnapsackSol)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem)
end FirstOrder.Language

/-!
# #Knapsack is parsimoniously `#P`-complete

Karp's reduction of Exact Cover to Knapsack
(`DescriptiveComplexity.Problems.Knapsack.Hardness`) is parsimonious as it stands. Its
items are the sets of the family, one each, so a set of items *is* a subfamily;
and the weights of a set of items sum to the target exactly when the subfamily
is an exact cover, the digit of the block of a ground element counting the
chosen sets that contain it. Hence the solutions of the interpreted instance
are the exact covers of the set system, bijectively
(`DescriptiveComplexity.KnapRed.solEquiv`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace KnapRed

open Language Structure

variable (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The solutions of the interpreted subset-sum instance are the exact covers
of the set system**, bijectively. -/
def solEquiv {a₀ : A} (ha₀ : IsBot a₀) :
    {G : A → Prop // Lax280166.CountingSetFamilies.ExactCoverBy (Lax799700.SetFamily.SSElem (A := A)) Lax799700.SetFamily.SSFam Lax799700.SetFamily.SSMem G} ≃
      {S : kInterp.Map A → Prop // Lax280166.CountingKnapsacks.KnapsackSol (kInterp.Map A) S} where
  toFun G := ⟨itemsOf a₀ G.1, kInterp.map_finite A, isLinOrd_bwLe,
    (subsetSum_itemsOf ha₀ G.2).1, (subsetSum_itemsOf ha₀ G.2).2⟩
  invFun S := ⟨coverOfItems a₀ S.1, exactCoverBy_coverOfItems ha₀ S.2.2.2.1 S.2.2.2.2⟩
  left_inv := by
    rintro ⟨G, hG⟩
    refine Subtype.ext (funext fun s => propext ⟨?_, fun h => ⟨s, h, rfl⟩⟩)
    rintro ⟨s', hs', heq⟩
    rw [kItem_injective a₀ heq]
    exact hs'
  right_inv := by
    rintro ⟨S, hS⟩
    refine Subtype.ext (funext fun i => propext ⟨?_, fun h => ?_⟩)
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · have hi := (eq_kItem ha₀ (hS.2.2.1 i h)).1
      exact ⟨i.2 0, show S (kItem a₀ (i.2 0)) by rw [← hi]; exact h, hi⟩

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpKnapsack_map : SharpKnapsack (kInterp.Map A) = SharpExactCover A := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpKnapsack_apply, sharpExactCover_apply]
  exact (Nat.card_congr (solEquiv A ha₀)).symm

end KnapRed

open KnapRed in
/-- **#ExactCover reduces parsimoniously to #Knapsack.** -/
noncomputable def sharpExactCover_ordered_parsimonious_sharpKnapsack :
    SharpExactCover ≤ᵖ[≤] SharpKnapsack where
  Tag := KTag
  dim := 2
  toInterpretation := kInterp
  correct A _ _ _ _ := (sharpKnapsack_map A).symm

/-- #Knapsack is parsimoniously `#P`-hard. -/
theorem sharpKnapsack_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpKnapsack :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpExactCover_ordered_parsimonious_sharpKnapsack sharpExactCover_sharpP_parsimoniousHard

/-- **#Knapsack is parsimoniously `#P`-complete**, its weights being written in
binary. -/
theorem sharpKnapsack_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpKnapsack :=
  ⟨sharpKnapsack_mem_sharpP, sharpKnapsack_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


