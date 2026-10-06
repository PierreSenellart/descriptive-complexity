/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Hardness
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.CountingHardness
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

namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingKnapsacks (KnapsackSol ZeroOneSol)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Knapsack (binWeights)
end FirstOrder.Language

/-!
# #0-1 integer programming is parsimoniously `#P`-complete

The reduction of Knapsack to 0-1 integer programming
(`DescriptiveComplexity.Problems.ZeroOneIP.Hardness`) reads a subset-sum instance as a
program with one equation: the items become the columns, and the interpreted
universe is a copy of the input. A set of items is a `0-1` vector, and it sums
to the target exactly when the equation holds, so the solutions correspond
bijectively (`DescriptiveComplexity.IPRed.solEquiv`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace IPRed

open Language Structure

variable (A : Type) [Lax799700.Knapsack.binWeights.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The solutions of the one-equation program are the solutions of the
subset-sum instance**, bijectively. -/
def solEquiv {a₀ : A} (ha₀ : IsBot a₀) :
    {S : A → Prop // Lax280166.CountingKnapsacks.KnapsackSol A S} ≃
      {x : ipInterp.Map A → Prop // Lax280166.CountingKnapsacks.ZeroOneSol (ipInterp.Map A) x} where
  toFun S := ⟨colsOf S.1, ipInterp.map_finite A, isLinOrd_ipLe S.2.2.1,
    (zeroOneSol_colsOf S.2.2.2.1 S.2.2.2.2).1, (zeroOneSol_colsOf S.2.2.2.1 S.2.2.2.2).2⟩
  invFun x := ⟨itemsOfCols x.1, ‹Finite A›, isLinOrd_bwLe_of_ipLe x.2.2.1,
    (subsetSum_itemsOfCols ha₀ x.2.2.2.1 x.2.2.2.2).1,
    (subsetSum_itemsOfCols ha₀ x.2.2.2.1 x.2.2.2.2).2⟩
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨x, hx⟩
    refine Subtype.ext (funext fun q => ?_)
    change x (ipPt (q.2 0)) = x q
    rw [← ipPt_surj q]

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpZeroOneIP_map : SharpZeroOneIP (ipInterp.Map A) = SharpKnapsack A := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpZeroOneIP_apply, sharpKnapsack_apply]
  exact (Nat.card_congr (solEquiv A ha₀)).symm

end IPRed

open IPRed in
/-- **#Knapsack reduces parsimoniously to #0-1 integer programming.** -/
noncomputable def sharpKnapsack_ordered_parsimonious_sharpZeroOneIP :
    SharpKnapsack ≤ᵖ[≤] SharpZeroOneIP where
  Tag := Unit
  dim := 1
  toInterpretation := ipInterp
  correct A _ _ _ _ := (sharpZeroOneIP_map A).symm

/-- #0-1 integer programming is parsimoniously `#P`-hard. -/
theorem sharpZeroOneIP_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpZeroOneIP :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpKnapsack_ordered_parsimonious_sharpZeroOneIP sharpKnapsack_sharpP_parsimoniousHard

/-- **#0-1 integer programming is parsimoniously `#P`-complete**, its entries
being written in binary. -/
theorem sharpZeroOneIP_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpZeroOneIP :=
  ⟨sharpZeroOneIP_mem_sharpP, sharpZeroOneIP_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


