/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.ExactCover
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.CountingFromSat
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

namespace Lax280166.CountingSatVariants
end Lax280166.CountingSatVariants

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSatVariants (OneInModel)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

/-!
# #ExactCover is parsimoniously `#P`-complete

The reduction of 1-in-SAT to Exact Cover in
`DescriptiveComplexity.Problems.ExactCover` is parsimonious as it stands: covering the
element of a variable exactly once *is* choosing one of its two literals, so
the exact covers of the literal set system are the exactly-one models of the
formula, bijectively (`DescriptiveComplexity.ExactCoverRed.modelEquiv`). No order, no
gadget, dimension 1.

The one thing counting asks of that reduction is that only the *variables* of
the formula be ground elements: an element occurring in no clause would
otherwise be covered by either of two singleton sets.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace ExactCoverRed

open Language Structure SatOcc

/-- **The exact covers of the literal set system are the exactly-one models of
the formula**, bijectively. -/
def modelEquiv (A : Type) [Lax904597.Sat.sat.Structure A] :
    {ν : A → Prop // Lax280166.CountingSatVariants.OneInModel A ν} ≃
      {G : ecInterp.Map A → Prop //
        Lax280166.CountingSetFamilies.ExactCoverBy (Lax799700.SetFamily.SSElem (A := ecInterp.Map A)) Lax799700.SetFamily.SSFam Lax799700.SetFamily.SSMem G} where
  toFun ν := ⟨coverOf ν.1, exactCoverBy_coverOf ν.2.1⟩
  invFun G := ⟨assignOf G.1, oneInProper_assignOf G.2,
    fun x hx => (ssFam_lset true x).mp (G.2.1 _ hx)⟩
  left_inv := by
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun x => propext ⟨?_, fun h => ⟨true, x, rfl, h, hν.2 x h⟩⟩)
    rintro ⟨s, y, heq, hT, -⟩
    obtain ⟨hs, rfl⟩ := ecPt_eq_iff.mp heq
    obtain rfl : true = s := by simpa using hs
    exact hT
  right_inv := by
    rintro ⟨G, hG⟩
    refine Subtype.ext (funext fun S => propext ⟨?_, fun h => ?_⟩)
    · rintro ⟨s, x, rfl, hT, hocc⟩
      exact (exactCoverBy_lit hG hocc s).mpr hT
    · obtain ⟨s, x, hocc, rfl⟩ := ssFam_cases (hG.1 S h)
      exact ⟨s, x, rfl, (exactCoverBy_lit hG hocc s).mp h, hocc⟩

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpExactCover_map (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpExactCover (ecInterp.Map A) = SharpOneInSAT A := by
  rw [sharpExactCover_apply, sharpOneInSat_apply]
  exact (Nat.card_congr (modelEquiv A)).symm

end ExactCoverRed

open ExactCoverRed in
/-- **#1-in-SAT reduces parsimoniously to #ExactCover**, without an order. -/
noncomputable def sharpOneInSat_parsimonious_sharpExactCover :
    SharpOneInSAT ≤ᵖ SharpExactCover where
  Tag := ECTag
  dim := 1
  toInterpretation := ecInterp
  correct A _ _ _ := (sharpExactCover_map A).symm

/-- #ExactCover is parsimoniously `#P`-hard. -/
theorem sharpExactCover_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpExactCover :=
  SharpP.parsimoniousHard_of_parsimonious sharpOneInSat_parsimonious_sharpExactCover
    sharpOneInSat_sharpP_parsimoniousHard

/-- **#ExactCover is parsimoniously `#P`-complete.** -/
theorem sharpExactCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpExactCover :=
  ⟨sharpExactCover_mem_sharpP, sharpExactCover_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


