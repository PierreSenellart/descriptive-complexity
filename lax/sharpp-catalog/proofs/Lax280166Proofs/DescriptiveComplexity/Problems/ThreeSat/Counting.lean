/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.ThreeSat.ToSat
import Lax280166Proofs.DescriptiveComplexity.Problems.Sat.Counting
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax799700.ThreeSat
end Lax799700.ThreeSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.ThreeSat (WidthAtMostThree)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

/-!
# #3SAT: counting the models of a 3-CNF formula

The counting version of `DescriptiveComplexity.ThreeSAT`: the number of models of a CNF
formula whose clauses have at most three literals. As for the decision
problem, the width bound is folded in: an instance violating it has no model
to count. Models are those of `DescriptiveComplexity.SharpSAT` – sets of variables of
the formula (`DescriptiveComplexity.SatModel`).

`DescriptiveComplexity.SharpThreeSAT` is in `#P`
(`DescriptiveComplexity.sharpThreeSat_mem_sharpP`), the kernel of #SAT being conjoined
with the first-order sentence stating the width bound. Its parsimonious
hardness is in `DescriptiveComplexity.Problems.ThreeSat.CountingFromSat`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The first-order kernel of #3SAT: no clause is wide, and the truth
assignment is a model. -/
noncomputable def sharpThreeSatKernel : satSOLang.Sentence :=
  ∼(LHom.sumInl.onSentence ThreeSatToSat.wideS) ⊓ sharpSatKernel

/-- Realization of the kernel of #3SAT. -/
theorem realize_sharpThreeSatKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpThreeSatKernel) ↔
      Lax799700.ThreeSat.WidthAtMostThree A ∧ Lax366625.CountingSat.SatModel A ((satAssignEquiv A).symm ρ) := by
  have h2 := realize_sharpSatKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpThreeSatKernel, Sentence.Realize, Formula.realize_inf, Formula.realize_not]
  refine and_congr ?_ h2
  have h1 : (A ⊨ (LHom.sumInl.onSentence ThreeSatToSat.wideS : satSOLang.Sentence)) ↔
      ThreeSatToSat.Wide A :=
    (LHom.realize_onSentence A LHom.sumInl ThreeSatToSat.wideS).trans
      (ThreeSatToSat.realize_wideS (A := A))
  exact (not_congr (h1.trans (ThreeSatToSat.wide_iff_not_widthAtMostThree (A := A)))).trans
    not_not

/-- The number of models of a 3-CNF formula is the number of witnesses of the
kernel of #3SAT. -/
theorem card_threeSatModel_eq_witnessCount (A : Type) [Lax904597.Sat.sat.Structure A] :
    Nat.card {ν : A → Prop // Lax799700.ThreeSat.WidthAtMostThree A ∧ Lax366625.CountingSat.SatModel A ν} =
      Lax366625.WitnessCounting.witnessCount satAssignBlock sharpThreeSatKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpThreeSatKernel, Equiv.symm_apply_apply])

/-- **#3SAT**: the number of models of a CNF formula with at most three
literals per clause; zero when some clause is wider. -/
noncomputable def SharpThreeSAT : Lax366625.CountingProblems.CountingProblem Lax904597.Sat.sat where
  Count := fun A inst =>
    Nat.card {ν : A → Prop // @Lax799700.ThreeSat.WidthAtMostThree A inst ∧ @Lax366625.CountingSat.SatModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_threeSatModel_eq_witnessCount A, card_threeSatModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpThreeSatKernel e

theorem sharpThreeSat_apply (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpThreeSAT A = Nat.card {ν : A → Prop // Lax799700.ThreeSat.WidthAtMostThree A ∧ Lax366625.CountingSat.SatModel A ν} :=
  rfl

/-- On an instance within the width bound, #3SAT is #SAT. -/
theorem sharpThreeSat_eq_sharpSat {A : Type} [Lax904597.Sat.sat.Structure A]
    (h : Lax799700.ThreeSat.WidthAtMostThree A) : SharpThreeSAT A = SharpSAT A :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right h)

/-- **The support of #3SAT is 3SAT.** -/
theorem sharpThreeSat_support_iff (A : Type) [Lax904597.Sat.sat.Structure A] [Finite A] :
    SharpThreeSAT.support A ↔ ThreeSAT A := by
  by_cases h : Lax799700.ThreeSat.WidthAtMostThree A
  · rw [CountingProblem.support_iff, sharpThreeSat_eq_sharpSat h]
    exact (sharpSat_support_iff A).trans (and_iff_right h).symm
  · refine iff_of_false ?_ fun hT => h hT.1
    rw [CountingProblem.support_iff, sharpThreeSat_apply, Nat.card_pos_iff]
    rintro ⟨⟨_, hw, -⟩, -⟩
    exact h hw

/-- **#3SAT is in `#P`.** -/
theorem sharpThreeSat_mem_sharpP : SharpThreeSAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_threeSatModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpThreeSatKernel)

end Lax280166Proofs.DescriptiveComplexity


