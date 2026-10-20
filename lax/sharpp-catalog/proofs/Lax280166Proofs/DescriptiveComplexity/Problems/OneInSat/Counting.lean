/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.Defs
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

namespace Lax280166.CountingSatVariants
end Lax280166.CountingSatVariants

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.OneInSat
end Lax799700.OneInSat

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSatVariants (OneInModel)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.OneInSat (OneInProper)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# #1-in-SAT: counting exactly-one models

The counting version of `DescriptiveComplexity.OneInSAT`: the number of assignments
giving every clause *exactly one* true literal. As for #SAT, an assignment is
a set of variables of the formula – of elements occurring in a clause
(`DescriptiveComplexity.OneInModel`).

`DescriptiveComplexity.SharpOneInSAT` is in `#P`
(`DescriptiveComplexity.sharpOneInSat_mem_sharpP`); its parsimonious hardness is in
`DescriptiveComplexity.Problems.OneInSat.CountingFromSat`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-- The first-order kernel of #1-in-SAT. -/
noncomputable def sharpOneInKernel : satSOLang.Sentence :=
  oneInKernel ⊓ satVarKernel

/-- Realization of the kernel of #1-in-SAT. -/
theorem realize_sharpOneInKernel {A : Type} [Lax904597.Sat.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpOneInKernel) ↔
      Lax280166.CountingSatVariants.OneInModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_oneInKernel_iff_oneInProper ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpOneInKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

/-- The number of exactly-one models is the number of witnesses of the
kernel. -/
theorem card_oneInModel_eq_witnessCount (A : Type) [Lax904597.Sat.sat.Structure A] :
    Nat.card {ν : A → Prop // Lax280166.CountingSatVariants.OneInModel A ν} =
      Lax366625.WitnessCounting.witnessCount satAssignBlock sharpOneInKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpOneInKernel, Equiv.symm_apply_apply])

/-- **#1-in-SAT**: the number of assignments of the variables of a CNF formula
giving every clause exactly one true literal. -/
noncomputable def SharpOneInSAT : Lax366625.CountingProblems.CountingProblem Lax904597.Sat.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @Lax280166.CountingSatVariants.OneInModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_oneInModel_eq_witnessCount A, card_oneInModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpOneInKernel e

theorem sharpOneInSat_apply (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpOneInSAT A = Nat.card {ν : A → Prop // Lax280166.CountingSatVariants.OneInModel A ν} :=
  rfl

/-- An exactly-one proper assignment restricts to an exactly-one model: only
its values at the variables of the formula matter. -/
theorem oneInModel_restrict {A : Type} [Lax904597.Sat.sat.Structure A] {ν : A → Prop}
    (h : Lax799700.OneInSat.OneInProper ν) : Lax280166.CountingSatVariants.OneInModel A fun x => ν x ∧ Lax366625.CountingSat.SatOccurs A x := by
  have hlit : ∀ c y t, Lax799700.Common.SatOcc.OccIn c y t →
      (Lax799700.Common.SatOcc.LitTrue (fun x => ν x ∧ Lax366625.CountingSat.SatOccurs A x) y t ↔ Lax799700.Common.SatOcc.LitTrue ν y t) := by
    intro c y t hy
    have hocc : Lax366625.CountingSat.SatOccurs A y := by
      cases t
      · exact ⟨c, hy.1, Or.inr hy.2⟩
      · exact ⟨c, hy.1, Or.inl hy.2⟩
    cases t
    · exact not_congr (and_iff_left hocc)
    · exact and_iff_left hocc
  refine ⟨fun c hc => ?_, fun x hx => hx.2⟩
  obtain ⟨x, s, hx, hT, huniq⟩ := h c hc
  exact ⟨x, s, hx, (hlit c x s hx).mpr hT,
    fun y t hy hTy => huniq y t hy ((hlit c y t hy).mp hTy)⟩

/-- **The support of #1-in-SAT is 1-in-SAT.** -/
theorem sharpOneInSat_support_iff (A : Type) [Lax904597.Sat.sat.Structure A] [Finite A] :
    SharpOneInSAT.support A ↔ OneInSAT A := by
  rw [CountingProblem.support_iff, sharpOneInSat_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨ν, hν⟩, -⟩
    exact ⟨ν, hν.1⟩
  · rintro ⟨ν, hν⟩
    exact ⟨⟨⟨_, oneInModel_restrict hν⟩⟩, inferInstance⟩

/-- **#1-in-SAT is in `#P`.** -/
theorem sharpOneInSat_mem_sharpP : SharpOneInSAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_oneInModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpOneInKernel)

end Lax280166Proofs.DescriptiveComplexity


