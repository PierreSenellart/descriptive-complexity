/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Membership
import Lax280166Proofs.DescriptiveComplexity.Counting.Class
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

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSetFamilies (ExactCoverBy)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.SetFamily (SSElem SSFam SSMem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.SetFamily (setSystem)
end FirstOrder.Language

/-!
# #ExactCover: counting exact covers

The counting version of `DescriptiveComplexity.ExactCover`: the number of subfamilies
of a set system covering every ground element exactly once
(`DescriptiveComplexity.ExactCoverBy`). A cover is a set of members of the family, so
nothing has to be said about the other elements of the instance.

`DescriptiveComplexity.SharpExactCover` is in `#P`
(`DescriptiveComplexity.sharpExactCover_mem_sharpP`); its parsimonious hardness is in
`DescriptiveComplexity.Problems.ExactCoverCounting`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- Subfamilies, as assignments of the guess block with an empty binary
relation. -/
def familyGuessOf {A : Type} (G : A → Prop) : familyGuessBlock.Assignment A :=
  fun i => match i with
    | .guess => fun w : Fin 1 → A => G (w 0)
    | .inj => fun _ : Fin 2 → A => False

/-- **The exact covers of a set system are the witnesses of the counting
kernel**, bijectively. -/
def exactCoverEquiv (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    {ρ : familyGuessBlock.Assignment A //
        @Sentence.Realize setFamilySOLang A
          (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) sharpExactCoverKernel} ≃
      {G : A → Prop // Lax280166.CountingSetFamilies.ExactCoverBy (Lax799700.SetFamily.SSElem (A := A)) Lax799700.SetFamily.SSFam Lax799700.SetFamily.SSMem G} where
  toFun ρ := ⟨fun s => ρ.1 .guess ![s], ((realize_sharpExactCoverKernel ρ.1).mp ρ.2).1⟩
  invFun G := ⟨familyGuessOf G.1,
    (realize_sharpExactCoverKernel _).mpr ⟨G.2, fun _ _ h => h⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hinj := ((realize_sharpExactCoverKernel ρ).mp hρ).2
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | guess =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .guess) (funext fun k => by fin_cases k; rfl)
    | inj =>
      refine funext fun (w : Fin 2 → A) => propext ⟨fun h => h.elim, fun h => ?_⟩
      refine hinj (w 0) (w 1) ?_
      exact (congrArg (ρ .inj) (funext fun k => by fin_cases k <;> rfl)).mpr h
  right_inv := fun _ => rfl

/-- **#ExactCover**: the number of exact covers of a set system. -/
noncomputable def SharpExactCover : Lax366625.CountingProblems.CountingProblem Lax799700.SetFamily.setSystem where
  Count := fun A inst =>
    Nat.card {G : A → Prop //
      Lax280166.CountingSetFamilies.ExactCoverBy (@Lax799700.SetFamily.SSElem A inst) (@Lax799700.SetFamily.SSFam A inst) (@Lax799700.SetFamily.SSMem A inst) G}
  iso_invariant := fun {A B} _ _ e => by
    rw [← Nat.card_congr (exactCoverEquiv A), ← Nat.card_congr (exactCoverEquiv B)]
    exact witnessCount_iso familyGuessBlock sharpExactCoverKernel e

theorem sharpExactCover_apply (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpExactCover A =
      Nat.card {G : A → Prop // Lax280166.CountingSetFamilies.ExactCoverBy (Lax799700.SetFamily.SSElem (A := A)) Lax799700.SetFamily.SSFam Lax799700.SetFamily.SSMem G} :=
  rfl

/-- **The support of #ExactCover is Exact Cover.** -/
theorem sharpExactCover_support_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpExactCover.support A ↔ ExactCover A := by
  rw [CountingProblem.support_iff, sharpExactCover_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨G, hG⟩, _⟩ => ⟨G, hG⟩, fun ⟨G, hG⟩ => ⟨⟨⟨G, hG⟩⟩, inferInstance⟩⟩

/-- **#ExactCover is in `#P`.** -/
theorem sharpExactCover_mem_sharpP : SharpExactCover ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (exactCoverEquiv A))
    (sharpPDefinable_ofKernel familyGuessBlock sharpExactCoverKernel)

end Lax280166Proofs.DescriptiveComplexity


