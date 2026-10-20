/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Counting.Reduction
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax859101Proofs.DescriptiveComplexity.CountingProblem
end Lax859101Proofs.DescriptiveComplexity.CountingProblem

namespace Lax859101Proofs.DescriptiveComplexity.OneCallReduction
end Lax859101Proofs.DescriptiveComplexity.OneCallReduction

namespace Lax859101Proofs.DescriptiveComplexity.SharpPDefinable
end Lax859101Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable)
end Lax859101Proofs.DescriptiveComplexity

/-!
# Restricting a counting problem to a definable class of instances

#2SAT, #HORN-SAT or #Monotone-2SAT count the models of a CNF formula *of a
certain shape*, and are `0` on every other formula. That is #SAT restricted
to a first-order definable class of instances
(`DescriptiveComplexity.CountingProblem.restrict`), and two facts carry over
from the unrestricted problem: membership in `#P`, by one more conjunct in
the kernel (`DescriptiveComplexity.SharpPDefinable.restrict`), and one-call
hardness, by any one-call reduction whose outputs all lie in the class
(`DescriptiveComplexity.OneCallReduction.restrict`).
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

open Classical in
/-- **A counting problem restricted to the instances satisfying a sentence**:
the count on those, `0` on the others. -/
noncomputable def CountingProblem.restrict (C : Lax366625.CountingProblems.CountingProblem L) (P : L.Sentence) :
    Lax366625.CountingProblems.CountingProblem L where
  Count := fun A inst => if @Sentence.Realize L A inst P then C A else 0
  iso_invariant := fun {A B} _ _ e => by
    rw [StrongHomClass.realize_sentence e P, C.iso_invariant e]

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax859101Proofs.DescriptiveComplexity.CountingProblem (restrict)

end Lax366625.CountingProblems.CountingProblem

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

theorem CountingProblem.restrict_of_realize (C : Lax366625.CountingProblems.CountingProblem L) (P : L.Sentence) (A : Type)
    [L.Structure A] (h : A ⊨ P) : C.restrict P A = C A :=
  if_pos h

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax859101Proofs.DescriptiveComplexity.CountingProblem (restrict_of_realize)

end Lax366625.CountingProblems.CountingProblem

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

theorem CountingProblem.restrict_of_not_realize (C : Lax366625.CountingProblems.CountingProblem L) (P : L.Sentence)
    (A : Type) [L.Structure A] (h : ¬A ⊨ P) : C.restrict P A = 0 :=
  if_neg h

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.CountingProblem

export Lax859101Proofs.DescriptiveComplexity.CountingProblem (restrict_of_not_realize)

end Lax366625.CountingProblems.CountingProblem

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- The sentence `P`, read over the vocabulary of a counting kernel. -/
def kernelLift (B : Lax904597.SecondOrder.SOBlock) (P : L.Sentence) : ((L.sum Language.order).sum B.lang).Sentence :=
  LHom.sumInl.onSentence (LHom.sumInl.onSentence P)

omit [L.IsRelational] in
theorem realize_kernelLift (B : Lax904597.SecondOrder.SOBlock) (P : L.Sentence) (A : Type) [L.Structure A]
    [LinearOrder A] (ρ : B.Assignment A) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (kernelLift B P)) ↔ A ⊨ P := by
  let := B.structure ρ
  rw [kernelLift, LHom.realize_onSentence, LHom.realize_onSentence]

/-- **Restriction keeps `#P`-definability**: the restricting sentence is one
more conjunct of the kernel. -/
theorem SharpPDefinable.restrict {C : Lax366625.CountingProblems.CountingProblem L} (hC : Lax366625.WitnessCounting.SharpPDefinable C)
    (P : L.Sentence) : Lax366625.WitnessCounting.SharpPDefinable (C.restrict P) := by
  obtain ⟨B, φ, hφ⟩ := hC
  refine ⟨B, φ ⊓ kernelLift B P, fun A _ _ _ _ => ?_⟩
  have hk : ∀ ρ : B.Assignment A,
      (@Sentence.Realize _ A (@sumStructure _ _ A _ (B.structure ρ)) (φ ⊓ kernelLift B P)) ↔
        (@Sentence.Realize _ A (@sumStructure _ _ A _ (B.structure ρ)) φ) ∧ A ⊨ P :=
    fun ρ => by
      let := B.structure ρ
      exact Formula.realize_inf.trans (and_congr Iff.rfl (realize_kernelLift B P A ρ))
  by_cases hP : A ⊨ P
  · rw [C.restrict_of_realize P A hP, hφ A]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun ρ => ((hk ρ).trans (and_iff_left hP)).symm)
  · rw [C.restrict_of_not_realize P A hP]
    refine (Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨ρ, hρ⟩ => hP ((hk ρ).mp hρ).2⟩)).symm

end Lax859101Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax859101Proofs.DescriptiveComplexity.SharpPDefinable (restrict)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- **A one-call reduction whose outputs all satisfy `P` is a one-call
reduction into the restriction to `P`.** -/
noncomputable def OneCallReduction.restrict {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}
    (f : C ≤ᶜ[≤] D) (P : L'.Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      f.toRelInterpretation.MapRel A ⊨ P) : C ≤ᶜ[≤] D.restrict P :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    post := f.post
    correct := fun A _ _ _ _ => by
      rw [D.restrict_of_realize P _ (h A)]
      exact f.correct A }

end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101.OneCallReductions.OneCallReduction

export Lax859101Proofs.DescriptiveComplexity.OneCallReduction (restrict)

end Lax859101.OneCallReductions.OneCallReduction

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

end Lax859101Proofs.DescriptiveComplexity


