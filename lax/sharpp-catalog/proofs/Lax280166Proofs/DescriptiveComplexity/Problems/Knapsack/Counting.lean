/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.Membership
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

namespace Lax280166.CountingKnapsacks
end Lax280166.CountingKnapsacks

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingKnapsacks (KnapsackSol)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Knapsack (BWBit BWItem BWLe BWPosn BWTarget BWTgt BWWeight)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (MaxPos)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Knapsack (binWeights)
end FirstOrder.Language

/-!
# #Knapsack: counting the solutions of a subset-sum instance

The counting version of `DescriptiveComplexity.Knapsack`: the number of sets of items
whose binary weights sum exactly to the target
(`DescriptiveComplexity.KnapsackSol`).

Membership in `#P` (`DescriptiveComplexity.sharpKnapsack_mem_sharpP`) is where a
counting definition differs from a `Σ₁` one. The certificate of
`DescriptiveComplexity.knapsack_sigmaSODefinable` carries, besides the chosen items,
the running totals and the carries of an addition walk, and a count of
certificates is a count of solutions only if a solution has *one*: the totals
and carries are forced where the walk reads them
(`DescriptiveComplexity.isChain_agree`), and the counting kernel
(`DescriptiveComplexity.sharpKnapsackKernel`) forbids them anywhere else. The
certificates are then the solutions, bijectively
(`DescriptiveComplexity.knapsackEquiv`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.Knapsack.binWeights.Structure A]

variable {A}

/-- The certificate built on a walk: the chosen items, and the totals and
carries of the walk kept only where a walk reads them. -/
def certOfWalk (S : A → Prop) (PS Cy : A → A → Prop) : knapsackGuessBlock.Assignment A :=
  fun idx => match idx with
    | .sel => fun w : Fin 1 → A => S (w 0)
    | .pS => fun w : Fin 2 → A => PS (w 0) (w 1) ∧ Lax799700.Knapsack.BWItem (w 0) ∧ Lax799700.Knapsack.BWPosn (w 1)
    | .carry => fun w : Fin 2 → A =>
        Cy (w 0) (w 1) ∧ Lax799700.Knapsack.BWItem (w 0) ∧ Lax799700.Knapsack.BWPosn (w 1) ∧ ¬Lax904597.Machines.MinPos Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem (w 0)

/-- A walk ending on the target gives a certificate of the counting kernel. -/
theorem knapsackCert_certOfWalk (hlin : Lax904597.Machines.IsLinOrd (Lax799700.Knapsack.BWLe (A := A))) {S : A → Prop}
    {PS Cy : A → A → Prop} (hSitem : ∀ i, S i → Lax799700.Knapsack.BWItem i)
    (hchain : IsChain Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWPosn S Lax799700.Knapsack.BWBit PS Cy)
    (hfinal : ∀ i p : A, Lax366625.MachineNumbers.MaxPos Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem i → Lax799700.Knapsack.BWPosn p → (PS i p ↔ Lax799700.Knapsack.BWTgt p))
    (hempty : (∀ i : A, ¬Lax799700.Knapsack.BWItem i) → ∀ p : A, Lax799700.Knapsack.BWPosn p → ¬Lax799700.Knapsack.BWTgt p) :
    KnapsackCert A (certOfWalk S PS Cy) := by
  have hnmin : ∀ {i j : A}, Lax904597.Machines.SuccPos Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem i j → ¬Lax904597.Machines.MinPos Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem j := fun hij hmin =>
    hij.2.2.2.1 (hlin.2.2.1 _ _ hij.2.2.1 (hmin.2 _ hij.1))
  refine ⟨hlin, hSitem, ?_, fun i p hi hp => ?_, hempty, fun i p h => h.2,
    fun i p h => h.2⟩
  · exact hchain.congr (fun i p hi hp => (and_iff_left ⟨hi, hp⟩).symm)
      (fun i j p hij hp => (and_iff_left ⟨hij.2.1, hp, hnmin hij⟩).symm)
  · exact (and_iff_left ⟨hi.1, hp⟩).trans (hfinal i p hi hp)

variable [Finite A]

/-- A solution has a certificate. -/
theorem exists_knapsackCert {S : A → Prop} (h : Lax280166.CountingKnapsacks.KnapsackSol A S) :
    ∃ PS Cy : A → A → Prop, IsChain Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWItem Lax799700.Knapsack.BWLe Lax799700.Knapsack.BWPosn S Lax799700.Knapsack.BWBit PS Cy ∧
      KnapsackCert A (certOfWalk S PS Cy) := by
  obtain ⟨-, hlin, hSitem, hsum⟩ := h
  obtain ⟨PS, Cy, hchain, hfinal, hempty⟩ := exists_chain_of_subsetSum hlin hSitem hsum
  exact ⟨PS, Cy, hchain, knapsackCert_certOfWalk hlin hSitem hchain hfinal hempty⟩

/-- The chosen items of a certificate are a solution. -/
theorem knapsackSol_of_cert {ρ : knapsackGuessBlock.Assignment A} (h : KnapsackCert A ρ) :
    Lax280166.CountingKnapsacks.KnapsackSol A fun i => ρ .sel ![i] := by
  obtain ⟨hlin, hsel, hchain, hfinal, hempty, -, -⟩ := h
  exact ⟨‹Finite A›, hlin, hsel, subsetSum_of_chain hlin hsel hchain hfinal hempty⟩

variable (A) in
/-- **The solutions of a subset-sum instance are the witnesses of the counting
kernel**, bijectively: a solution has exactly one certificate. -/
noncomputable def knapsackEquiv :
    {ρ : knapsackGuessBlock.Assignment A //
        @Sentence.Realize ksSOLang A
          (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) sharpKnapsackKernel} ≃
      {S : A → Prop // Lax280166.CountingKnapsacks.KnapsackSol A S} where
  toFun ρ := ⟨fun i => ρ.1 .sel ![i],
    knapsackSol_of_cert ((realize_sharpKnapsackKernel ρ.1).mp ρ.2)⟩
  invFun S := ⟨certOfWalk S.1 (exists_knapsackCert S.2).choose
      (exists_knapsackCert S.2).choose_spec.choose,
    (realize_sharpKnapsackKernel _).mpr (exists_knapsackCert S.2).choose_spec.choose_spec.2⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hcert := (realize_sharpKnapsackKernel ρ).mp hρ
    have hsol := knapsackSol_of_cert hcert
    obtain ⟨hlin, hsel, hchainρ, -, -, hpin₁, hpin₂⟩ := hcert
    have hchain := (exists_knapsackCert hsol).choose_spec.choose_spec.1
    obtain ⟨hPS, hCy⟩ := isChain_agree hlin hlin hsel hchain hchainρ
    refine Subtype.ext (funext fun idx => ?_)
    cases idx with
    | sel =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .sel) (funext fun k => by fin_cases k; rfl)
    | pS =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw : ρ .pS ![w 0, w 1] ↔ ρ .pS w :=
        iff_of_eq (congrArg (ρ .pS) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hi, hp⟩
        exact hw.mp ((hPS _ _ hi hp).mp h)
      · intro h
        obtain ⟨hi, hp⟩ := hpin₁ _ _ (hw.mpr h)
        exact ⟨(hPS _ _ hi hp).mpr (hw.mpr h), hi, hp⟩
    | carry =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw : ρ .carry ![w 0, w 1] ↔ ρ .carry w :=
        iff_of_eq (congrArg (ρ .carry) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hi, hp, hnmin⟩
        obtain ⟨j, hj⟩ := exists_predPos hlin hi hnmin
        exact hw.mp ((hCy _ _ _ hj hp).mp h)
      · intro h
        obtain ⟨hi, hp, hnmin⟩ := hpin₂ _ _ (hw.mpr h)
        obtain ⟨j, hj⟩ := exists_predPos hlin hi hnmin
        exact ⟨(hCy _ _ _ hj hp).mpr (hw.mpr h), hi, hp, hnmin⟩
  right_inv := fun _ => rfl

end Solutions

/-- **#Knapsack**: the number of sets of items whose weights sum exactly to the
target. -/
noncomputable def SharpKnapsack : Lax366625.CountingProblems.CountingProblem Lax799700.Knapsack.binWeights where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax280166.CountingKnapsacks.KnapsackSol A inst S}
  iso_invariant := fun {A B} _ _ e => by
    by_cases hfin : Finite A
    · have : Finite B := Finite.of_equiv A e.toEquiv
      rw [← Nat.card_congr (knapsackEquiv A), ← Nat.card_congr (knapsackEquiv B)]
      exact witnessCount_iso knapsackGuessBlock sharpKnapsackKernel e
    · have hB : ¬Finite B := fun h => hfin (Finite.of_equiv B e.toEquiv.symm)
      have hA0 : IsEmpty {S : A → Prop // Lax280166.CountingKnapsacks.KnapsackSol A S} := ⟨fun S => hfin S.2.1⟩
      have hB0 : IsEmpty {S : B → Prop // Lax280166.CountingKnapsacks.KnapsackSol B S} := ⟨fun S => hB S.2.1⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

theorem sharpKnapsack_apply (A : Type) [Lax799700.Knapsack.binWeights.Structure A] :
    SharpKnapsack A = Nat.card {S : A → Prop // Lax280166.CountingKnapsacks.KnapsackSol A S} :=
  rfl

/-- **The support of #Knapsack is Knapsack.** -/
theorem sharpKnapsack_support_iff (A : Type) [Lax799700.Knapsack.binWeights.Structure A] [Finite A] :
    SharpKnapsack.support A ↔ Knapsack A := by
  rw [CountingProblem.support_iff, sharpKnapsack_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨S, hfin, hlin, hS, hsum⟩, -⟩
    exact ⟨hfin, hlin, S, hS, hsum⟩
  · rintro ⟨hfin, hlin, S, hS, hsum⟩
    exact ⟨⟨⟨S, hfin, hlin, hS, hsum⟩⟩, inferInstance⟩

/-- **#Knapsack is in `#P`**: a solution has exactly one certificate of the
counting kernel. -/
theorem sharpKnapsack_mem_sharpP : SharpKnapsack ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (knapsackEquiv A))
    (sharpPDefinable_ofKernel knapsackGuessBlock sharpKnapsackKernel)

end Lax280166Proofs.DescriptiveComplexity


