/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Membership
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

namespace Lax799700.ZeroOneIP
end Lax799700.ZeroOneIP

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingKnapsacks (ZeroOneSol)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd MinPos SuccPos)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.ZeroOneIP (IPCoef IPCoefVal IPCol IPLe IPPosn IPRhs IPRhsVal IPRow)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (MaxPos)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.ZeroOneIP (zeroOneIP)
end FirstOrder.Language

/-!
# #0-1 integer programming: counting the `0-1` solutions

The counting version of `DescriptiveComplexity.ZeroOneIP`: the number of `0-1` vectors
`x` with `C x = d` (`DescriptiveComplexity.ZeroOneSol`), the entries being written in
binary.

Membership in `#P` (`DescriptiveComplexity.sharpZeroOneIP_mem_sharpP`) is Knapsack's
argument once per row (`DescriptiveComplexity.Problems.Knapsack.Counting`): the walks
of a certificate are forced where they are read
(`DescriptiveComplexity.isChain_agree`) and forbidden elsewhere by the counting kernel,
so a solution has exactly one certificate
(`DescriptiveComplexity.zeroOneIPEquiv`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A]

variable {A}

/-- The certificate built on a family of walks: the chosen columns, and the
totals and carries of each row's walk kept only where a walk reads them. -/
def certOfWalks (x : A → Prop) (PS Cy : A → A → A → Prop) :
    zeroOneIPGuessBlock.Assignment A :=
  fun idx => match idx with
    | .x => fun w : Fin 1 → A => x (w 0)
    | .pS => fun w : Fin 3 → A =>
        PS (w 0) (w 1) (w 2) ∧ Lax799700.ZeroOneIP.IPRow (w 0) ∧ Lax799700.ZeroOneIP.IPCol (w 1) ∧ Lax799700.ZeroOneIP.IPPosn (w 2)
    | .cy => fun w : Fin 3 → A =>
        Cy (w 0) (w 1) (w 2) ∧ Lax799700.ZeroOneIP.IPRow (w 0) ∧ Lax799700.ZeroOneIP.IPCol (w 1) ∧ Lax799700.ZeroOneIP.IPPosn (w 2) ∧
          ¬Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol (w 1)

/-- Walks ending on the right-hand sides give a certificate of the counting
kernel. -/
theorem zeroOneIPCert_certOfWalks (hlin : Lax904597.Machines.IsLinOrd (Lax799700.ZeroOneIP.IPLe (A := A))) {x : A → Prop}
    {PS Cy : A → A → A → Prop} (hx : ∀ j, x j → Lax799700.ZeroOneIP.IPCol j)
    (hchains : ∀ r : A, Lax799700.ZeroOneIP.IPRow r → IsChain Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn x (Lax799700.ZeroOneIP.IPCoef r) (PS r) (Cy r))
    (hfin : ∀ r j p : A, Lax799700.ZeroOneIP.IPRow r → Lax366625.MachineNumbers.MaxPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol j → Lax799700.ZeroOneIP.IPPosn p → (PS r j p ↔ Lax799700.ZeroOneIP.IPRhs r p))
    (hemp : (∀ j : A, ¬Lax799700.ZeroOneIP.IPCol j) → ∀ r p : A, Lax799700.ZeroOneIP.IPRow r → Lax799700.ZeroOneIP.IPPosn p → ¬Lax799700.ZeroOneIP.IPRhs r p) :
    ZeroOneIPCert A (certOfWalks x PS Cy) := by
  have hnmin : ∀ {i j : A}, Lax904597.Machines.SuccPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol i j → ¬Lax904597.Machines.MinPos Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol j := fun hij hmin =>
    hij.2.2.2.1 (hlin.2.2.1 _ _ hij.2.2.1 (hmin.2 _ hij.1))
  refine ⟨hlin, hx, fun r hr => ?_, fun r j p hr hj hp => ?_, hemp, fun r j p h => h.2,
    fun r j p h => h.2⟩
  · exact (hchains r hr).congr (fun j p hj hp => (and_iff_left ⟨hr, hj, hp⟩).symm)
      (fun i j p hij hp => (and_iff_left ⟨hr, hij.2.1, hp, hnmin hij⟩).symm)
  · exact (and_iff_left ⟨hr, hj.1, hp⟩).trans (hfin r j p hr hj hp)

variable [Finite A]

/-- A solution has a certificate. -/
theorem exists_zeroOneIPCert {x : A → Prop} (h : Lax280166.CountingKnapsacks.ZeroOneSol A x) :
    ∃ PS Cy : A → A → A → Prop,
      (∀ r : A, Lax799700.ZeroOneIP.IPRow r → IsChain Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPCol Lax799700.ZeroOneIP.IPLe Lax799700.ZeroOneIP.IPPosn x (Lax799700.ZeroOneIP.IPCoef r) (PS r) (Cy r)) ∧
      ZeroOneIPCert A (certOfWalks x PS Cy) := by
  obtain ⟨-, hlin, hx, hsum⟩ := h
  obtain ⟨PS, Cy, hchains, hfin, hemp⟩ := exists_chains_of_zeroOneSol hlin hx hsum
  exact ⟨PS, Cy, hchains, zeroOneIPCert_certOfWalks hlin hx hchains hfin hemp⟩

/-- The chosen columns of a certificate are a solution. -/
theorem zeroOneSol_of_cert {ρ : zeroOneIPGuessBlock.Assignment A} (h : ZeroOneIPCert A ρ) :
    Lax280166.CountingKnapsacks.ZeroOneSol A fun j => ρ .x ![j] := by
  obtain ⟨hlin, hx, hchains, hfin, hemp, -, -⟩ := h
  exact ⟨‹Finite A›, hlin, hx, zeroOneSol_of_chains hlin hx hchains hfin hemp⟩

variable (A) in
/-- **The solutions of a 0-1 integer program are the witnesses of the counting
kernel**, bijectively: a solution has exactly one certificate. -/
noncomputable def zeroOneIPEquiv :
    {ρ : zeroOneIPGuessBlock.Assignment A //
        @Sentence.Realize zoSOLang A
          (@sumStructure _ _ A _ (zeroOneIPGuessBlock.structure ρ)) sharpZeroOneIPKernel} ≃
      {x : A → Prop // Lax280166.CountingKnapsacks.ZeroOneSol A x} where
  toFun ρ := ⟨fun j => ρ.1 .x ![j],
    zeroOneSol_of_cert ((realize_sharpZeroOneIPKernel ρ.1).mp ρ.2)⟩
  invFun x := ⟨certOfWalks x.1 (exists_zeroOneIPCert x.2).choose
      (exists_zeroOneIPCert x.2).choose_spec.choose,
    (realize_sharpZeroOneIPKernel _).mpr (exists_zeroOneIPCert x.2).choose_spec.choose_spec.2⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hcert := (realize_sharpZeroOneIPKernel ρ).mp hρ
    have hsol := zeroOneSol_of_cert hcert
    obtain ⟨hlin, hx, hchainρ, -, -, hpin₁, hpin₂⟩ := hcert
    have hchain := (exists_zeroOneIPCert hsol).choose_spec.choose_spec.1
    refine Subtype.ext (funext fun idx => ?_)
    cases idx with
    | x =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .x) (funext fun k => by fin_cases k; rfl)
    | pS =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw : ρ .pS ![w 0, w 1, w 2] ↔ ρ .pS w :=
        iff_of_eq (congrArg (ρ .pS) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hr, hj, hp⟩
        exact hw.mp (((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).1 _ _ hj hp).mp h)
      · intro h
        obtain ⟨hr, hj, hp⟩ := hpin₁ _ _ _ (hw.mpr h)
        exact ⟨((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).1 _ _ hj hp).mpr
          (hw.mpr h), hr, hj, hp⟩
    | cy =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw : ρ .cy ![w 0, w 1, w 2] ↔ ρ .cy w :=
        iff_of_eq (congrArg (ρ .cy) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hr, hj, hp, hnmin⟩
        obtain ⟨i, hi⟩ := exists_predPos hlin hj hnmin
        exact hw.mp
          (((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).2 _ _ _ hi hp).mp h)
      · intro h
        obtain ⟨hr, hj, hp, hnmin⟩ := hpin₂ _ _ _ (hw.mpr h)
        obtain ⟨i, hi⟩ := exists_predPos hlin hj hnmin
        exact ⟨((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).2 _ _ _ hi hp).mpr
          (hw.mpr h), hr, hj, hp, hnmin⟩
  right_inv := fun _ => rfl

end Solutions

/-- **#0-1 integer programming**: the number of `0-1` vectors satisfying every
equation of the program. -/
noncomputable def SharpZeroOneIP : Lax366625.CountingProblems.CountingProblem Lax799700.ZeroOneIP.zeroOneIP where
  Count := fun A inst => Nat.card {x : A → Prop // @Lax280166.CountingKnapsacks.ZeroOneSol A inst x}
  iso_invariant := fun {A B} _ _ e => by
    by_cases hfin : Finite A
    · have : Finite B := Finite.of_equiv A e.toEquiv
      rw [← Nat.card_congr (zeroOneIPEquiv A), ← Nat.card_congr (zeroOneIPEquiv B)]
      exact witnessCount_iso zeroOneIPGuessBlock sharpZeroOneIPKernel e
    · have hB : ¬Finite B := fun h => hfin (Finite.of_equiv B e.toEquiv.symm)
      have hA0 : IsEmpty {x : A → Prop // Lax280166.CountingKnapsacks.ZeroOneSol A x} := ⟨fun x => hfin x.2.1⟩
      have hB0 : IsEmpty {x : B → Prop // Lax280166.CountingKnapsacks.ZeroOneSol B x} := ⟨fun x => hB x.2.1⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

theorem sharpZeroOneIP_apply (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] :
    SharpZeroOneIP A = Nat.card {x : A → Prop // Lax280166.CountingKnapsacks.ZeroOneSol A x} :=
  rfl

/-- **The support of #0-1 integer programming is 0-1 integer programming.** -/
theorem sharpZeroOneIP_support_iff (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] [Finite A] :
    SharpZeroOneIP.support A ↔ ZeroOneIP A := by
  rw [CountingProblem.support_iff, sharpZeroOneIP_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨x, hfin, hlin, hx, hsum⟩, -⟩
    exact ⟨hfin, hlin, x, hx, hsum⟩
  · rintro ⟨hfin, hlin, x, hx, hsum⟩
    exact ⟨⟨⟨x, hfin, hlin, hx, hsum⟩⟩, inferInstance⟩

/-- **#0-1 integer programming is in `#P`.** -/
theorem sharpZeroOneIP_mem_sharpP : SharpZeroOneIP ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (zeroOneIPEquiv A))
    (sharpPDefinable_ofKernel zeroOneIPGuessBlock sharpZeroOneIPKernel)

end Lax280166Proofs.DescriptiveComplexity


