/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Defs
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Partition: definition

PARTITION ([Karp 1972][karp1972reducibility]): can a family of numbers be split
into two parts of equal sum? It lives on `FirstOrder.Language.binWeights`
unchanged (`Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Defs`), the vocabulary of
the binary encoding – items, bit positions, the bits of each weight, and a
linear order – with the *target* symbol simply unused: what a partition must
match is not a given number but the weight of the items it leaves out.

That absence is what makes Partition a genuinely different problem from
Knapsack rather than a special case: the number to reach, half the total, is
not part of the instance, so an interpretation cannot compute it. Hardness
therefore does not come from Knapsack by the classical two-extra-items padding
(those two weights are arithmetic in the total, hence not first-order
definable); it comes from NAE-SAT, whose *not-all-equal* condition is exactly
the two-sided constraint a balanced split imposes
(`Lax799700Proofs.DescriptiveComplexity.naeSat_ordered_fo_reduction_partition`).
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [Lax799700.Knapsack.binWeights.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B]

private theorem hasEqualSplit_of_iso (e : A ≃[Lax799700.Knapsack.binWeights] B)
    (h : Lax799700.Partition.HasEqualSplit A) : Lax799700.Partition.HasEqualSplit B := by
  obtain ⟨hfin, hlin, S, hSi, hsum⟩ := h
  have hle : ∀ a a' : A, Lax799700.Knapsack.BWLe a a' ↔ Lax799700.Knapsack.BWLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.Knapsack.bwLe a a'
  have hposn : ∀ a : A, Lax799700.Knapsack.BWPosn a ↔ Lax799700.Knapsack.BWPosn (e a) := fun a => relMap_equiv₁ e Lax799700.Knapsack.bwPosn a
  have hitem : ∀ a : A, Lax799700.Knapsack.BWItem a ↔ Lax799700.Knapsack.BWItem (e a) := fun a => relMap_equiv₁ e Lax799700.Knapsack.bwItem a
  have hbit : ∀ a a' : A, Lax799700.Knapsack.BWBit a a' ↔ Lax799700.Knapsack.BWBit (e a) (e a') := fun a a' =>
    relMap_equiv₂ e Lax799700.Knapsack.bwBit a a'
  have hw : ∀ a : A, Lax799700.Knapsack.BWWeight a = Lax799700.Knapsack.BWWeight (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hbit a)
  -- the weight of a set of items is carried along the equivalence
  have htransport : ∀ P : A → Prop,
      (∑ᶠ a ∈ {a | P a}, Lax799700.Knapsack.BWWeight a) = ∑ᶠ b ∈ {b | P (e.toEquiv.symm b)}, Lax799700.Knapsack.BWWeight b := by
    intro P
    refine finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha
  have key : ∀ b : B, Lax799700.Knapsack.BWItem (e.toEquiv.symm b) ↔ Lax799700.Knapsack.BWItem b := fun b =>
    (hitem (e.toEquiv.symm b)).trans
      (Iff.of_eq (congrArg Lax799700.Knapsack.BWItem (e.toEquiv.apply_symm_apply b)))
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => S (e.toEquiv.symm b), fun b hb => ?_, ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hitem _).mp (hSi _ hb)
  · rw [← htransport S, hsum, htransport fun a => Lax799700.Knapsack.BWItem a ∧ ¬S a]
    refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
    simp only [Set.mem_ofPred_eq]
    exact and_congr_left fun _ => key b

/-- Being a yes-instance of Partition is isomorphism-invariant. -/
theorem hasEqualSplit_iso (e : A ≃[Lax799700.Knapsack.binWeights] B) :
    Lax799700.Partition.HasEqualSplit A ↔ Lax799700.Partition.HasEqualSplit B :=
  ⟨hasEqualSplit_of_iso e, hasEqualSplit_of_iso e.symm⟩

end Iso

/-- PARTITION, as a problem on binary-weighted instances: can the items be
split into two parts of equal weight? The weights are written in *binary*, and
the target symbol of the vocabulary is ignored – the number to reach is half
the total, which the instance does not carry. -/
def Partition : Lax904597.Problems.DecisionProblem Lax799700.Knapsack.binWeights where
  Holds := fun A inst => @Lax799700.Partition.HasEqualSplit A inst
  iso_invariant := fun e => hasEqualSplit_iso e

end Lax799700Proofs.DescriptiveComplexity


