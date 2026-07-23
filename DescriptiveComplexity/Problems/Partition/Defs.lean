/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Defs

/-!
# Partition: definition

PARTITION ([Karp 1972][karp1972reducibility]): can a family of numbers be split
into two parts of equal sum? It lives on `FirstOrder.Language.binWeights`
unchanged (`DescriptiveComplexity.Problems.Knapsack.Defs`), the vocabulary of
representation (C) – items, bit positions, the bits of each weight, and a
linear order – with the *target* symbol simply unused: what a partition must
match is not a given number but the weight of the items it leaves out.

That absence is what makes Partition a genuinely different problem from
Knapsack rather than a special case: the number to reach, half the total, is
not part of the instance, so an interpretation cannot compute it. Hardness
therefore does not come from Knapsack by the classical two-extra-items padding
(those two weights are arithmetic in the total, hence not first-order
definable); it comes from NAE-3SAT, whose *not-all-equal* condition is exactly
the two-sided constraint a balanced split imposes.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [Language.binWeights.Structure A]

/-- A binary-weighted instance is a yes-instance of Partition when its order is
a linear order and some set of items weighs exactly as much as the items it
leaves out. -/
def HasEqualSplit : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧
    ∃ S : A → Prop, (∀ i, S i → BWItem i) ∧
      (∑ᶠ i ∈ {i | S i}, BWWeight i) = ∑ᶠ i ∈ {i | BWItem i ∧ ¬S i}, BWWeight i

end Problem

section Iso

variable {A B : Type} [Language.binWeights.Structure A] [Language.binWeights.Structure B]

private theorem hasEqualSplit_of_iso (e : A ≃[Language.binWeights] B)
    (h : HasEqualSplit A) : HasEqualSplit B := by
  obtain ⟨hfin, hlin, S, hSi, hsum⟩ := h
  have hle : ∀ a a' : A, BWLe a a' ↔ BWLe (e a) (e a') := fun a a' =>
    relMap_equiv₂ e bwLe a a'
  have hposn : ∀ a : A, BWPosn a ↔ BWPosn (e a) := fun a => relMap_equiv₁ e bwPosn a
  have hitem : ∀ a : A, BWItem a ↔ BWItem (e a) := fun a => relMap_equiv₁ e bwItem a
  have hbit : ∀ a a' : A, BWBit a a' ↔ BWBit (e a) (e a') := fun a a' =>
    relMap_equiv₂ e bwBit a a'
  have hw : ∀ a : A, BWWeight a = BWWeight (e a) := fun a =>
    binNum_equiv e.toEquiv hle hposn (hbit a)
  -- the weight of a set of items is carried along the equivalence
  have htransport : ∀ P : A → Prop,
      (∑ᶠ a ∈ {a | P a}, BWWeight a) = ∑ᶠ b ∈ {b | P (e.toEquiv.symm b)}, BWWeight b := by
    intro P
    refine finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha
  have key : ∀ b : B, BWItem (e.toEquiv.symm b) ↔ BWItem b := fun b =>
    (hitem (e.toEquiv.symm b)).trans
      (Iff.of_eq (congrArg BWItem (e.toEquiv.apply_symm_apply b)))
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => S (e.toEquiv.symm b), fun b hb => ?_, ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hitem _).mp (hSi _ hb)
  · rw [← htransport S, hsum, htransport fun a => BWItem a ∧ ¬S a]
    refine finsum_mem_congr (Set.ext fun b => ?_) fun _ _ => rfl
    simp only [Set.mem_setOf_eq]
    exact and_congr_left fun _ => key b

/-- Being a yes-instance of Partition is isomorphism-invariant. -/
theorem hasEqualSplit_iso (e : A ≃[Language.binWeights] B) :
    HasEqualSplit A ↔ HasEqualSplit B :=
  ⟨hasEqualSplit_of_iso e, hasEqualSplit_of_iso e.symm⟩

end Iso

/-- PARTITION, as a problem on binary-weighted instances: can the items be
split into two parts of equal weight? The weights are written in *binary*, and
the target symbol of the vocabulary is ignored – the number to reach is half
the total, which the instance does not carry. -/
def Partition : DecisionProblem Language.binWeights where
  Holds := fun A inst => @HasEqualSplit A inst
  iso_invariant := fun e => hasEqualSplit_iso e

end DescriptiveComplexity
