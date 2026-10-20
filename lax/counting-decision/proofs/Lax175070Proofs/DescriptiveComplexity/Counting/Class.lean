/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Counting.SharpP
import Lax175070Proofs.DescriptiveComplexity.Counting.Relativized
import Lax175070Proofs.DescriptiveComplexity.Hierarchy
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Lax175070Proofs.DescriptiveComplexity.FixedPointReduction
import Lax175070Proofs.DescriptiveComplexity.FixedPointStep
import Lax175070Proofs.DescriptiveComplexity.OrderWalk
import Lax175070Proofs.DescriptiveComplexity.OrderedComposition
import Lax175070Proofs.DescriptiveComplexity.Padding
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat
import Lax175070Proofs.DescriptiveComplexity.RelComposition
import Lax175070Proofs.DescriptiveComplexity.SecondOrder
import Lax175070Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax175070Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax175070Proofs.DescriptiveComplexity.SecondOrderLift
import Lax175070Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax175070Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax175070Proofs.DescriptiveComplexity.SecondOrderPull
import Lax175070Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax175070.CountDefinability
import Lax175070.SelectedSat
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax175070Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax175070Proofs.DescriptiveComplexity.SharpPDefinable
end Lax175070Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable)
end Lax175070Proofs.DescriptiveComplexity

/-!
# Counting classes, the class `#P`, and its relation to NP

A `DescriptiveComplexity.CountingClass` is to counting problems what a
`DescriptiveComplexity.ComplexityClass` is to decision problems: a membership
predicate and a hardness predicate, closed under reductions – here the
*parsimonious* ones of `DescriptiveComplexity.Counting`, membership backward and
hardness forward. As on the decision side, hardness also travels along the
*relativized* reductions of `DescriptiveComplexity.Counting.Relativized`, whose target
universe is definable, and hardness for a class is cofinality for those: a
problem whose solutions span the universe can be hard in no other way.

## Parsimonious hardness is not the hardness of the literature

The hardness predicate is named `ParsimoniousHard`, and completeness
`ParsimoniousComplete`, never plain “hard” and “complete”, because they are
strictly stronger than what “`#P`-hard” and “`#P`-complete” mean in the
literature, where the reductions are polynomial-time Turing (or one oracle call
followed by arithmetic). Counting the satisfying assignments of a DNF formula,
or the independent sets of a graph, is `#P`-complete in that sense, and it is
*not* parsimoniously `#P`-hard unless `NP ⊆ PTIME`
(`DescriptiveComplexity.NP_subset_PTIME_of_sharpP_parsimoniousHard`): a parsimonious
reduction preserves “the count is positive”, so it carries the hardness of the
decision problem along, and these problems have an easy one. The unqualified
names are left free for the weaker notion.

Parsimonious completeness is the notion under which completeness says
something about the decision problem underneath and about approximability
([Arenas, Muñoz, Riveros 2020][arenas2020descriptive]).

The class `DescriptiveComplexity.SharpP` is *defined* by witness counting
(`DescriptiveComplexity.SharpPDefinable`), as `NP` is defined by existential
second-order definability.

## Relation to NP

The decision problem underneath a counting problem is its support, “is the
count positive?”. Three statements tie `#P` to NP through it:

* `DescriptiveComplexity.mem_NP_iff_exists_sharpP_support`: the problems of NP are
  exactly the supports of the problems of `#P`;
* `DescriptiveComplexity.NP_hard_support_of_sharpP_parsimoniousHard`: the support of a
  parsimoniously `#P`-hard problem is NP-hard;
* `DescriptiveComplexity.NP_subset_PTIME_of_sharpP_parsimoniousHard`: if a
  parsimoniously `#P`-hard problem has
  its support in PTIME, then `NP ⊆ PTIME`.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- An abstract counting class: a collection of counting problems (its
`Mem`bership predicate) together with a `ParsimoniousHard`ness predicate, closed under
parsimonious reductions. Membership travels backward along them, hardness
forward. -/
structure CountingClass where
  /-- The counting problems belonging to the class. Use the notation
  `C ∈ 𝒞`. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], Lax366625.CountingProblems.CountingProblem L → Prop
  /-- The counting problems every problem of the class parsimoniously reduces
  to. -/
  ParsimoniousHard : ∀ {L : Language.{0, 0}} [L.IsRelational], Lax366625.CountingProblems.CountingProblem L → Prop
  /-- Membership travels backward along parsimonious reductions. -/
  mem_of_parsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}, (C ≤ᵖ D) → Mem D → Mem C
  /-- Parsimonious hardness travels forward along parsimonious reductions. -/
  parsimoniousHard_of_parsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'},
    (C ≤ᵖ D) → ParsimoniousHard C → ParsimoniousHard D
  /-- Membership travels backward along ordered parsimonious reductions. -/
  mem_of_orderedParsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'}, (C ≤ᵖ[≤] D) → Mem D → Mem C
  /-- Parsimonious hardness travels forward along ordered parsimonious
  reductions. -/
  parsimoniousHard_of_orderedParsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'},
    (C ≤ᵖ[≤] D) → ParsimoniousHard C → ParsimoniousHard D
  /-- Parsimonious hardness travels forward along relativized ordered
  parsimonious reductions – the reductions with a definable target universe,
  needed for the problems whose solutions span it. -/
  parsimoniousHard_of_relOrderedParsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D : Lax366625.CountingProblems.CountingProblem L'},
    (C ≤ʳᵖ[≤] D) → ParsimoniousHard C → ParsimoniousHard D
  /-- Membership only depends on the values of a counting problem on finite
  structures. -/
  mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {C D : Lax366625.CountingProblems.CountingProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], C A = D A) → (Mem C ↔ Mem D)
  /-- Parsimonious hardness, too, only depends on the finite instances. -/
  parsimoniousHard_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational]
    {C D : Lax366625.CountingProblems.CountingProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], C A = D A) → (ParsimoniousHard C ↔ ParsimoniousHard D)

/-- `C ∈ 𝒞`: the counting problem `C` belongs to the counting class `𝒞`. -/
scoped notation:50 C:51 " ∈ " K:51 => CountingClass.Mem K C

namespace CountingClass

/-- The counting class with a given membership predicate, parsimonious hardness
being cofinality for it: every member reduces to the problem, by a relativized
ordered parsimonious reduction. Only the membership obligations have to be
supplied. -/
def ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax366625.CountingProblems.CountingProblem L₀ → Prop)
    (mem_of_orderedParsimonious : ∀ {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational]
      [L₂.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L₁} {D : Lax366625.CountingProblems.CountingProblem L₂},
      (C ≤ᵖ[≤] D) → Mem D → Mem C)
    (mem_congr_finite : ∀ {L₁ : Language.{0, 0}} [L₁.IsRelational] {C D : Lax366625.CountingProblems.CountingProblem L₁},
      (∀ (A : Type) [L₁.Structure A] [Finite A], C A = D A) → (Mem C ↔ Mem D)) :
    CountingClass where
  Mem C := Mem C
  ParsimoniousHard C := ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''),
    Mem D → Nonempty (D ≤ʳᵖ[≤] C)
  mem_of_parsimonious f h := mem_of_orderedParsimonious f.toOrdered h
  parsimoniousHard_of_parsimonious f hC := fun D hD =>
    ⟨(hC D hD).some.trans f.toOrdered.toRel⟩
  mem_of_orderedParsimonious f h := mem_of_orderedParsimonious f h
  parsimoniousHard_of_orderedParsimonious f hC := fun D hD => ⟨(hC D hD).some.trans f.toRel⟩
  parsimoniousHard_of_relOrderedParsimonious f hC := fun D hD => ⟨(hC D hD).some.trans f⟩
  mem_congr_finite h := mem_congr_finite h
  parsimoniousHard_congr_finite h :=
    ⟨fun hC _ _ D hD => ⟨(hC D hD).some.congrTarget h⟩,
      fun hC _ _ D hD => ⟨(hC D hD).some.congrTarget fun A _ _ => (h A).symm⟩⟩

variable (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]

/-- A counting problem is parsimoniously complete for a class if it belongs to
it and every problem of the class parsimoniously reduces to it. -/
def ParsimoniousComplete (C : Lax366625.CountingProblems.CountingProblem L) : Prop :=
  C ∈ K ∧ K.ParsimoniousHard C

theorem ParsimoniousComplete.mem {C : Lax366625.CountingProblems.CountingProblem L} (h : K.ParsimoniousComplete C) :
    C ∈ K := h.1

theorem ParsimoniousComplete.parsimoniousHard {C : Lax366625.CountingProblems.CountingProblem L}
    (h : K.ParsimoniousComplete C) : K.ParsimoniousHard C := h.2

end CountingClass

/-! ### The class `#P` -/

/-- **The class `#P`**: the counting problems that count the witnesses of an
existential second-order sentence over ordered structures
([Saluja, Subrahmanyam, Thakur 1995][saluja1995descriptive]). It is closed
under parsimonious reductions, and hardness for it is hardness under
relativized ordered parsimonious reductions. -/
noncomputable def SharpP : CountingClass :=
  .ofMem (fun C => Lax366625.WitnessCounting.SharpPDefinable C)
    (fun f h => h.of_orderedParsimonious f)
    (fun h => ⟨sharpPDefinable_congr h, sharpPDefinable_congr fun A _ _ => (h A).symm⟩)

variable {L : Language.{0, 0}} [L.IsRelational]

theorem mem_sharpP_iff (C : Lax366625.CountingProblems.CountingProblem L) : C ∈ SharpP ↔ Lax366625.WitnessCounting.SharpPDefinable C :=
  Iff.rfl

/-- Parsimonious `#P`-hardness, unfolded: every `#P`-definable counting problem
reduces to `C` by a relativized ordered parsimonious reduction. -/
theorem parsimoniousHard_sharpP_iff (C : Lax366625.CountingProblems.CountingProblem L) :
    SharpP.ParsimoniousHard C ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''),
        Lax366625.WitnessCounting.SharpPDefinable D → Nonempty (D ≤ʳᵖ[≤] C) :=
  Iff.rfl

/-- The witness-counting problem of an existential second-order sentence is in
`#P`. -/
theorem ofKernel_mem_sharpP (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) :
    CountingProblem.ofKernel B φ ∈ SharpP :=
  sharpPDefinable_ofKernel B φ

/-! ### Relation to NP -/

/-- The support of a `#P`-definable counting problem is `Σ₁`-definable: a
count of witnesses is positive exactly when there is a witness, and the order
the kernel reads is re-quantified by the order elimination of
`DescriptiveComplexity.sigmaSODefinable_of_orderPull`. -/
theorem SharpPDefinable.support_sigmaSODefinable {C : Lax366625.CountingProblems.CountingProblem L}
    (h : Lax366625.WitnessCounting.SharpPDefinable C) : Lax904597.SecondOrder.SigmaSODefinable 1 C.support := by
  obtain ⟨B, φ, hφ⟩ := h
  refine sigmaSODefinable_of_orderPull (k := 0) [B] rfl φ ?_
  intro A _ _ _
  constructor
  · intro hpos
    refine ⟨finiteLinearOrder A, ?_⟩
    let := finiteLinearOrder A
    rw [CountingProblem.support_iff, hφ A] at hpos
    exact (witnessCount_pos_iff B φ A).mp hpos
  · rintro ⟨lo, hlo⟩
    let := lo
    rw [CountingProblem.support_iff, hφ A]
    exact (witnessCount_pos_iff B φ A).mpr hlo

end Lax175070Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax175070Proofs.DescriptiveComplexity.SharpPDefinable (support_sigmaSODefinable)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The support of a problem of `#P` is in NP. -/
theorem support_mem_NP {C : Lax366625.CountingProblems.CountingProblem L} (h : C ∈ SharpP) : C.support ∈ NP :=
  SharpPDefinable.support_sigmaSODefinable h

/-- **NP is the class of supports of `#P`**: a decision problem is in NP exactly
when it is, on nonempty finite structures, the question whether some counting
problem of `#P` is positive – the counting problem being the number of
witnesses of the `Σ₁` definition. -/
theorem mem_NP_iff_exists_sharpP_support (P : Lax904597.Problems.DecisionProblem L) :
    P ∈ NP ↔ ∃ C : Lax366625.CountingProblems.CountingProblem L, C ∈ SharpP ∧
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], C.support A ↔ P A := by
  constructor
  · rintro ⟨Bs, hlen, φ, hφ⟩
    cases Bs with
    | nil => exact absurd hlen (by simp)
    | cons B Bs' =>
      cases Bs' with
      | nil =>
        exact ⟨CountingProblem.ofKernel B φ, ofKernel_mem_sharpP B φ, fun A _ _ _ =>
          (CountingProblem.ofKernel_support_iff B φ A).trans (hφ A).symm⟩
      | cons B' Bs'' => simp at hlen
  · rintro ⟨C, hC, hCP⟩
    obtain ⟨Bs, hlen, φ, hφ⟩ := support_mem_NP hC
    exact ⟨Bs, hlen, φ, fun A _ _ _ => (hCP A).symm.trans (hφ A)⟩

end Lax175070Proofs.DescriptiveComplexity


