/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.SharpP
import Lax366625Proofs.DescriptiveComplexity.Counting.Relativized
import Lax366625Proofs.DescriptiveComplexity.Hierarchy
import Lax366625Proofs.DescriptiveComplexity.FixedPointReductionClosure
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

namespace Lax366625Proofs.DescriptiveComplexity.OrderedParsimoniousReduction
end Lax366625Proofs.DescriptiveComplexity.OrderedParsimoniousReduction

namespace Lax366625Proofs.DescriptiveComplexity.SharpPDefinable
end Lax366625Proofs.DescriptiveComplexity.SharpPDefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (SharpPDefinable)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax366625Proofs.DescriptiveComplexity

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

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- Replacing the target of an ordered parsimonious reduction by a counting
problem with the same values on finite structures. -/
def OrderedParsimoniousReduction.congrTarget {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L} {D D' : Lax366625.CountingProblems.CountingProblem L'}
    (h : ∀ (A : Type) [L'.Structure A] [Finite A], D A = D' A) (g : C ≤ᵖ[≤] D) :
    C ≤ᵖ[≤] D' :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation := g.toInterpretation
    correct := fun A _ _ _ _ =>
      haveI := g.toInterpretation.map_finite A
      (g.correct A).trans (h (g.toInterpretation.Map A)) }

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction

export Lax366625Proofs.DescriptiveComplexity.OrderedParsimoniousReduction (congrTarget)

end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625Proofs.DescriptiveComplexity

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

/-- Parsimonious `#P`-hardness, unfolded: every `#P`-definable counting problem
reduces to `C` by a relativized ordered parsimonious reduction. -/
theorem parsimoniousHard_sharpP_iff (C : Lax366625.CountingProblems.CountingProblem L) :
    SharpP.ParsimoniousHard C ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''),
        Lax366625.WitnessCounting.SharpPDefinable D → Nonempty (D ≤ʳᵖ[≤] C) :=
  Iff.rfl

/-- A problem every `#P`-definable counting problem reduces to by an ordinary
ordered parsimonious reduction is parsimoniously `#P`-hard. -/
theorem parsimoniousHard_sharpP_of_ordered {C : Lax366625.CountingProblems.CountingProblem L}
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : Lax366625.CountingProblems.CountingProblem L''),
      Lax366625.WitnessCounting.SharpPDefinable D → Nonempty (D ≤ᵖ[≤] C)) : SharpP.ParsimoniousHard C :=
  fun D hD => (h D hD).map fun g => g.toRel

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

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.WitnessCounting.SharpPDefinable

export Lax366625Proofs.DescriptiveComplexity.SharpPDefinable (support_sigmaSODefinable)

end Lax366625.WitnessCounting.SharpPDefinable

namespace Lax366625Proofs.DescriptiveComplexity

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

/-- Every problem of NP reduces to the support of a parsimoniously `#P`-hard counting
problem. -/
theorem nonempty_relOrderedReduction_support_of_sharpP_parsimoniousHard
    {C : Lax366625.CountingProblems.CountingProblem L} (hC : SharpP.ParsimoniousHard C) {L' : Language.{0, 0}}
    [L'.IsRelational] (Q : Lax904597.Problems.DecisionProblem L') (hQ : Q ∈ NP) :
    Nonempty (Q ≤ʳᶠᵒ[≤] C.support) := by
  obtain ⟨D, hD, hDQ⟩ := (mem_NP_iff_exists_sharpP_support Q).mp hQ
  obtain ⟨g⟩ := hC D hD
  let := g.tagFinite
  exact ⟨{ Tag := g.Tag
           dim := g.dim
           toRelInterpretation := g.toRelInterpretation
           dom_nonempty := g.dom_nonempty
           correct := fun A _ _ _ _ =>
            (hDQ A).symm.trans (g.toRelOrderedFOReduction.correct A) }⟩

/-- **The support of a parsimoniously `#P`-hard counting problem is NP-hard.** -/
theorem NP_hard_support_of_sharpP_parsimoniousHard {C : Lax366625.CountingProblems.CountingProblem L}
    (hC : SharpP.ParsimoniousHard C) :
    NP.Hard C.support :=
  (hard_sigmaP_succ_iff 0 C.support).mpr fun Q hQ =>
    nonempty_relOrderedReduction_support_of_sharpP_parsimoniousHard hC Q hQ

/-- **A parsimoniously `#P`-hard counting problem with an easy decision version collapses NP
into PTIME.** This is why the counting problems whose support is in PTIME –
satisfying assignments of a DNF or of a monotone 2-CNF formula, independent
sets, worlds of a probabilistic database satisfying a monotone query – are
not parsimoniously `#P`-complete unless `NP ⊆ PTIME`. -/
theorem NP_subset_PTIME_of_sharpP_parsimoniousHard {C : Lax366625.CountingProblems.CountingProblem L}
    (hC : SharpP.ParsimoniousHard C)
    (hsupp : C.support ∈ PTIME) : NP ⊆ PTIME := fun _ _ Q hQ =>
  mem_PTIME_of_relOrderedReduction
    (nonempty_relOrderedReduction_support_of_sharpP_parsimoniousHard hC Q hQ).some hsupp

end Lax366625Proofs.DescriptiveComplexity


