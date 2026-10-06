/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull
import Lax134656Proofs.DescriptiveComplexity.Hierarchy
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656Proofs.DescriptiveComplexity.SOTCDefinable
end Lax134656Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax134656Proofs.DescriptiveComplexity

/-!
# PSPACE, by second-order transitive closure

**The class PSPACE**: the problems definable in SO(TC), second-order logic with
a transitive closure taken over assignments of a relation block
(`DescriptiveComplexity.SOTCDefinable`), which captures polynomial space on ordered
structures ([Immerman 1999][immerman1999descriptive], ch. 10). This is the same
move as defining `PTIME` by the Horn fragment, `NL` by the Krom fragment and
`NP` by `Σ₁`-definability: the class is a *definition*, not an axiom, and it is
a bona fide `DescriptiveComplexity.ComplexityClass` because SO(TC) definability is
closed under (ordered) first-order reductions – the block and the three
sentences all survive the pullback, see
`DescriptiveComplexity.SecondOrderTransitiveClosurePull`.

## Why the states are relations

An SO(TC) walk remembers an assignment of relations, i.e., `n^a` bits on a
universe of size `n`, and may take exponentially many steps to reach its
target. That is precisely a polynomially space-bounded computation: the
configuration is the remembered assignment, and the (first-order) transition
sentence is one step of the machine. Immerman's capture theorem is the
statement that nothing is lost either way; here, as everywhere in this library,
the logic is taken as the definition of the class and the capture theorem is a
statement about machines, to be proved against a machine model rather than
assumed (see `DescriptiveComplexity.Machines`).

## What is *not* free here

* **PSPACE = coPSPACE** is not the definitional duality that gives `PiP k` from
  `SigmaP k`: the complement of an SO(TC) definable problem is not *obviously*
  SO(TC) definable. It is a genuine theorem, and it is proved – downstream, in
  `DescriptiveComplexity.PSpaceCompl`, once QSAT is available: every SO(TC)
  definable problem reduces to QSAT, complementing a reduction is free, and the
  walk that decides QSAT is deterministic, so reading its answer the other way
  round decides the complement.
* **PH ⊆ PSPACE** is not a syntactic inclusion either: a `Σₖ` sentence is not a
  walk. It too is proved downstream, in `DescriptiveComplexity.PSpaceHierarchy`,
  by alternating that complement with the other closure property of SO(TC) – a
  walk can guess a block into its own state and never touch it again – along the
  quantifier prefix. What *is* immediate here is the bottom of the tower,
  `NP ⊆ PSPACE` (`DescriptiveComplexity.NP_subset_PSPACE`): an existential block
  is a walk that guesses its state in one step and then stops, so
  `Σ₁`-definability is SO(TC) definability with an empty transition relation.
  Everything below NP follows by composition.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class PSPACE**: the problems definable in SO(TC), second-order logic
with a transitive closure over assignments of a relation block, which captures
polynomial space on ordered structures ([Immerman
1999][immerman1999descriptive]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`); over a relational vocabulary it is the usual
notion, `DescriptiveComplexity.hard_PSPACE_iff`. -/
noncomputable def PSPACE : ComplexityClass :=
  .ofMem (fun P => Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sotcDefinable_congr h)

/-- Membership in PSPACE is exactly SO(TC) definability, by definition. -/
theorem mem_PSPACE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : P ∈ PSPACE ↔ Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P :=
  Iff.rfl

/-- Over a relational vocabulary, PSPACE-hardness is the usual notion: every
SO(TC) definable problem reduces to `P`. -/
theorem hard_PSPACE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    PSPACE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
        Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- A problem is PSPACE-hard as soon as every SO(TC) definable problem reduces
to it; the discharge shape shared by every PSPACE-hardness proof of the
catalog. -/
theorem PSPACE_hard_of_sotcDefinable [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : Lax904597.Problems.DecisionProblem L''),
      Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : PSPACE.Hard P :=
  (hard_PSPACE_iff P).mpr h

/-! ### `NP ⊆ PSPACE`: an existential block is a one-step walk

A `Σ₁` definition `∃ R̄. φ(R̄)` is the SO(TC) specification whose states are the
assignments of the block, whose transition relation is *empty*, and whose
starting and accepting states are both the ones satisfying `φ`. Its walks are
the one-state walks, so it accepts exactly when some assignment satisfies `φ`.

The only work is that an SO(TC) specification's sentences live over the
*ordered* expansion of the vocabulary, so the kernel has to be moved along the
language map that inserts the order symbol. -/

section SigmaOne

/-- The language map inserting the order vocabulary underneath a block
expansion: the kernel of a `Σ₁` definition, which does not see the order, read
as a sentence of the vocabulary an SO(TC) specification uses. -/
def blockOrderLift (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) :
    (L.sum B.lang) →ᴸ ((L.sum Language.order).sum B.lang) :=
  LHom.sumMap LHom.sumInl (LHom.id B.lang)

variable {A : Type} [L.Structure A] [LinearOrder A] (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A)

/-- Inserting the order symbol does not change how anything is interpreted. -/
theorem blockOrderLift_isExpansionOn :
    @LHom.IsExpansionOn _ _ (blockOrderLift L B) A
      (B.structure₁ (L := L) ρ) (B.structure₁ (L := L.sum Language.order) ρ) := by
  let := B.structure₁ (L := L) ρ
  let := B.structure₁ (L := L.sum Language.order) ρ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · cases f with
    | inl g => rfl
    | inr g => exact g.elim
  · cases r with
    | inl s => rfl
    | inr s => rfl

/-- The lifted kernel realizes over the ordered expansion exactly as the
original kernel realizes over the base expansion. -/
theorem realize_blockOrderLift (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize _ A (B.structure₁ (L := L.sum Language.order) ρ)
        ((blockOrderLift L B).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) ρ) φ :=
  letI := B.structure₁ (L := L) ρ
  letI := B.structure₁ (L := L.sum Language.order) ρ
  haveI := blockOrderLift_isExpansionOn (L := L) B ρ
  LHom.realize_onSentence (M := A) (blockOrderLift L B) φ

variable (L) in
/-- The specification of a `Σ₁` definition: the states are the assignments of
the block, there are no transitions, and the accepting states are the ones
satisfying the kernel. -/
def sigmaOneSpec (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence) : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L where
  B := B
  step := ⊥
  src := (blockOrderLift L B).onSentence φ
  tgt := (blockOrderLift L B).onSentence φ

/-- The one-step walk of a `Σ₁` definition accepts exactly when the kernel is
satisfiable in the block. -/
theorem sigmaOneSpec_accepts_iff (φ : (L.sum B.lang).Sentence) :
    (sigmaOneSpec L B φ).Accepts A ↔
      ∃ ρ : B.Assignment A, @Sentence.Realize _ A (B.structure₁ (L := L) ρ) φ := by
  have hstep : ∀ ρ σ : B.Assignment A, ¬(sigmaOneSpec L B φ).Step ρ σ := fun _ _ h => h
  constructor
  · rintro ⟨ρ, σ, hρ, -, -⟩
    exact ⟨ρ, (realize_blockOrderLift B ρ φ).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ, ρ, (realize_blockOrderLift B ρ φ).mpr hρ,
      (realize_blockOrderLift B ρ φ).mpr hρ, Relation.ReflTransGen.refl⟩

/-- **Every `Σ₁`-definable problem is SO(TC) definable**: guess the block in
the state, take no step. -/
theorem SOTCDefinable.of_sigmaSODefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax904597.SecondOrder.SigmaSODefinable 1 P) : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  match Bs, hlen with
  | [B], _ =>
    refine ⟨sigmaOneSpec L B φ, ?_⟩
    intro A _ _ _ _
    exact (hφ A).trans (sigmaOneSpec_accepts_iff B φ).symm

end SigmaOne

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax134656Proofs.DescriptiveComplexity.SOTCDefinable (of_sigmaSODefinable)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

section SigmaOne

variable {A : Type} [L.Structure A] [LinearOrder A] (B : Lax904597.SecondOrder.SOBlock) (ρ : B.Assignment A)

end SigmaOne

/-- **`NP ⊆ PSPACE`**: NP is `Σ₁`-definability (Fagin) and PSPACE is SO(TC)
definability, and an existential block is a walk that guesses its state and
stops. -/
theorem NP_subset_PSPACE : NP ⊆ PSPACE :=
  fun _ _ _ h => SOTCDefinable.of_sigmaSODefinable h

end Lax134656Proofs.DescriptiveComplexity


