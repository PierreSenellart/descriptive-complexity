/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrder
import Lax822549Proofs.DescriptiveComplexity.Ordered
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.SOBlock
end Lax822549Proofs.DescriptiveComplexity.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.SOTCSpec
end Lax822549Proofs.DescriptiveComplexity.SOTCSpec

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# SO(TC): second-order logic with transitive closure

The logic that captures polynomial space on ordered structures ([Immerman
1999][immerman1999descriptive], ch. 10): a transitive closure taken not over
tuples of *elements*, as in `DescriptiveComplexity.TransitiveClosure`, but over
tuples of *relations*. A state of the walk is an assignment of relations to a
second-order quantifier block, so a structure of size `n` has `2^(n^a)` states
and a walk through them is a computation of exponentially many steps – each one
first-order, hence cheap – on a polynomial amount of remembered information.
That is exactly the resource PSPACE measures.

## Why no fragment of plain SO would do

`DescriptiveComplexity.SigmaSODefinable` and its levels give the polynomial
hierarchy, and plain second-order logic gives `PH` as a whole
([Fagin 1974][fagin1974generalized]; [Stockmeyer
1976][stockmeyer1976polynomial]), so no fragment of plain SO can define PSPACE
without collapsing PH. Some iteration operator is unavoidable, and the
transitive closure is the cheapest one: it needs no positivity condition, no
stage or inflationary machinery, and no syntax of its own.

## The operator as data

As in `DescriptiveComplexity.TransitiveClosure` (and for the same reasons – not
touching Mathlib's `FirstOrder.Language.BoundedFormula`), the operator lives at
the Lean level. A `DescriptiveComplexity.SOTCSpec` bundles

* a second-order quantifier block `B`, whose assignments are the *states* of
  the walk;
* a `step` **sentence** over the base vocabulary expanded by the order and by
  *two* copies of the block – the current state and the next one;
* `src` and `tgt` sentences over one copy of the block.

Reachability itself is `Relation.ReflTransGen`, and a structure is accepted
when some `tgt` state is reachable from some `src` state
(`DescriptiveComplexity.SOTCSpec.Accepts`). A single application of `TC` in front
of a first-order matrix is taken as the definition, exactly as a single
existential block is taken as the definition of `Σ₁`-definability.

## No modes, no tuples

`DescriptiveComplexity.TCSpec` carries a finite *mode* beside its tuple of elements,
because a tuple of elements cannot hold finite data on a one-element universe.
Here nothing of the sort is needed: a relation variable of arity `0` *is* a
bit, so finite control is already inside a block, and a relation variable of
arity `1` holding a singleton is an element register. A state is therefore a
bare `DescriptiveComplexity.SOBlock.Assignment` and the walk carries no extra
components – which also makes the pullback of a specification through an
interpretation (`DescriptiveComplexity.SecondOrderTransitiveClosurePull`) purely a
matter of pulling the block back.

## What this file contains

The semantics (`DescriptiveComplexity.SOTCSpec.Step`,
`DescriptiveComplexity.SOTCSpec.Reach`, `DescriptiveComplexity.SOTCSpec.Accepts`),
its isomorphism-invariance, the transfer of acceptance along a bijection of
states (`DescriptiveComplexity.SOTCSpec.accepts_congr`, the workhorse of the
pullback), and the definability notion
`DescriptiveComplexity.SOTCDefinable`. The class `DescriptiveComplexity.PSPACE`
itself is built on top of it in `DescriptiveComplexity.PSpace`, once closure
under reductions is available.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Expanding a structure by one or two copies of a block -/

section Expand

/-- `FirstOrder.Language.StrongHomClass.realize_sentence` with the two structures
passed explicitly rather than by instance search. The structures a walk is read
against are built from block assignments (`DescriptiveComplexity.SOBlock.structure₁`,
`DescriptiveComplexity.SOBlock.structure₂`) and are never instances, so every
transport in this file and in
`DescriptiveComplexity.SecondOrderTransitiveClosurePull` goes through this form. -/
theorem realize_sentence_of_equiv {L' : Language.{0, 0}} {M N : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (φ : L'.Sentence) :
    @Sentence.Realize L' M instM φ ↔ @Sentence.Realize L' N instN φ :=
  letI := instM
  letI := instN
  StrongHomClass.realize_sentence e φ

/-- `DescriptiveComplexity.SOBlock.extendEquiv` with the two structures passed
explicitly rather than by instance search, for the same reason as
`DescriptiveComplexity.realize_sentence_of_equiv`: the layers a walk is read
against are block expansions, which are not instances. -/
def SOBlock.extendEquiv' (B : Lax904597.SecondOrder.SOBlock) {L' : Language.{0, 0}} {M N : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (ρ : B.Assignment M) :
    @Language.Equiv (L'.sum B.lang) M N (B.structure₁ ρ)
      (B.structure₁ (B.mapAssign e.toEquiv ρ)) :=
  letI := instM
  letI := instN
  B.extendEquiv e ρ

end Expand

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (extendEquiv')

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Expand

/-- Transport of block assignments along an equivalence of universes, as an
equivalence: the states of the walk are in bijection with the states of the
transported walk. -/
def SOBlock.assignEquiv (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A') :
    B.Assignment A ≃ B.Assignment A' where
  toFun := B.mapAssign e
  invFun := B.mapAssign e.symm
  left_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j => e.symm_apply_apply (x j))
  right_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j => e.apply_symm_apply (x j))

end Expand

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (assignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Expand

@[simp]
theorem SOBlock.assignEquiv_apply (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} (e : A ≃ A')
    (ρ : B.Assignment A) : B.assignEquiv e ρ = B.mapAssign e ρ :=
  rfl

end Expand

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (assignEquiv_apply)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Expand

/-- An `L`-isomorphism extends to `L` expanded by two copies of a block, the
two assignments being transported. -/
def SOBlock.extendEquiv₂ (B : Lax904597.SecondOrder.SOBlock) {A A' : Type} [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (ρ σ : B.Assignment A) :
    @Language.Equiv ((L.sum B.lang).sum B.lang) A A'
      (B.structure₂ ρ σ) (B.structure₂ (B.mapAssign e.toEquiv ρ) (B.mapAssign e.toEquiv σ)) :=
  letI := B.structure₁ (L := L) ρ
  letI := B.structure₁ (L := L) (B.mapAssign e.toEquiv ρ)
  B.extendEquiv (B.extendEquiv e ρ) σ

end Expand

end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax822549Proofs.DescriptiveComplexity.SOBlock (extendEquiv₂)

end Lax904597.SecondOrder.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

section Expand

end Expand

/-! ### Specifications -/

namespace SOTCSpec

section Semantics

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

end Semantics

/-! ### Transfer along a bijection of states

Acceptance only depends on the walk up to a bijection of its states. Stated for
two specifications over two vocabularies, since the pullback through an
interpretation relates a specification over the base structure to one over the
interpreted structure. -/

section Transfer

variable {L' : Language.{0, 0}} {spec₁ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L} {spec₂ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L'}
  {A B : Type} [L.Structure A] [LinearOrder A] [L'.Structure B] [LinearOrder B]

theorem reach_map (e : spec₁.State A ≃ spec₂.State B)
    (hstep : ∀ ρ σ, spec₁.Step ρ σ ↔ spec₂.Step (e ρ) (e σ)) {ρ σ : spec₁.State A}
    (h : spec₁.Reach ρ σ) : spec₂.Reach (e ρ) (e σ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((hstep c d).mp hcd)

end Transfer

end SOTCSpec

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax822549Proofs.DescriptiveComplexity.SOTCSpec (reach_map)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace SOTCSpec

section Transfer

variable {L' : Language.{0, 0}} {spec₁ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L} {spec₂ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L'}
  {A B : Type} [L.Structure A] [LinearOrder A] [L'.Structure B] [LinearOrder B]

/-- **Acceptance transfers along a bijection of states** carrying steps to
steps and endpoints to endpoints. -/
theorem accepts_congr (e : spec₁.State A ≃ spec₂.State B)
    (hstep : ∀ ρ σ, spec₁.Step ρ σ ↔ spec₂.Step (e ρ) (e σ))
    (hsrc : ∀ ρ, spec₁.IsSrc ρ ↔ spec₂.IsSrc (e ρ))
    (htgt : ∀ ρ, spec₁.IsTgt ρ ↔ spec₂.IsTgt (e ρ)) :
    spec₁.Accepts A ↔ spec₂.Accepts B := by
  have hstep' : ∀ ρ σ, spec₂.Step ρ σ ↔ spec₁.Step (e.symm ρ) (e.symm σ) := by
    intro ρ σ
    rw [hstep (e.symm ρ) (e.symm σ), e.apply_symm_apply, e.apply_symm_apply]
  constructor
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    exact ⟨e ρ, e σ, (hsrc ρ).mp hρ, (htgt σ).mp hσ, reach_map e hstep h⟩
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    refine ⟨e.symm ρ, e.symm σ, ?_, ?_, reach_map e.symm hstep' h⟩
    · rw [hsrc, e.apply_symm_apply]
      exact hρ
    · rw [htgt, e.apply_symm_apply]
      exact hσ

end Transfer

end SOTCSpec

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax822549Proofs.DescriptiveComplexity.SOTCSpec (accepts_congr)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace SOTCSpec

section Transfer

variable {L' : Language.{0, 0}} {spec₁ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L} {spec₂ : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L'}
  {A B : Type} [L.Structure A] [LinearOrder A] [L'.Structure B] [LinearOrder B]

end Transfer

/-! ### Isomorphism-invariance -/

section Iso

end Iso

end SOTCSpec

/-! ### SO(TC) definability -/

/-- SO(TC) definability only depends on the finite instances of a problem. -/
theorem sotcDefinable_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P ↔ Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Q := by
  constructor <;> rintro ⟨spec, hspec⟩ <;> refine ⟨spec, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hspec A)
  · exact (h A).trans (hspec A)

end Lax822549Proofs.DescriptiveComplexity


