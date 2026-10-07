/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax480241Proofs.DescriptiveComplexity.SecondOrderPull
import Lax480241Proofs.DescriptiveComplexity.OrderedComposition
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

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.FOInterpretation
end Lax480241Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SOTCDefinable
end Lax480241Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity.SOTCSpec
end Lax480241Proofs.DescriptiveComplexity.SOTCSpec

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# Pulling SO(TC) definability back through an interpretation

SO(TC) definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SOTCDefinable.of_orderedReduction`). This is what makes
`DescriptiveComplexity.PSPACE` a `DescriptiveComplexity.ComplexityClass` rather than a
mere definability predicate.

## The walk on the interpreted structure, read on the base structure

A state of an SO(TC) walk is an assignment of a second-order block, so pulling
a specification back is *entirely* a matter of pulling its block back – there
are no tuples of elements and no modes to rearrange, unlike
`DescriptiveComplexity.TCSpec.comap`. The block pullback of
`DescriptiveComplexity.SecondOrderPull` already supplies everything:

* the pulled block is `DescriptiveComplexity.SOBlock.pull`, one `(n·d)`-ary relation
  variable on the base universe per `n`-tuple of tags;
* its assignments are in bijection with the assignments of the original block
  on the interpreted universe (`DescriptiveComplexity.SOBlock.pullAssignEquiv`,
  the two transfers `pullAssign`/`mergeAssign` being mutually inverse);
* the three sentences are pulled back by
  `DescriptiveComplexity.FOInterpretation.pullSentence` through the interpretation
  extended along the block – twice for the transition sentence, which sees two
  copies of the block.

The order enters as it does for the clausal fragments and for FO(TC): the
sentences live over the *ordered* expansion of the target vocabulary, so the
pullback goes through `DescriptiveComplexity.FOInterpretation.ordExtend`, which
interprets the target's order as the lexicographic order on tagged tuples, and
the interpreted structure is equipped with that same order
(`DescriptiveComplexity.FOInterpretation.mapLinearOrder`). Since SO(TC)
definability is required *for every* linear order, the lexicographic one is
available.

## The chain of transports

Each of the three correctness lemmas is the same three-step chain, read from
the interpreted side:

1. `DescriptiveComplexity.FOInterpretation.realize_pullSentence` – the pulled
   sentence on the base structure is the original on the interpreted one;
2. `DescriptiveComplexity.FOInterpretation.extendSOEquiv` – interpreting and then
   expanding by a block is expanding by the pulled block and then interpreting
   (once per copy of the block);
3. `DescriptiveComplexity.FOInterpretation.ordExtendLEquiv` – the order-extended
   interpretation produces the interpreted structure with the lexicographic
   order.

Steps 2 and 3 need the expansion of an isomorphism along a block that is
interpreted by the *same* assignment on both sides, which is
`DescriptiveComplexity.SOBlock.extendEquiv` at an identity map (its transport
`DescriptiveComplexity.SOBlock.mapAssign` along `Equiv.refl` is the identity, by
definitional eta).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The two assignment transfers are mutually inverse -/

section AssignEquiv

variable {Tag : Type} [Finite Tag] {d : ℕ} {A : Type}

/-- Merging a pulled assignment gives the assignment back: the transfer
`DescriptiveComplexity.SOBlock.pullAssign` is injective, with
`DescriptiveComplexity.SOBlock.mergeAssign` as a retraction on the other side. -/
theorem SOBlock.mergeAssign_pullAssign (B : Lax904597.SecondOrder.SOBlock)
    (ρ : B.Assignment (Tag × (Fin d → A))) : B.mergeAssign (B.pullAssign ρ) = ρ := by
  funext i y
  change ρ i (fun k => ((y k).1, fun j =>
    (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).2
      (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2)) = ρ i y
  refine congrArg (ρ i) (funext fun k => ?_)
  simp only [Equiv.symm_apply_apply]

end AssignEquiv

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (mergeAssign_pullAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section AssignEquiv

variable {Tag : Type} [Finite Tag] {d : ℕ} {A : Type}

variable (Tag d A) in
/-- **The states of the pulled walk are the states of the original walk on the
interpreted universe**: assignments of the pulled block on the base universe
correspond bijectively to assignments of the block on the tagged tuples. -/
def SOBlock.pullAssignEquiv (B : Lax904597.SecondOrder.SOBlock) :
    B.Assignment (Tag × (Fin d → A)) ≃ (B.pull Tag d).Assignment A where
  toFun := B.pullAssign
  invFun := B.mergeAssign
  left_inv := B.mergeAssign_pullAssign
  right_inv := B.pullAssign_mergeAssign

end AssignEquiv

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (pullAssignEquiv)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section AssignEquiv

variable {Tag : Type} [Finite Tag] {d : ℕ} {A : Type}

end AssignEquiv

/-! ### The pullback of a specification -/

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

/-- The interpretation extended with the order and along one copy of a block:
the layer through which the source and target sentences are pulled back. -/
noncomputable def FOInterpretation.ordExtendSO
    (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d) (B : Lax904597.SecondOrder.SOBlock) :
    Lax904597.Interpretations.FOInterpretation ((L.sum Language.order).sum (B.pull Tag d).lang)
      ((L'.sum Language.order).sum B.lang) Tag d :=
  I.ordExtend.extendSO B

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax480241Proofs.DescriptiveComplexity.FOInterpretation (ordExtendSO)

end Lax904597.Interpretations.FOInterpretation

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

/-- **The pullback of a specification through an interpretation**: the walk of
`spec` on the interpreted structure, written on the base structure. Its states
are the assignments of the pulled block; its three sentences are pulled back
through the order-extended interpretation, expanded along one copy of the block
for the endpoints and along two for the transition. -/
noncomputable def SOTCSpec.comap (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L')
    (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d) : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L where
  B := spec.B.pull Tag d
  step := ((I.ordExtendSO spec.B).extendSO spec.B).pullSentence spec.step
  src := (I.ordExtendSO spec.B).pullSentence spec.src
  tgt := (I.ordExtendSO spec.B).pullSentence spec.tgt

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (comap)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Starting states correspond.** -/
theorem SOTCSpec.comap_isSrc_iff (ρ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.IsSrc ρ ↔ (spec.comap I).IsSrc (spec.B.pullAssign ρ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  exact Iff.symm (((I.ordExtendSO spec.B).realize_pullSentence spec.src A).trans
    ((realize_sentence_of_equiv (I.ordExtend.extendSOEquiv spec.B A ρ) spec.src).trans
      (realize_sentence_of_equiv (spec.B.extendEquiv (I.ordExtendLEquiv A) ρ) spec.src)))

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (comap_isSrc_iff)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Accepting states correspond.** -/
theorem SOTCSpec.comap_isTgt_iff (ρ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.IsTgt ρ ↔ (spec.comap I).IsTgt (spec.B.pullAssign ρ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  exact Iff.symm (((I.ordExtendSO spec.B).realize_pullSentence spec.tgt A).trans
    ((realize_sentence_of_equiv (I.ordExtend.extendSOEquiv spec.B A ρ) spec.tgt).trans
      (realize_sentence_of_equiv (spec.B.extendEquiv (I.ordExtendLEquiv A) ρ) spec.tgt)))

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (comap_isTgt_iff)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Steps correspond**: a step of the specification on the interpreted
structure is a step of the pullback on the base structure. -/
theorem SOTCSpec.comap_step_iff (ρ σ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.Step ρ σ ↔ (spec.comap I).Step (spec.B.pullAssign ρ) (spec.B.pullAssign σ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  let := (spec.B.pull Tag d).structure₂ (L := L.sum Language.order) (spec.B.pullAssign ρ)
    (spec.B.pullAssign σ)
  exact Iff.symm ((((I.ordExtendSO spec.B).extendSO spec.B).realize_pullSentence
      spec.step A).trans
    ((realize_sentence_of_equiv
        ((I.ordExtendSO spec.B).extendSOEquiv spec.B A σ) spec.step).trans
      ((realize_sentence_of_equiv
          (spec.B.extendEquiv' (I.ordExtend.extendSOEquiv spec.B A ρ) σ) spec.step).trans
        (realize_sentence_of_equiv
          (spec.B.extendEquiv₂ (I.ordExtendLEquiv A) ρ σ) spec.step))))

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (comap_step_iff)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The pullback is correct**: it accepts the base structure exactly when the
specification accepts the interpreted one. -/
theorem SOTCSpec.comap_accepts_iff :
    letI := I.mapLinearOrder A
    spec.Accepts (I.Map A) ↔ (spec.comap I).Accepts A := by
  let := I.mapLinearOrder A
  exact SOTCSpec.accepts_congr (spec.B.pullAssignEquiv Tag d A) (spec.comap_step_iff I)
    (spec.comap_isSrc_iff I) (spec.comap_isTgt_iff I)

end Comap

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec

export Lax480241Proofs.DescriptiveComplexity.SOTCSpec (comap_accepts_iff)

end Lax134656.SecondOrderTransitiveClosure.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Comap

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L') (I : Lax904597.Interpretations.FOInterpretation (L.sum Language.order) L' Tag d)

variable {A : Type} [L.Structure A] [LinearOrder A]

end Comap

/-! ### Closure under reductions -/

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
  {Q : Lax904597.Problems.DecisionProblem L'}

/-- **SO(TC) definability is closed under ordered first-order reductions.** The
walk of the specification on the interpreted structure is a walk on the base
structure, its states the assignments of the pulled block. -/
theorem SOTCDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Q) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨spec.comap f.toInterpretation, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hspec (f.toInterpretation.Map A)).trans
    (spec.comap_accepts_iff f.toInterpretation))

end Closure

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax480241Proofs.DescriptiveComplexity.SOTCDefinable (of_orderedReduction)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
  {Q : Lax904597.Problems.DecisionProblem L'}

/-- SO(TC) definability is closed under first-order reductions. -/
theorem SOTCDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Q) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

end Lax480241Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax480241Proofs.DescriptiveComplexity.SOTCDefinable (of_foReduction)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
  {Q : Lax904597.Problems.DecisionProblem L'}

end Closure

end Lax480241Proofs.DescriptiveComplexity


