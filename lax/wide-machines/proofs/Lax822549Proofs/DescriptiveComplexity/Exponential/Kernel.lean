/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Exponential.Class
import Lax822549Proofs.DescriptiveComplexity.SecondOrderOrdered
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

/-!
# What a NEXPTIME source problem looks like

`DescriptiveComplexity.ExpDefinable` `DescriptiveComplexity.NP` is the class the
hardness proof for `DescriptiveComplexity.WideAccept` starts from, and it is
stated as an existential over an expansion and a *problem* of `NP`. A machine
cannot be programmed against that. This file puts it in the normal form a program
is written against:

> **an expansion, one block of guessed relation variables, and a first-order
> kernel** – `DescriptiveComplexity.NexKernel` – the problem holding at a
> structure exactly when some assignment of the block satisfies the kernel over
> its expansion.

That is the same shape as the data of the EXPSPACE program – an expansion, a
block, a first-order body – with the block's relation variables **guessed** once
rather than iterated to a fixed point, which is the whole difference between the
two programs.

## The order

The kernel is stated over `L.sum FirstOrder.Language.order`, one language wider
than `DescriptiveComplexity.SigmaSODefinable` supplies. Nothing is added by that:
a machine has an order on its universe whatever the source says, the atoms of an
ordered kernel are what the program's atom machinery is written for, and a
sentence that mentions no order symbol is a sentence that may. The transport is
`DescriptiveComplexity.orderAddLHom`, the dual of
`DescriptiveComplexity.orderElimLHom` – which eliminates an order symbol by
re-quantifying it inside a block, and is the direction that costs something.

Which linear order is on the expanded universe is left to the consumer: the
normal form holds at **every** one, so a reduction may choose the order its
encoding induces and pay nothing for the choice.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Adding an order symbol to a kernel -/

section AddOrder

variable {L : Language.{0, 0}}

/-- **The language morphism adding an order symbol** to a first-order kernel
over a block: every symbol goes to itself, and the order symbol of the target is
simply not in the image. The dual of
`DescriptiveComplexity.orderElimLHom`. -/
def orderAddLHom (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) :
    L.sum B.lang →ᴸ (L.sum Language.order).sum B.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => nomatch g
  onRelation {_n} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s => Sum.inr s

/-- **The ordered structure is an expansion along the morphism**, whatever the
order: the order symbol is the only new one and no formula in the image mentions
it. -/
theorem orderAddLHom_isExpansionOn (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (A : Type)
    (instA : L.Structure A) (lo : LinearOrder A) (ρ : B.Assignment A) :
    @LHom.IsExpansionOn _ _ (orderAddLHom L B) A
      (@sumStructure L B.lang A instA (B.structure ρ))
      (@sumStructure (L.sum Language.order) B.lang A
        (letI := instA; letI := lo; Lax904597.Interpretations.sumOrderStructure L A) (B.structure ρ)) := by
  let := instA
  let := lo
  let := B.structure ρ
  exact
    { map_onFunction := fun {_n} f _x => by
        match f with
        | Sum.inl g => rfl
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {_n} r _x => by
        match r with
        | Sum.inl s => rfl
        | Sum.inr s => rfl }

/-- **Adding the order symbol changes no meaning.** -/
theorem realize_orderAdd (B : Lax904597.SecondOrder.SOBlock) (A : Type) [instA : L.Structure A] [lo : LinearOrder A]
    (ρ : B.Assignment A) (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure (L.sum Language.order) B.lang A (Lax904597.Interpretations.sumOrderStructure L A) (B.structure ρ))
        ((orderAddLHom L B).onSentence φ) ↔
      @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A instA (B.structure ρ)) φ :=
  @LHom.realize_onSentence _ _ A (@sumStructure L B.lang A instA (B.structure ρ))
    (@sumStructure (L.sum Language.order) B.lang A (Lax904597.Interpretations.sumOrderStructure L A) (B.structure ρ))
    (orderAddLHom L B) (orderAddLHom_isExpansionOn L B A instA lo ρ) φ

/-- **A `Σ₁` definition, with its kernel read over the ordered expansion.** The
one block is the certificate the machine guesses; the kernel is what it checks;
and the statement holds at every linear order, so a consumer may impose its
own. -/
theorem exists_orderedKernel [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax904597.SecondOrder.SigmaSODefinable 1 P) :
    ∃ (B : Lax904597.SecondOrder.SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ ∃ ρ : B.Assignment A, @Sentence.Realize _ A
          (@sumStructure (L.sum Language.order) B.lang A (Lax904597.Interpretations.sumOrderStructure L A)
            (B.structure ρ)) φ := by
  obtain ⟨Bs, hlen, φ, hspec⟩ := h
  match Bs, hlen with
  | [B], _ =>
    refine ⟨B, (orderAddLHom L B).onSentence φ, fun A _ _ _ _ => (hspec A).trans ?_⟩
    -- Satisfaction of a single existential block unfolds definitionally.
    exact exists_congr fun ρ => (realize_orderAdd B A ρ φ).symm

end AddOrder

/-! ### The normal form of a NEXPTIME source -/

section Kernel

variable {L : Language.{0, 0}}

/-- **The data a NEXPTIME hardness program is written against**: an exponential
expansion, one block of guessed relation variables, and a first-order kernel over
the expanded vocabulary, its order, and the block. -/
structure NexKernel (L : Language.{0, 0}) : Type 1 where
  /-- The exponential expansion whose points the machine's tape addresses. -/
  X : Lax480241.Expansions.ExpExpansion L
  /-- The relation variables the machine guesses. -/
  B : Lax904597.SecondOrder.SOBlock
  /-- The first-order sentence the machine checks. -/
  ker : ((X.E.sum Language.order).sum B.lang).Sentence

namespace NexKernel

variable (K : NexKernel L)

/-- **What the kernel says**: some assignment of the guessed block satisfies it.
This is the predicate the machine's run has to be equivalent to – guess, then
check – and it is stated at an arbitrary linear order on the universe, the
reduction's own being one. -/
def Holds (M : Type) [instM : K.X.E.Structure M] [LinearOrder M] : Prop :=
  ∃ ρ : K.B.Assignment M, @Sentence.Realize _ M
    (@sumStructure (K.X.E.sum Language.order) K.B.lang M
      (Lax904597.Interpretations.sumOrderStructure K.X.E M) (K.B.structure ρ)) K.ker

end NexKernel

end Kernel

end Lax822549Proofs.DescriptiveComplexity


