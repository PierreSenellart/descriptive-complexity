/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Block
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

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# Writing an expansion's sentences with iterated block expansions

An exponential expansion defines an `n`-ary symbol by a sentence over the base
vocabulary expanded by `DescriptiveComplexity.SOBlock.replicate` – *one* block
holding `n` copies. The rest of the library writes its multi-state sentences
over *iterated* expansions instead: one copy of `B.lang` per state, stacked as
nested sums (`DescriptiveComplexity.SOBlock.structure₁`,
`DescriptiveComplexity.SOBlock.structure₂` – the shape of an
`DescriptiveComplexity.SOTCSpec`).

This file bridges the two presentations at the arities an expansion actually
needs, one and two:

* `DescriptiveComplexity.SOBlock.oneLHom` reads a sentence over `L ⊕ B.lang`
  inside `L ⊕ (B.replicate 1).lang`;
* `DescriptiveComplexity.SOBlock.twoLHom` reads a sentence over
  `(L ⊕ B.lang) ⊕ B.lang` inside `L ⊕ (B.replicate 2).lang`, the first copy
  becoming copy `0` and the second copy `1`.

Both transports are definitional on assignments – reading copy `k` of a
replicated assignment *is* reading the `k`-th assignment – so their correctness
lemmas are `DescriptiveComplexity.SOBlock.realize_homSentence` and one
`LHom.IsExpansionOn` whose relation case is `rfl`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

/-! ### One copy -/

variable (L) in
/-- Reading a sentence over one copy of a block inside the block replicated
once. -/
def oneLHom : (L.sum B.lang) →ᴸ (L.sum (B.replicate 1).lang) :=
  LHom.sumMap (LHom.id L) (homLHom (fun i => ((0 : Fin 1), i)) fun _ => rfl)

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (oneLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

variable {A : Type} [L.Structure A]

/-- **Correctness of the one-copy reading**: the replicated assignment holds
the original assignment in its single copy. -/
theorem realize_oneLHom (ρs : Fin 1 → B.Assignment A) (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize _ A ((B.replicate 1).structure₁ (L := L) (B.replicateAssign ρs))
        ((B.oneLHom L).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) (ρs 0)) φ :=
  realize_homSentence (B := B) (B' := B.replicate 1) (fun i => ((0 : Fin 1), i)) (fun _ => rfl)
    (B.replicateAssign ρs) φ

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (realize_oneLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

variable {A : Type} [L.Structure A]

/-! ### Two copies -/

variable (L) in
/-- Reading a sentence over two stacked copies of a block inside the block
replicated twice: the inner copy becomes copy `0`, the outer copy `1`. -/
def twoLHom : ((L.sum B.lang).sum B.lang) →ᴸ (L.sum (B.replicate 2).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl g) => Sum.inl g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl s
    | Sum.inl (Sum.inr s) => Sum.inr (B.replicateSym 0 s)
    | Sum.inr s => Sum.inr (B.replicateSym 1 s)

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (twoLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

variable {A : Type} [L.Structure A]

/-- The two-copy reading is an expansion between the stacked structure and the
replicated one. Stated at a *family* of two assignments rather than at a pair,
since that is the shape a defining sentence of an expansion is realized
against. -/
theorem twoLHom_isExpansionOn (ρs : Fin 2 → B.Assignment A) :
    @LHom.IsExpansionOn _ _ (B.twoLHom L) A (B.structure₂ (L := L) (ρs 0) (ρs 1))
      ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)) := by
  let := B.structure₂ (L := L) (ρs 0) (ρs 1)
  let := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  refine ⟨fun {_} f _ => ?_, fun {_} r _ => ?_⟩
  · match f with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match r with
    | Sum.inl (Sum.inl _) => rfl
    | Sum.inl (Sum.inr _) => rfl
    | Sum.inr _ => rfl

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (twoLHom_isExpansionOn)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

variable {A : Type} [L.Structure A]

/-- **Correctness of the two-copy reading**: the replicated assignment holds
the current state in copy `0` and the next one in copy `1`. -/
theorem realize_twoLHom (ρs : Fin 2 → B.Assignment A)
    (φ : ((L.sum B.lang).sum B.lang).Sentence) :
    @Sentence.Realize _ A ((B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs))
        ((B.twoLHom L).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₂ (L := L) (ρs 0) (ρs 1)) φ :=
  letI := B.structure₂ (L := L) (ρs 0) (ρs 1)
  letI := (B.replicate 2).structure₁ (L := L) (B.replicateAssign ρs)
  haveI := B.twoLHom_isExpansionOn (L := L) ρs
  LHom.realize_onSentence (M := A) (B.twoLHom L) φ

end SOBlock

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (realize_twoLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock)

variable {A : Type} [L.Structure A]

/-! ### Two copies, the other way

`DescriptiveComplexity.SOBlock.twoLHom` reads a *stacked* sentence inside a
replicated one, which is what an expansion's defining sentence needs. A walk
over an expanded universe needs the converse: an
`DescriptiveComplexity.SOTCSpec` states its transition over two stacked copies
of its state block, while everything said about two points of an expanded
universe – their order, their equality, one being the successor of the other –
is written over the block replicated twice. -/

end SOBlock

end Lax480241Proofs.DescriptiveComplexity


