/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.TagBits
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# A guessed block that is a point of the expanded universe

`DescriptiveComplexity.SOBlock.tagGuardF` says a guessed assignment *names a
tag*. A quantifier of the translation lemma ranges over the points of
`X.Map A`, which is less: a point must also satisfy its tag's **domain
sentence**. This file conjoins the two into
`DescriptiveComplexity.ExpExpansion.pointGuardF`, the guard every peeled
quantifier carries – existentially as a conjunct, universally as a hypothesis.

The only new bookkeeping is reading `X.dom t`, a sentence over the block
`X.B`, inside the tag-extended block `X.B.withTag X.Tag`. That is
`DescriptiveComplexity.SOBlock.homLHom` at the inclusion `Sum.inr`, whose
arity condition is `rfl` and whose transported assignment is
`DescriptiveComplexity.SOBlock.dropTag` exactly – so the transport lemma is
`DescriptiveComplexity.SOBlock.realize_homSentence` with nothing to prove.

The domain sentence is selected by the tag *bits* rather than statically, so it
appears once per tag, guarded by that tag's bit. Exactly one bit is set, so
exactly one of those implications has a true hypothesis.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### Reading a block sentence inside the tag-extended block -/

variable (L) in
/-- The inclusion of a block into its tag extension, as a vocabulary map: the
tag variables are simply not mentioned. -/
def withTagLHom (B : Lax904597.SecondOrder.SOBlock) (T : Type) [Finite T] :
    ((L.sum Language.order).sum B.lang) →ᴸ ((L.sum Language.order).sum (B.withTag T).lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (Sum.inr : B.ι → (B.withTag T).ι) fun _ => rfl)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (withTagLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-- **Reading a block sentence in the extension is reading it at the dropped
assignment**: the tag bits are invisible to it. -/
theorem realize_withTagLHom {B : Lax904597.SecondOrder.SOBlock} {T : Type} [Finite T] {A : Type}
    [L.Structure A] [LinearOrder A] (σ : (B.withTag T).Assignment A)
    (φ : ((L.sum Language.order).sum B.lang).Sentence) :
    (@Sentence.Realize _ A
        ((B.withTag T).structure₁ (L := L.sum Language.order) σ)
        ((withTagLHom L B T).onSentence φ) ↔
      @Sentence.Realize _ A
        (B.structure₁ (L := L.sum Language.order) (SOBlock.dropTag σ)) φ) :=
  SOBlock.realize_homSentence (B := B) (B' := B.withTag T) Sum.inr (fun _ => rfl) σ φ

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_withTagLHom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

/-! ### The point guard -/

/-- **The guard saying a guessed block is a point of the expanded universe**:
its tag bits name a tag, and its assignment satisfies that tag's domain
sentence. -/
noncomputable def pointGuardF :
    ((L.sum Language.order).sum (X.B.withTag X.Tag).lang).Sentence :=
  SOBlock.tagGuardF X.B X.Tag ⊓
    listInf ((finEnum X.Tag).map fun t =>
      SOBlock.tagBitF X.B X.Tag t ⟹ (withTagLHom L X.B X.Tag).onSentence (X.dom t))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pointGuardF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

/-- **The guard is exactly “this is a point”.** -/
theorem realize_pointGuardF (σ : (X.B.withTag X.Tag).Assignment A) :
    (@Sentence.Realize _ A
        ((X.B.withTag X.Tag).structure₁ (L := L.sum Language.order) σ) X.pointGuardF ↔
      ∃ (t : X.Tag) (ρ : X.B.Assignment A),
        σ = SOBlock.tagAssign t ρ ∧ Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ)) := by
  let := (X.B.withTag X.Tag).structure₁ (L := L.sum Language.order) σ
  rw [pointGuardF, Sentence.Realize, Formula.realize_inf, realize_listInf]
  constructor
  · rintro ⟨hguard, hdom⟩
    obtain ⟨t, ρ, rfl⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) σ).mp hguard
    refine ⟨t, ρ, rfl, ?_⟩
    have h := hdom _ (List.mem_map.mpr ⟨t, mem_finEnum t, rfl⟩)
    rw [Formula.realize_imp] at h
    exact (realize_withTagLHom _ (X.dom t)).mp
      (h ((SOBlock.realize_tagBitF (L := L.sum Language.order) _ t).mpr rfl))
  · rintro ⟨t, ρ, rfl, hdt⟩
    refine ⟨(SOBlock.realize_tagGuardF (L := L.sum Language.order) _).mpr ⟨t, ρ, rfl⟩,
      fun ψ hψ => ?_⟩
    obtain ⟨t', -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_imp]
    intro hbit
    have ht' : t' = t := (SOBlock.realize_tagBitF (L := L.sum Language.order) _ t').mp hbit
    subst ht'
    exact (realize_withTagLHom _ (X.dom t')).mpr hdt

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_pointGuardF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L)

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


