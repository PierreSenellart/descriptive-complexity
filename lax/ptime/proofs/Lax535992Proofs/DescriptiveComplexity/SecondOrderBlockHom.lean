/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax535992Proofs.DescriptiveComplexity.FixedPointStep
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992Proofs.DescriptiveComplexity.SOBlock
end Lax535992Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Morphisms of second-order blocks

An arity-preserving map of relation variables induces a morphism of the
blocks' vocabularies (`DescriptiveComplexity.SOBlock.homLHom`), and a sentence
over a base vocabulary expanded by the source block transports to one over
the base expanded by the target block
(`DescriptiveComplexity.SOBlock.realize_homSentence`): realization against an
assignment of the target block is realization against its pullback along the
map (`DescriptiveComplexity.SOBlock.homAssign`).

This is the bookkeeping that reads a formula written for one block inside a
*larger* block containing a copy of it. Its first consumer is the FO(≤, IFP)
→ FO(LFP) translation (`DescriptiveComplexity.FixedPointInflationaryLFP`),
whose output sentence mentions the original relation variables while the
translated program computes them as one group of a larger block; the
invariant-structure simulations of `DescriptiveComplexity.Invariant.Simulation`
want it for the same reason.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : Lax904597.SecondOrder.SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

/-- The vocabulary morphism induced by an arity-preserving map of relation
variables. -/
def homLHom : B.lang →ᴸ B'.lang where
  onFunction := fun {_} g => isEmptyElim g
  onRelation := fun {_} r => ⟨f r.1, (hf r.1).trans r.2⟩

end SOBlock

end Lax535992Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax535992Proofs.DescriptiveComplexity.SOBlock (homLHom)

end Lax904597.SecondOrder.SOBlock

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : Lax904597.SecondOrder.SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

/-- The pullback of an assignment of the target block along the map: each
source variable reads its image. -/
def homAssign {A : Type} (σ : B'.Assignment A) : B.Assignment A :=
  fun i x => σ (f i) fun j => x (Fin.cast (hf i) j)

end SOBlock

end Lax535992Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax535992Proofs.DescriptiveComplexity.SOBlock (homAssign)

end Lax904597.SecondOrder.SOBlock

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : Lax904597.SecondOrder.SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

variable {L : Language.{0, 0}} {A : Type} [L.Structure A]

/-- The vocabulary morphism is an expansion between the two induced
structures. -/
theorem homLHom_isExpansionOn (σ : B'.Assignment A) :
    @LHom.IsExpansionOn _ _ (homLHom f hf (B := B)) A
      (B.structure (B.homAssign f hf σ)) (B'.structure σ) := by
  let := B.structure (B.homAssign f hf σ)
  let := B'.structure σ
  refine ⟨fun {n} g => isEmptyElim g, fun {n} r x => ?_⟩
  rfl

end SOBlock

end Lax535992Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax535992Proofs.DescriptiveComplexity.SOBlock (homLHom_isExpansionOn)

end Lax904597.SecondOrder.SOBlock

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : Lax904597.SecondOrder.SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

variable {L : Language.{0, 0}} {A : Type} [L.Structure A]

/-- **Transport of a sentence along a block morphism**: realization over the
target block's assignment is realization of the original sentence over the
pulled-back assignment. -/
theorem realize_homSentence (σ : B'.Assignment A) (φ : (L.sum B.lang).Sentence) :
    (@Sentence.Realize _ A (B'.structure₁ (L := L) σ)
      ((LHom.sumMap (LHom.id L) (homLHom f hf (B := B))).onSentence φ)) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) (B.homAssign f hf σ)) φ := by
  let := B.structure (B.homAssign f hf σ)
  let := B'.structure σ
  have := homLHom_isExpansionOn f hf (A := A) σ
  exact LHom.realize_onSentence (M := A)
    (φ := LHom.sumMap (LHom.id L) (homLHom f hf (B := B))) (ψ := φ)

end SOBlock

end Lax535992Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax535992Proofs.DescriptiveComplexity.SOBlock (realize_homSentence)

end Lax904597.SecondOrder.SOBlock

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : Lax904597.SecondOrder.SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

variable {L : Language.{0, 0}} {A : Type} [L.Structure A]

end SOBlock

end Lax535992Proofs.DescriptiveComplexity


