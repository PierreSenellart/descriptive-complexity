/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Block
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
export Lax480241.Expansions.SOBlock (replicate replicateAssign structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# Exponential expansions: reading a structure over its second-order objects

The one construction the exponential classes are built from. An **exponential
expansion** of `L`-structures maps a finite ordered `L`-structure `A` to a
structure over another vocabulary `E` whose *universe is a definable set of
tagged assignments of a second-order block*. A block with a variable of arity
`a` has `2^(n^a)` assignments on a universe of size `n`, so the expanded
universe is exponentially larger than `A`, and a resource bound read there is
one exponential higher than the same bound read on `A`.

The data (`DescriptiveComplexity.ExpExpansion`) mirrors
`DescriptiveComplexity.RelFOInterpretation` one level up:

* a finite `Tag` type and a block `B`, whose pairs `(t, ρ)` are the candidate
  points – the analogue of the tagged tuples `Tag × A^dim`;
* a **domain sentence** `dom t` per tag, over the ordered base vocabulary
  expanded by one copy of the block, cutting the universe down to a definable
  set (`DescriptiveComplexity.ExpExpansion.Map`, a subtype);
* a **defining sentence** `relSentence r τ` per relation symbol of `E` and per
  tuple of tags, over the ordered base vocabulary expanded by as many copies of
  the block as the symbol has arguments
  (`DescriptiveComplexity.SOBlock.replicate`).

Three design points, each paying for itself downstream.

**The tags are part of the data, not a separate dimension.** A `d`-tuple of
points is a tag tuple together with an assignment of the replicated block, so
composing an expansion with a first-order interpretation gives an expansion
again, exactly rather than up to an embedding
(`DescriptiveComplexity.Exponential.Pull`). Without the tag factor every
hardness discharge would owe a relativization argument.

**There is a domain sentence.** Hardness in this library is cofinal hardness
and `DescriptiveComplexity.cofinalHard_iff` hands out *relativized* reductions
`≤ʳᶠᵒ[≤]`, whose target universe is already a subtype; an expansion composed
with one is again an expansion only if expansions may carve out their universe
too. `dom_nonempty` is then the same obligation, for the same reason, as in
`DescriptiveComplexity.RelOrderedFOReduction`.

**The sentences see the order, the problem does not.** This is the discipline
of `DescriptiveComplexity.SOTCSpec`: the capture theorems this development
builds on are the ordered ones, while order-invariance is what makes the notion
a `DescriptiveComplexity.DecisionProblem`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### The data -/

attribute [instance] Lax480241.Expansions.ExpExpansion.tagFinite Lax480241.Expansions.ExpExpansion.eRelational

namespace ExpExpansion

variable (X : Lax480241.Expansions.ExpExpansion L)

/-! ### The expanded universe -/

variable {X}

variable (X)

variable {X}

@[simp]
theorem pt_tag {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag)
    (ρ : X.B.Assignment A) (h : Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ)) : (Lax480241.Expansions.ExpExpansion.pt t ρ h).1.1 = t :=
  rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pt_tag)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace ExpExpansion

variable (X : Lax480241.Expansions.ExpExpansion L)

variable {X}

variable (X)

variable {X}

@[simp]
theorem pt_assign {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag)
    (ρ : X.B.Assignment A) (h : Lax480241.Expansions.ExpExpansion.DomHolds (X := X) (t, ρ)) : (Lax480241.Expansions.ExpExpansion.pt t ρ h).1.2 = ρ :=
  rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (pt_assign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace ExpExpansion

variable (X : Lax480241.Expansions.ExpExpansion L)

variable {X}

variable (X)

variable {X}

/-- Two points of the expanded universe are equal as soon as their tags and
their assignments are: the domain condition is a proof. -/
theorem map_ext {A : Type} [L.Structure A] [LinearOrder A] {x y : X.Map A}
    (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext_iff.mpr ⟨h₁, h₂⟩)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (map_ext)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace ExpExpansion

variable (X : Lax480241.Expansions.ExpExpansion L)

variable {X}

variable (X)

variable {X}

variable (X)

theorem relMap_map {A : Type} [L.Structure A] [LinearOrder A] {n : ℕ} (r : X.E.Relations n)
    (xs : Fin n → X.Map A) :
    RelMap r xs ↔
      @Sentence.Realize _ A
        ((X.B.replicate n).structure₁ (L := L.sum Language.order)
          (X.B.replicateAssign fun i => (xs i).1.2))
        (X.relSentence r fun i => (xs i).1.1) :=
  Iff.rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (relMap_map)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace ExpExpansion

variable (X : Lax480241.Expansions.ExpExpansion L)

variable {X}

variable (X)

variable {X}

variable (X)

/-! ### Finiteness and nonemptiness -/

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


