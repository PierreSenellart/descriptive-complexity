/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.PSpace
import Lax480241Proofs.DescriptiveComplexity.SecondOrderOrdered
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

namespace Lax134656.OrderFreeTransitiveClosure
end Lax134656.OrderFreeTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.SOTCSpec
end Lax480241Proofs.DescriptiveComplexity.SOTCSpec

namespace Lax480241Proofs.DescriptiveComplexity.SOTCSpecFree
end Lax480241Proofs.DescriptiveComplexity.SOTCSpecFree

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
export Lax904597.Interpretations (sumOrderStructure)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.OrderFreeTransitiveClosure (SOTCDefinableFree SOTCSpecFree)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# SO(TC) needs no order: the order is a guessed state component

`DescriptiveComplexity.SOTCDefinable`, like the clausal fragments and the
reachability logics, reads its three sentences over the *ordered* expansion of
the vocabulary and asks for the equivalence at every linear order on the
universe. For SO(TC) that hypothesis is removable, and this file removes it.

The reason it is removable here and not for SO-Horn, SO-Krom, FO(TC) or
FO(DTC) is the reason Fagin's theorem needs no order either: a walk over
assignments of a block can **guess** the order and carry it along. A state of
the walk is an assignment of relation variables, so one more binary variable
holds a candidate order; the source condition checks that it is a linear one
(`DescriptiveComplexity.linearGuard`), the transition condition says it does
not change, and every sentence of the original specification reads it in place
of the order symbol (`DescriptiveComplexity.orderElimLHom` and its two-copy
analogue below). The order is then a *component of the certificate*, exactly as
it is in the first block of a `Σₖ₊₁` sentence
(`DescriptiveComplexity.SecondOrderOrdered`), and nothing outside the
specification sees it.

A deterministic fragment cannot do this – guessing is what the Horn and Krom
kernels do not have, and their capture theorems are genuinely statements about
ordered structures – so `DescriptiveComplexity.PTIME`,
`DescriptiveComplexity.NL` and `DescriptiveComplexity.LOGSPACE` keep the
hypothesis while `DescriptiveComplexity.PSPACE` loses it.

## What this file contains

* `DescriptiveComplexity.SOTCSpecFree`, an SO(TC) specification whose three
  sentences live over the bare vocabulary expanded by copies of the block, with
  its semantics: acceptance is defined on structures carrying **no order at
  all**.
* `DescriptiveComplexity.SOTCSpecFree.toSpec`, reading such a specification as
  an ordinary one (the order symbol is simply never used), and
  `DescriptiveComplexity.SOTCSpecFree.accepts_toSpec_iff`.
* `DescriptiveComplexity.SOTCSpec.orderFree`, the converse construction: the
  order is guessed into the state, guarded at the source and frozen by every
  step (`DescriptiveComplexity.SOTCSpec.orderFree_accepts_iff`).
* `DescriptiveComplexity.SOTCDefinableFree` and the equivalence
  `DescriptiveComplexity.sotcDefinable_iff_free`, whence
  `DescriptiveComplexity.mem_PSPACE_iff_sotcDefinableFree`: membership in
  `PSPACE` is definability by an order-free specification.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Order-free specifications -/

namespace SOTCSpecFree

section Semantics

end Semantics

end SOTCSpecFree

/-! ### Reading an order-free specification as an ordinary one

The easy direction: a specification that does not mention the order is one that
happens never to use it. The language morphism below adds the order symbol to
the vocabulary, and the two structures agree on everything else. -/

section AddOrder

end AddOrder

namespace SOTCSpecFree

end SOTCSpecFree

/-! ### The order symbol, eliminated in favor of a state component

The hard direction. The block of the walk is extended by one binary relation
variable (`DescriptiveComplexity.SOBlock.withOrder`, shared with the
order elimination of `DescriptiveComplexity.SecondOrderOrdered`), the three
sentences read that variable in place of the order symbol, the source condition
adds `DescriptiveComplexity.linearGuard` and the transition condition adds that
the variable does not change. -/

section OrderElim

end OrderElim

/-! ### The order-free reading of a specification -/

section Free

variable (spec : Lax134656.SecondOrderTransitiveClosure.SOTCSpec L)

variable {spec} {A : Type} [instL : L.Structure A]

section Transport

variable [lo : LinearOrder A] {B : Lax904597.SecondOrder.SOBlock} (ρ σ : B.withOrder.Assignment A)
  (hord : ∀ w : Fin 2 → A, ρ (Sum.inl ()) w ↔ w 0 ≤ w 1)

include hord

/-- A sentence over the ordered expansion and one copy of a block says, read
through `DescriptiveComplexity.orderElimLHom` at a state whose order variable
holds the order, what it says of the underlying assignment. -/
theorem realize_orderElim_one (φ : ((L.sum Language.order).sum B.lang).Sentence) :
    @Sentence.Realize _ A (@Lax480241.Expansions.SOBlock.structure₁ L B.withOrder A instL ρ)
        ((orderElimLHom L B).onSentence φ) ↔
      @Sentence.Realize _ A
        (@Lax480241.Expansions.SOBlock.structure₁ (L.sum Language.order) B A (Lax904597.Interpretations.sumOrderStructure L A) (B.restPart ρ))
        φ := by
  let := @Lax480241.Expansions.SOBlock.structure₁ (L.sum Language.order) B A (Lax904597.Interpretations.sumOrderStructure L A) (B.restPart ρ)
  let := @Lax480241.Expansions.SOBlock.structure₁ L B.withOrder A instL ρ
  have : @LHom.IsExpansionOn _ _ (orderElimLHom L B) A
      (@Lax480241.Expansions.SOBlock.structure₁ (L.sum Language.order) B A (Lax904597.Interpretations.sumOrderStructure L A) (B.restPart ρ))
      (@Lax480241.Expansions.SOBlock.structure₁ L B.withOrder A instL ρ) :=
    orderElimLHom_isExpansionOn L B A instL lo ρ hord
  exact LHom.realize_onSentence (M := A) (orderElimLHom L B) φ

end Transport

section Semantics

end Semantics

end Free

/-! ### Order-free SO(TC) definability -/

end Lax480241Proofs.DescriptiveComplexity


