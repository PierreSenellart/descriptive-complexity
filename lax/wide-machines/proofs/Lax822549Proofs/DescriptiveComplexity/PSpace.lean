/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull
import Lax822549Proofs.DescriptiveComplexity.Hierarchy
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

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.SOTCDefinable
end Lax822549Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

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

namespace Lax822549Proofs.DescriptiveComplexity

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

end SigmaOne

end Lax822549Proofs.DescriptiveComplexity


