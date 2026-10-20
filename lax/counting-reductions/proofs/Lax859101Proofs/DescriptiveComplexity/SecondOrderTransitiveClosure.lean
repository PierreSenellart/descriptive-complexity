/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.SecondOrder
import Lax859101Proofs.DescriptiveComplexity.Ordered
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax859101Proofs.DescriptiveComplexity.SOBlock
end Lax859101Proofs.DescriptiveComplexity.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
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

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Expanding a structure by one or two copies of a block -/

section Expand

end Expand

/-! ### Specifications -/

namespace SOTCSpec

section Semantics

end Semantics

/-! ### Transfer along a bijection of states

Acceptance only depends on the walk up to a bijection of its states. Stated for
two specifications over two vocabularies, since the pullback through an
interpretation relates a specification over the base structure to one over the
interpreted structure. -/

section Transfer

end Transfer

/-! ### Isomorphism-invariance -/

section Iso

end Iso

end SOTCSpec

/-! ### SO(TC) definability -/

end Lax859101Proofs.DescriptiveComplexity


