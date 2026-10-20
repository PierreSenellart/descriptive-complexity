/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Exponential.Class
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax822549Proofs.DescriptiveComplexity.FixedPoint
import Lax822549Proofs.DescriptiveComplexity.Hierarchy
import Lax822549Proofs.DescriptiveComplexity.OrderWalk
import Lax822549Proofs.DescriptiveComplexity.FixedPointPartialMachine
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

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.SecondOrderFixedPoints
end Lax480241.SecondOrderFixedPoints

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax822549Proofs.DescriptiveComplexity.SOLFPDefinable
end Lax822549Proofs.DescriptiveComplexity.SOLFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable
end Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (LFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (PFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax480241.SecondOrderFixedPoints (SOLFPDefinable SOPFPDefinable)
end Lax822549Proofs.DescriptiveComplexity

/-!
# Second-order fixed points: SO(LFP) and SO(PFP)

> A **second-order** fixed point is a first-order fixed point **read over a
> structure whose universe is the assignments of a second-order block**.

A relation over an exponential expansion of `A` is a set of tuples of
second-order objects of `A`, so iterating a definable operator on it is a
second-order induction; and the first-order fixpoint logics, read there, are
the second-order ones. That is the definition of
`DescriptiveComplexity.SOLFPDefinable` and
`DescriptiveComplexity.SOPFPDefinable`, and the two classes
`DescriptiveComplexity.EXPTIME` and `DescriptiveComplexity.EXPSPACE` are named
after them.

**No third-order syntax is introduced**, and none is needed. The fixpoint
variable of SO(LFP) is a relation over the expanded universe, hence a
third-order object over `A`; but the expansion has already made those objects
the first-order elements of a new sort, so the syntax is the ordinary
`FirstOrder.Language.BoundedFormula` layer and the fixpoint is the ordinary
`DescriptiveComplexity.LFPDefinable`. This is the standard type-lowering
translation of higher-order logic into many-sorted first-order logic over the
power type ([Henkin 1950][henkin1950completeness]), which is why “SO(LFP) over
`A`” and “FO(LFP) over the expansion of `A`” are two presentations of one
object.

## The bridge theorems

`DescriptiveComplexity.solfpDefinable_iff_expDefinable` and
`DescriptiveComplexity.sopfpDefinable_iff_expDefinable` say that the two logics
are `DescriptiveComplexity.ExpDefinable` at `PTIME` and at `PSPACE`. Each is a
congruence down to the library's own capture theorem
(`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`,
`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`) applied at the expanded
vocabulary, which is relational by the `eRelational` field of an expansion.
There is no mathematics in them, and that is the point of the design: they let
every later statement be proved once, about
`DescriptiveComplexity.ComplexityClass.exp` at an arbitrary class, and read off
at the exponential classes.

## Literature

These are *definitions* here, so nothing is claimed. Naming the classes after
these logics follows [Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint], which
parameterizes fixpoint logic by operator and iteration construct and obtains
characterizations up to EXPTIME. That work is stated in the *relational*
(order-free, generic) setting, so it must not be cited as a capture theorem for
the classes defined here; what this development proves in its place are the
bridge theorems above, which are about this library's own classes and owe the
literature nothing. The order these two definitions carry is nevertheless
removable (`DescriptiveComplexity.solfpDefinable_iff_free`,
`DescriptiveComplexity.sopfpDefinable_iff_free`): the expansion can guess it,
and the resulting union of copies costs one existential – paid for by guessing
the copy in `DescriptiveComplexity.Exponential.FreeSpace`, and by naming it with
a point in `DescriptiveComplexity.Exponential.FreeTime`.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The two logics -/

/-! ### The bridge theorems -/

/-- **SO(≤, PFP) is polynomial space over an expanded universe**: the
Abiteboul–Vianu capture theorem, read at the expanded vocabulary. -/
theorem sopfpDefinable_iff_expDefinable (P : Lax904597.Problems.DecisionProblem L) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinable P ↔ ExpDefinable PSPACE P :=
  exists_congr fun _X => exists_congr fun Q =>
    and_congr_left' (pfpDefinable_iff_mem_PSPACE Q)

/-! ### Closure under reductions, inherited

The three membership obligations of
`DescriptiveComplexity.ComplexityClass.ofMem` are *borrowed* through the bridge
theorems rather than proved: `DescriptiveComplexity.Exponential.Class` proved
them once, for `ExpDefinable C` at an arbitrary `C`. -/

variable {L' : Language.{0, 0}} [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

theorem SOPFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : Lax480241.SecondOrderFixedPoints.SOPFPDefinable Q) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinable P :=
  (sopfpDefinable_iff_expDefinable P).mpr
    (((sopfpDefinable_iff_expDefinable Q).mp h).of_foReduction f)

end Lax822549Proofs.DescriptiveComplexity

namespace Lax480241.SecondOrderFixedPoints.SOPFPDefinable

export Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable (of_foReduction)

end Lax480241.SecondOrderFixedPoints.SOPFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

variable {L' : Language.{0, 0}} [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

theorem SOPFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : Lax480241.SecondOrderFixedPoints.SOPFPDefinable Q) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinable P :=
  (sopfpDefinable_iff_expDefinable P).mpr
    (((sopfpDefinable_iff_expDefinable Q).mp h).of_orderedReduction f)

end Lax822549Proofs.DescriptiveComplexity

namespace Lax480241.SecondOrderFixedPoints.SOPFPDefinable

export Lax822549Proofs.DescriptiveComplexity.SOPFPDefinable (of_orderedReduction)

end Lax480241.SecondOrderFixedPoints.SOPFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

variable {L' : Language.{0, 0}} [L'.IsRelational] {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}

theorem sopfpDefinable_congr {P P' : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) :
    Lax480241.SecondOrderFixedPoints.SOPFPDefinable P ↔ Lax480241.SecondOrderFixedPoints.SOPFPDefinable P' :=
  (sopfpDefinable_iff_expDefinable P).trans
    ((expDefinable_congr h).trans (sopfpDefinable_iff_expDefinable P').symm)

end Lax822549Proofs.DescriptiveComplexity


