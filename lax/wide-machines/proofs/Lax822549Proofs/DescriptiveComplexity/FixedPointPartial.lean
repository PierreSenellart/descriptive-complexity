/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.FixedPointInflationary
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

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax822549Proofs.DescriptiveComplexity.IFPDefinable
end Lax822549Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity.IFPDefinableFree
end Lax822549Proofs.DescriptiveComplexity.IFPDefinableFree

namespace Lax822549Proofs.DescriptiveComplexity.PFPDefinable
end Lax822549Proofs.DescriptiveComplexity.PFPDefinable

namespace Lax822549Proofs.DescriptiveComplexity.PFPDefinableFree
end Lax822549Proofs.DescriptiveComplexity.PFPDefinableFree

namespace Lax822549Proofs.DescriptiveComplexity.StepDef
end Lax822549Proofs.DescriptiveComplexity.StepDef

namespace Lax822549Proofs.DescriptiveComplexity.StepDef.PFPHolds
end Lax822549Proofs.DescriptiveComplexity.StepDef.PFPHolds

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (IFPDefinableFree PFPDefinable PFPDefinableFree)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
export Lax134656.PartialFixedPoint.StepDef (PFPHolds partStage)
end Lax535992.InflationaryFixedPoint.StepDef

/-!
# FO(PFP): first-order logic with a partial fixed point

The partial fixed-point logic ([Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` by *replacement* – each stage is
one application of the step formulas to the previous one – and read the
output at the first stable stage, if the iteration stabilizes at all.

## The divergence convention

`DescriptiveComplexity.StepDef.PFPHolds` requires convergence: a diverging
iteration makes the definition *false*, whatever the output sentence. The
textbook semantics instead assigns a diverging iteration the empty relations
and reads the output there; the two readings are compared precisely by
`DescriptiveComplexity.StepDef.realize_pfpValue_iff` – they agree unless the
iteration diverges *and* the output holds at the empty assignment. The
convergence-requiring convention is chosen deliberately:

* it is what makes the translation to SO(TC) direct
  (`DescriptiveComplexity.FixedPointPartialSpace`): acceptance of the walk
  *is* «some stable stage satisfying the output is reachable», with no
  divergence detection – on unordered structures, none is available;
* every definition in the textbook semantics whose output fails on the empty
  assignment means the same thing here, and conversely a definition of this
  file is read in the textbook semantics by guarding its output with «the
  state is a fixed point of the step» – the guard is first-order
  (`DescriptiveComplexity.StepDef.isFixedPtF` in
  `DescriptiveComplexity.FixedPointPartialSpace`), and it fails at the empty
  assignment of a diverging iteration, since a diverging iteration's empty
  *start* is not a fixed point.

As for IFP, there is an ordered notion (`DescriptiveComplexity.PFPDefinable`,
the setting of the capture theorem FO(≤, PFP) = PSPACE) and an order-free one
(`DescriptiveComplexity.PFPDefinableFree`, the right-hand side of the
Abiteboul–Vianu theorem), and the two must not be conflated.

## Inflation is a special case

`DescriptiveComplexity.StepDef.inflate` disjoins each variable's own atom
onto its step formula, making the *partial* iteration of the modified
definition the *inflationary* iteration of the original one. Since an
inflationary iteration always converges on finite structures, FO(IFP) is
contained in FO(PFP) (`DescriptiveComplexity.IFPDefinable.pfpDefinable`,
`DescriptiveComplexity.IFPDefinableFree.pfpDefinableFree`) – the easy
inclusion of Abiteboul–Vianu, in both its ordered and order-free forms.

## Closure properties

Same story as for IFP: closed under (ordered) first-order reductions by the
transport lemmas of `DescriptiveComplexity.FixedPointStep`
(`DescriptiveComplexity.PFPDefinable.of_orderedReduction`,
`DescriptiveComplexity.PFPDefinableFree.of_foReduction`). Closure under
complement is *not* by negating the output – divergence makes both a
definition and its output-negation false – but follows on ordered structures
from the capture theorem (`DescriptiveComplexity.FixedPointPartialSpace`)
and `PSPACE = coPSPACE`.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of a partial definition -/

/-- The partial iteration converges: some stage is a fixed point of the
step. -/
def PFPConverges (d : Lax535992.InflationaryFixedPoint.StepDef L) (A : Type) [L.Structure A] : Prop :=
  ∃ n, IsFixedPt d.next (d.partStage A n)

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (PFPConverges)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

/-- A definition whose value is read converges. -/
theorem PFPHolds.converges {d : Lax535992.InflationaryFixedPoint.StepDef L} {A : Type} [L.Structure A]
    (h : d.PFPHolds A) : d.PFPConverges A :=
  ⟨h.choose, h.choose_spec.1⟩

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax134656.PartialFixedPoint.StepDef.PFPHolds

export Lax822549Proofs.DescriptiveComplexity.StepDef.PFPHolds (converges)

end Lax134656.PartialFixedPoint.StepDef.PFPHolds

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

open Classical in
/-- **The first stage that does not move**: convergence is witnessed by a
*least* index. That is what a machine testing «this stage and the next
agree» at each round stops at, and what makes its earlier rounds' tests
fail. -/
theorem exists_least_stable (d : Lax535992.InflationaryFixedPoint.StepDef L) (A : Type) [L.Structure A]
    (h : d.PFPConverges A) :
    ∃ N, d.partStage A N = d.partStage A (N + 1) ∧
      ∀ n, n < N → d.partStage A n ≠ d.partStage A (n + 1) := by
  have hex : ∃ n, d.partStage A n = d.partStage A (n + 1) := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by rw [d.partStage_succ, hn]⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (exists_least_stable)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

/-- The value of a partial definition is isomorphism-invariant. -/
theorem pfpHolds_equiv (d : Lax535992.InflationaryFixedPoint.StepDef L) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : d.PFPHolds M ↔ d.PFPHolds N := by
  refine exists_congr fun n => ?_
  rw [d.partStage_map e n]
  refine and_congr (d.isFixedPt_next_map_iff e _).symm ?_
  exact realize_sentence_of_equiv
    (d.B.extendEquiv' (L' := L) e (d.partStage M n)) d.out

end StepDef

end Lax822549Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax822549Proofs.DescriptiveComplexity.StepDef (pfpHolds_equiv)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

end StepDef

/-! ### Definability, ordered and order-free -/

/-! ### Closure under reductions -/

section Closure

end Closure

/-! ### FO(IFP) is contained in FO(PFP) -/

section Inflate

end Inflate

end Lax822549Proofs.DescriptiveComplexity


