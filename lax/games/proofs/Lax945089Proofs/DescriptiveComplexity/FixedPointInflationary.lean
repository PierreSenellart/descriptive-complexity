/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.FixedPointStep
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089Proofs.DescriptiveComplexity.IFPDefinable
end Lax945089Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax945089Proofs.DescriptiveComplexity.IFPDefinableFree
end Lax945089Proofs.DescriptiveComplexity.IFPDefinableFree

namespace Lax945089Proofs.DescriptiveComplexity.LFPDef
end Lax945089Proofs.DescriptiveComplexity.LFPDef

namespace Lax945089Proofs.DescriptiveComplexity.LFPDefinable
end Lax945089Proofs.DescriptiveComplexity.LFPDefinable

namespace Lax945089Proofs.DescriptiveComplexity.StepDef
end Lax945089Proofs.DescriptiveComplexity.StepDef

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax134656.PartialFixedPoint (IFPDefinableFree)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# FO(IFP): first-order logic with an inflationary fixed point

The inflationary fixed-point logic ([Gurevich–Shelah
1986][gurevich1986fixed]; [Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` *inflationarily* – each stage
accumulates what the step formulas derive on top of the previous stage – and
read the output sentence at the limit. No positivity is required of the step
formulas: inflation makes the iteration monotone whatever they are, which is
the whole point of the logic.

Two definability notions result, and keeping them distinct is the entire
subject of the Abiteboul–Vianu theorem:

* `DescriptiveComplexity.IFPDefinableFree` – over the bare vocabulary, on
  unordered structures;
* `DescriptiveComplexity.IFPDefinable` – over the vocabulary expanded by an
  order, required for every linear order on the universe, the problem itself
  never seeing it. This is the setting of the capture theorem
  FO(≤, IFP) = PTIME (`DescriptiveComplexity.FixedPointInflationaryLFP`).

For SO(TC) the corresponding two notions coincide
(`DescriptiveComplexity.sotcDefinable_iff_free`): a walk can guess an order
into its state. Here they must *not* be conflated – an inflationary induction
cannot manufacture an order (its stages are isomorphism-invariant, so on a
bare set of `n` elements nothing asymmetric is ever derived), and the gap
between the two notions is precisely what makes the unordered
Abiteboul–Vianu theorem (`DescriptiveComplexity.AbiteboulVianu`) a theorem
about `P = PSPACE` rather than a triviality.

## Relation to FO(LFP), and why Gurevich–Shelah is not needed

`DescriptiveComplexity.LFPDefinable.ifpDefinable` embeds FO(LFP) into ordered
FO(IFP): the rules of a Horn program, read as one simultaneous step
(`DescriptiveComplexity.hornStepF`), form a `StepDef` whose inflationary
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`
(`DescriptiveComplexity.inflStage_toStepDef`). The converse translation –
FO(≤, IFP) back into FO(LFP), hence the capture of PTIME – is
`DescriptiveComplexity.FixedPointInflationaryLFP`.

This library states the Abiteboul–Vianu theorem for IFP versus PFP, as in
Abiteboul and Vianu's original form. The classical statement for *least*
fixed points on unordered structures needs Gurevich–Shelah (order-free
LFP = IFP, by stage comparison) on top; phrasing the theorem with IFP makes
that machinery unnecessary, a design decision, not an omission.

## Closure properties

FO(IFP) definability is closed under complement by construction
(`DescriptiveComplexity.IFPDefinable.compl` – negate the output), and under
(ordered) first-order reductions
(`DescriptiveComplexity.IFPDefinableFree.of_foReduction`,
`DescriptiveComplexity.IFPDefinable.of_orderedReduction`): the stages commute
with the pullback of the block (`DescriptiveComplexity.StepDef.inflStage_pull`)
and the output sentence pulls back through the extended interpretation,
exactly as for FO(LFP). The notion is class-worthy in the sense of
`DescriptiveComplexity.ComplexityClass`.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of an inflationary definition -/

end StepDef

/-! ### Definability, ordered and order-free -/

/-- Order-free FO(IFP) definability only depends on the finite instances of a
problem. -/
theorem ifpDefinableFree_congr [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    Lax134656.PartialFixedPoint.IFPDefinableFree P ↔ Lax134656.PartialFixedPoint.IFPDefinableFree Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-! ### Closure under reductions -/

section Closure

end Closure

/-! ### Horn rules as one simultaneous inflationary step

The rules of an FO(LFP) definition, read as a single simultaneous step: the
step formula of the variable `i` says that some rule with head `i` fires –
its guard holds and its body atoms are in the current stage – with the head's
arguments instantiated at the free variables. Iterated inflationarily, the
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`,
so the limit is the least fixed point and FO(LFP) embeds into FO(≤, IFP)
(`DescriptiveComplexity.LFPDefinable.ifpDefinable`). The step formulas
produced here are *positive* in the block – inflation just does not care. -/

section Horn

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The relation symbol of a block variable, in the expanded vocabulary
`L.sum B.lang` (the generic-`L` sibling of
`DescriptiveComplexity.varOutSym`). -/
abbrev varInSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) :
    (L.sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

section Realize

end Realize

end Horn

/-! ### FO(LFP) embeds into FO(≤, IFP) -/

section OfLFP

end OfLFP

end Lax945089Proofs.DescriptiveComplexity


