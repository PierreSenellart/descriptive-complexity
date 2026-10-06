/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.TransitiveClosureParam
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Lax945089Proofs.DescriptiveComplexity.FixedPoint
import Lax945089Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax945089Proofs.DescriptiveComplexity.FixedPointReduction
import Lax945089Proofs.DescriptiveComplexity.FixedPointStep
import Lax945089Proofs.DescriptiveComplexity.Hierarchy
import Lax945089Proofs.DescriptiveComplexity.OrderWalk
import Lax945089Proofs.DescriptiveComplexity.Ordered
import Lax945089Proofs.DescriptiveComplexity.OrderedComposition
import Lax945089Proofs.DescriptiveComplexity.RelComposition
import Lax945089Proofs.DescriptiveComplexity.SecondOrder
import Lax945089Proofs.DescriptiveComplexity.SecondOrderLift
import Lax945089Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax945089Proofs.DescriptiveComplexity.SecondOrderPull
import Lax945089Proofs.DescriptiveComplexity.SecondOrderTransitiveClosure
import Lax945089Proofs.DescriptiveComplexity.Vocabulary
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

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax945089.TransitiveClosureReductions
end Lax945089.TransitiveClosureReductions

namespace Lax945089Proofs.DescriptiveComplexity.FOReduction
end Lax945089Proofs.DescriptiveComplexity.FOReduction

namespace Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax945089Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax945089Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax945089Proofs.DescriptiveComplexity.RelOrderedFOReduction
end Lax945089Proofs.DescriptiveComplexity.RelOrderedFOReduction

namespace Lax945089Proofs.DescriptiveComplexity.TCFamily
end Lax945089Proofs.DescriptiveComplexity.TCFamily

namespace Lax945089Proofs.DescriptiveComplexity.TCInterpretation
end Lax945089Proofs.DescriptiveComplexity.TCInterpretation

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.TransitiveClosureReductions (TCFamily TCInterpretation)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# FO(TC) reductions: the logarithmic-space reductions

The reduction notion of `DescriptiveComplexity.NL`: an interpretation whose
defining formulas may consult, besides the input structure, the **reachability
relations of first-order walks** (`DescriptiveComplexity.TCFamily`). It sits
between the two notions already built,

`≤ᶠᵒ[≤]` ⊆ `≤ᵗᶜ` ⊆ `≤ˡᶠᵖ`,

the first inclusion strict (`DescriptiveComplexity.TransitiveClosureReductionStrict`),
and it is what “logarithmic-space reduction” means in a machine-free
development, exactly as `≤ˡᶠᵖ` is what “polynomial-time reduction” means.

## What comes for free, and what does not

A walk is an inflationary induction of a very restricted shape
(`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`), so an FO(TC)
interpretation *is* an FO(LFP) interpretation
(`DescriptiveComplexity.TCInterpretation.toLFP`) and an FO(TC) reduction is an
FO(LFP) reduction (`DescriptiveComplexity.TCReduction.toLFP`). Every closure
theorem of `DescriptiveComplexity.FixedPointReductionClosure` therefore
transfers: PTIME, NP and coNP are closed under `≤ᵗᶜ`, and hardness under
first-order reductions implies hardness under these.

What does not transfer is the closure of NL itself: the membership walk
pulled back through the reduction is a walk whose steps consult walks, and the
route the other classes took is unavailable here – there the induction was
absorbed by a *smaller* class already known to sit inside (PTIME inside NP),
and NL has no smaller class to lean on. What it needs is its own normal form,
a `TC` of a formula containing `TC`s being a single `TC`, and that is proved
as an algebra of walks with two exits (`DescriptiveComplexity.Decider`,
`DescriptiveComplexity.TransitiveClosureDecide` through
`DescriptiveComplexity.TransitiveClosureSentenceDecide`): NL is closed under
`≤ᵗᶜ` (`DescriptiveComplexity.mem_NL_of_tcReduction`, in
`DescriptiveComplexity.TransitiveClosureReductionClosure`).

Transitivity of `≤ᵗᶜ` (`DescriptiveComplexity.TCReduction.trans`, in
`DescriptiveComplexity.TransitiveClosureReductionTrans`) composes two FO(TC)
interpretations by pulling the outer walks back through the inner
interpretation, flattening them with the same deciders, and extending the
inner interpretation to the outer walks' vocabulary. So `≤ᵗᶜ` is a reduction
*order*, with the closure properties of NL and of the classes above it.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Interpretations that read walks -/

namespace TCInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax945089.TransitiveClosureReductions.TCInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-! ### A walk is an induction, so an FO(TC) interpretation is an FO(LFP) one -/

end TCInterpretation

/-! ### FO(TC) reductions -/

variable {L L' : Language.{0, 0}}

/-- An **FO(TC) reduction** from `P` to `Q` – a logarithmic-space reduction, in
the logical form of [Immerman 1999][immerman1999descriptive]: an FO(TC)
interpretation over the ordered expansion of the source vocabulary, mapping
yes-instances exactly to yes-instances, for every finite linear order on the
input. -/
structure TCReduction [L.IsRelational] [L'.IsRelational] (P : Lax904597.Problems.DecisionProblem L)
    (Q : Lax904597.Problems.DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying FO(TC) interpretation, over the ordered expansion. -/
  toInterpretation : Lax945089.TransitiveClosureReductions.TCInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (toInterpretation.Map A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᵗᶜ " Q:51 => TCReduction P Q

/-! ### Every FO(TC) reduction is an FO(LFP) reduction -/

section ToLFP

end ToLFP

/-! ### Every first-order reduction is an FO(TC) reduction -/

section OfFO

end OfFO

section Embed

end Embed

/-! ### The classes above NL are closed under FO(TC) reductions -/

section Closure

end Closure

end Lax945089Proofs.DescriptiveComplexity


