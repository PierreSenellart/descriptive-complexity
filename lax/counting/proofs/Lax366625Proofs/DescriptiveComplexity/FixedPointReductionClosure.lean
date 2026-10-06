/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax366625Proofs.DescriptiveComplexity.FixedPoint
import Lax366625Proofs.DescriptiveComplexity.FixedPointHorn
import Lax366625Proofs.DescriptiveComplexity.FixedPointInflationaryLFP
import Lax366625Proofs.DescriptiveComplexity.FixedPointOrderTransfer
import Lax366625Proofs.DescriptiveComplexity.OrderWalk
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Defs
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Unsat
import Lax366625Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax366625Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax366625Proofs.DescriptiveComplexity.FixedPointReduction
import Lax366625Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax366625Proofs.DescriptiveComplexity.FixedPointStratify
import Lax366625Proofs.DescriptiveComplexity.SecondOrderRelPull
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

namespace Lax366625Proofs.DescriptiveComplexity.CofinalHard
end Lax366625Proofs.DescriptiveComplexity.CofinalHard

namespace Lax366625Proofs.DescriptiveComplexity.IFPDefinable
end Lax366625Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax366625Proofs.DescriptiveComplexity.PiSODefinable
end Lax366625Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax366625Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax366625Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax366625Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax366625Proofs.DescriptiveComplexity.SigmaSODefinable

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SORealize SigmaSODefinable)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Classes (CofinalHard)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable)
end Lax366625Proofs.DescriptiveComplexity

/-!
# The classes are closed under FO(LFP) reductions

Membership in PTIME, in NP and in coNP travels backward along an FO(LFP)
reduction (`DescriptiveComplexity.mem_PTIME_of_lfpReduction`,
`DescriptiveComplexity.mem_NP_of_lfpReduction`,
`DescriptiveComplexity.mem_coNP_of_lfpReduction`), exactly as it does along a
first-order one. This is what makes `≤ˡᶠᵖ` a usable reduction notion for these
classes rather than a definition with no theorems: without it, “`P` reduces to a
problem of the class” would say nothing about `P`.

The three proofs are different, and the difference is the point.

* **PTIME** is closed because the logic is: the reduction's induction and the
  membership's induction *stratify* into one
  (`DescriptiveComplexity.StepDef.stratify`), after the latter is pulled back
  through the interpretation. Nothing is guessed.
* **NP** is closed because an induction can be eliminated from a `Σ₁`
  definition (`DescriptiveComplexity.sigmaSODefinable_of_ifpExpand`), the
  quantifier block that replaces it merging with the one already there.
* **coNP** is closed by complementation – a reduction complements
  (`DescriptiveComplexity.LFPReduction.compl`) – which is cheaper than
  redoing the argument with a universal block.

Above the first level nothing is claimed here. The same argument would put an
extra existential block *innermost* in a `Σₖ` prefix, which merges with the
innermost block only when that block is existential; the even levels would need
the dual elimination, through `DescriptiveComplexity.PTIME_subset_coNP`, and the
vocabulary bookkeeping of a block inserted in the middle of a prefix. PSPACE is
open here for a sharper reason: FO(PFP) has no stratification theorem, the
partial iteration not being monotone.

## Hardness

`DescriptiveComplexity.CofinalHardLFP` is hardness stated with `≤ˡᶠᵖ` in place
of `≤ʳᶠᵒ[≤]`, and `DescriptiveComplexity.CofinalHard.toLFP` says that a hard
problem in the library's sense is hard in this weaker one – the expected
implication, since a first-order reduction is an FO(LFP) reduction. Note the
direction: hardness under a *larger* class of reductions is a *weaker*
statement, so every completeness theorem of the catalog implies its
polynomial-time-reduction reading, and none of them is superseded by it.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### The definable domain is inhabited, as a sentence -/

section DomNonempty

end DomNonempty

/-! ### Polynomial time -/

section PTime

end PTime

/-! ### NP, and coNP by complementation -/

section NP

end NP

/-! ### Membership under relativized first-order reductions

The same three classes are closed under the *relativized* first-order
reductions `≤ʳᶠᵒ[≤]` – the notion all of this library's hardness travels along.
Only the hardness half of that closure was available before
(`DescriptiveComplexity.ComplexityClass.hard_of_relOrderedReduction`); the
membership half is these three theorems, and they are corollaries of the
pullback of `DescriptiveComplexity.SecondOrderRelPull` and of
`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`. (What is still
missing is the corresponding *field* of
`DescriptiveComplexity.ComplexityClass`, which every class literal of the
library would have to supply.) -/

section RelOrdered

variable [L₁.IsRelational] [L₂.IsRelational] {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}

/-- **PTIME is closed under relativized ordered reductions.**
Registered in the Lax archive as
[`Lax535992.PTIMEClosure.PTIME_mem_of_relOrderedReduction`](https://laxarchive.org/lax-535992/Lax535992.PTIMEClosure.html#s-Lax535992.PTIMEClosure.PTIME_mem_of_relOrderedReduction). -/
theorem mem_PTIME_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME P).mp
    (((ifpDefinable_iff_mem_PTIME Q).mpr h).of_relOrderedReduction f)

end RelOrdered

/-! ### Hardness under FO(LFP) reductions -/

section Hardness

end Hardness

end Lax366625Proofs.DescriptiveComplexity


