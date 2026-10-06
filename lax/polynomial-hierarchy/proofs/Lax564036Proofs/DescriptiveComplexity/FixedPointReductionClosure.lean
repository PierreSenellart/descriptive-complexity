/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.FixedPointHorn
import Lax564036Proofs.DescriptiveComplexity.FixedPointStep
import Lax564036Proofs.DescriptiveComplexity.Problems.HornSat
import Lax564036Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax564036Proofs.DescriptiveComplexity.FixedPointReduction
import Lax564036Proofs.DescriptiveComplexity.FixedPointStepRel
import Lax564036Proofs.DescriptiveComplexity.SecondOrderRelPull
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

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax564036Proofs.DescriptiveComplexity.CofinalHard
end Lax564036Proofs.DescriptiveComplexity.CofinalHard

namespace Lax564036Proofs.DescriptiveComplexity.IFPDefinable
end Lax564036Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax564036Proofs.DescriptiveComplexity.PiSODefinable
end Lax564036Proofs.DescriptiveComplexity.PiSODefinable

namespace Lax564036Proofs.DescriptiveComplexity.RelFOInterpretation
end Lax564036Proofs.DescriptiveComplexity.RelFOInterpretation

namespace Lax564036Proofs.DescriptiveComplexity.SigmaSODefinable
end Lax564036Proofs.DescriptiveComplexity.SigmaSODefinable

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

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Relativized (RelFOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SORealize SigmaSODefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Classes (CofinalHard)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable)
end Lax564036Proofs.DescriptiveComplexity

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

namespace Lax564036Proofs.DescriptiveComplexity

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

/-- **coNP is closed under relativized ordered reductions.** -/
theorem mem_coNP_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : Q ∈ coNP) : P ∈ coNP :=
  PiSODefinable.of_relOrderedReduction f h

end RelOrdered

/-! ### Hardness under FO(LFP) reductions -/

section Hardness

end Hardness

end Lax564036Proofs.DescriptiveComplexity


