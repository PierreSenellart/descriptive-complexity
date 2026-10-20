/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.SecondOrderNewOrdered
import Lax604544Proofs.DescriptiveComplexity.Hierarchy
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
import Lax604544.DagIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.RelationIsomorphism
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
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

namespace Lax624099.ValueInvention
end Lax624099.ValueInvention

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax624099.ValueInvention (SigmaSONewDefinable)
end Lax604544Proofs.DescriptiveComplexity

/-!
# The class RE, defined by value invention

**RE** (`DescriptiveComplexity.RE`), the recursively enumerable problems,
*defined* – like every class in this library – by a logic: definability in
`∃SO[new]`, existential second-order logic over a universe extended by finitely
many invented values (`DescriptiveComplexity.SigmaSONewDefinable`, in
`DescriptiveComplexity.SecondOrderNew`).

It is a bona fide `DescriptiveComplexity.ComplexityClass` because `∃SO[new]`
definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SigmaSONewDefinable.of_foReduction` in
`DescriptiveComplexity.SecondOrderNewPull`, and
`DescriptiveComplexity.SigmaSONewDefinable.of_orderedReduction` in
`DescriptiveComplexity.SecondOrderNewOrdered`): the target's extended universe
is definable inside the source's, with the same invented values, so the kernel
pulls back through a relativized interpretation, and the order of an ordered
reduction is re-quantified inside the block under a guard relativized to the
original elements.

`DescriptiveComplexity.NP_subset_RE` is the inclusion `NP ⊆ RE`, by inventing
nothing.

## What this file claims, and where the rest is

RE is here a *logically defined* class, exactly as NP is `Σ₁`-definability
rather than a machine notion: a completeness proof for it is an `∃SO[new]`
definition plus a first-order reduction. Two facts about it are proved
elsewhere, where the class meets Mathlib's computability layer, and nothing in
this file assumes them:

* `DescriptiveComplexity.mem_RE_iff_rePred` – RE *is* recursive enumerability:
  a problem is `∃SO[new]`-definable exactly when its concrete instances form an
  `REPred`;
* `DescriptiveComplexity.RE_ne_coRE` – RE differs from its complement
  `DescriptiveComplexity.coRE`. That separation is not available here:
  `coNP = Π₁ᵖ` has a *logical* dual definition, while `∃SO[new]` has no dual
  reading, so nothing in this file relates the two classes. It is the
  undecidability of an RE-complete problem, through Post's theorem, that
  separates them.

Both are in `DescriptiveComplexity.Computability.CodeHaltComplete`.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **The class RE**: the problems definable in `∃SO[new]`, existential
second-order logic with value invention. Unbounding the number of invented
values is the only change from the `Σ₁` definition of NP, and it is what takes
the class from “search a space exponential in the instance” to “search an
unbounded space of finite witnesses”.

It is a `DescriptiveComplexity.ComplexityClass` by the two closure theorems of
`DescriptiveComplexity.SecondOrderNewPull` and
`DescriptiveComplexity.SecondOrderNewOrdered`; hardness is *cofinal*, as
everywhere in this development (see `DescriptiveComplexity.hard_RE_iff`). -/
noncomputable def RE : ComplexityClass :=
  .ofMem (fun P => Lax624099.ValueInvention.SigmaSONewDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSONewDefinable_congr h)

variable {L : Language.{0, 0}}

@[simp]
theorem mem_RE_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : P ∈ RE ↔ Lax624099.ValueInvention.SigmaSONewDefinable P :=
  Iff.rfl

end Lax604544Proofs.DescriptiveComplexity


