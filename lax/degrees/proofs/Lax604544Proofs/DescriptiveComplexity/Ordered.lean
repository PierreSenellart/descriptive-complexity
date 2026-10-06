/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Interpretation
import Mathlib.ModelTheory.Order
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

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax604544Proofs.DescriptiveComplexity

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation OrderedFOReduction sumOrderOrderedStructure sumOrderStructure)
end Lax604544Proofs.DescriptiveComplexity

/-!
# Ordered first-order reductions

Textbook FO reductions ([Immerman 1999][immerman1999descriptive],
*Descriptive Complexity*, ch. 3) operate on *ordered* finite structures: the
input structure comes with a linear order on
its universe, which the defining formulas may mention. The order is essential
for many reductions: e.g., reducing SAT to 3-colorability threads an OR-gadget
chain along the order of each clause's literals, which no order-free
first-order interpretation can express.

This file provides the ordered variant of `DescriptiveComplexity.FOReduction`:

* an `(L.sum Language.order).Structure` instance on any linearly ordered
  `L`-structure, realizing the extra binary symbol `leSymb` as `≤`;
* `DescriptiveComplexity.OrderedFOReduction P Q`: a first-order interpretation of `L'` in
  the ordered expansion `L.sum Language.order`, mapping yes-instances of `P`
  exactly to yes-instances of `Q` – for every *finite* linearly ordered input
  structure. Finiteness matters: gadget constructions traverse the order and
  need minima, maxima and successors.

Since the problem `P` does not mention the order and correctness is required
for *every* linear order on the input structure, an `OrderedFOReduction` is
what descriptive complexity calls an order-invariant FO reduction.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

section OrderedStructures

variable (A : Type) [L.Structure A] [LE A]

variable {L A}

@[simp]
theorem relMap_sumInl {n : ℕ} (r : L.Relations n) (x : Fin n → A) :
    RelMap (L := L.sum Language.order) (Sum.inl r) x ↔ RelMap r x :=
  Iff.rfl

end OrderedStructures

variable {L} {L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ[≤] " Q:51 => Lax904597.Interpretations.OrderedFOReduction P Q

end Lax604544Proofs.DescriptiveComplexity


