/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso.ToDigraphIso
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso.FromDigraphIso
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

/-!
# DAG Isomorphism is GI-complete

Putting the two halves together: DAG ISOMORPHISM
(`DescriptiveComplexity.DagIso`) is complete for the degree of Graph
Isomorphism (`DescriptiveComplexity.GI`), the first entry of that degree
besides Digraph Isomorphism itself.

* **Membership** (`DescriptiveComplexity.dagIso_mem_GI`,
  `DescriptiveComplexity.Problems.DagIso.ToDigraphIso`): forget the topological
  orders, after checking first-order that they are ones – the check the
  instances carry their acyclicity witness for.
* **Hardness** (`DescriptiveComplexity.dagIso_GI_hard`,
  `DescriptiveComplexity.Problems.DagIso.FromDigraphIso`): subdivide every arc
  twice, so that the direction of an arc survives as the difference between
  the two subdivision levels.

Both reductions are order-free, as reductions between isomorphism problems have
to be: an interpretation commutes with isomorphisms, which is what makes the
forward half of each correctness proof available at all, and an order-invariant
reduction would only fix the *answer*, not the constructed structure up to
isomorphism.

Membership in NP comes from the same reduction as membership in the degree
(`DescriptiveComplexity.dagIso_mem_NP`); no hardness for a *class* is claimed,
and none is expected – that is what makes the degree worth having.
-/

namespace Lax604544Proofs.DescriptiveComplexity

/-- DAG Isomorphism is in NP: it reduces to Digraph Isomorphism, which is. -/
theorem dagIso_mem_NP : DagIso ∈ NP :=
  NP.mem_of_foReduction dagIso_fo_reduction_digraphIso digraphIso_mem_NP

end Lax604544Proofs.DescriptiveComplexity


