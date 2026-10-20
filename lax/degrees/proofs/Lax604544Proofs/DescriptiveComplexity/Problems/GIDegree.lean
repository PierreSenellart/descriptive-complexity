/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Problems.GraphIso.Hardness
import Lax604544Proofs.DescriptiveComplexity.Problems.DagIso
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
# The GI degree, collected

The degree is defined on `DescriptiveComplexity.GraphIso`, the undirected
problem the literature names GI. Its members therefore reach it through the
digraph-to-graph gadget of
`DescriptiveComplexity.Problems.GraphIso.Hardness`, which is why the
completeness theorems of the problems stated over the *directed* vocabulary are
collected here rather than beside their reductions.

Complete for the degree: Graph Isomorphism itself
(`DescriptiveComplexity.graphIso_GI_complete`), Digraph Isomorphism
(`DescriptiveComplexity.digraphIso_GI_complete`) and DAG Isomorphism
(`DescriptiveComplexity.dagIso_GI_complete`).
-/

namespace Lax604544Proofs.DescriptiveComplexity

/-- DAG Isomorphism belongs to the GI degree: forget the topological orders,
then turn the digraph into a simple graph. -/
theorem dagIso_mem_GI : DagIso ∈ GI :=
  ⟨(dagIso_fo_reduction_digraphIso.trans digraphIso_fo_reduction_graphIso).toOrdered⟩

/-- DAG Isomorphism is hard for the GI degree: Digraph Isomorphism, which is,
reduces to it. -/
theorem dagIso_GI_hard : GI.Hard DagIso :=
  GI.hard_of_foReduction digraphIso_fo_reduction_dagIso digraphIso_GI_complete.hard

/-- **DAG Isomorphism is GI-complete**: it reduces to Digraph Isomorphism by
forgetting the carried topological orders, and Digraph Isomorphism reduces to it
by subdividing every arc twice. -/
theorem dagIso_GI_complete : GI.Complete DagIso :=
  ⟨dagIso_mem_GI, dagIso_GI_hard⟩

end Lax604544Proofs.DescriptiveComplexity


