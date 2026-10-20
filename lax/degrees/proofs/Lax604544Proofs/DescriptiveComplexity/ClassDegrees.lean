/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax604544Proofs.DescriptiveComplexity.Degree
import Lax604544Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax604544Proofs.DescriptiveComplexity.Problems.Taut
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Lax604544Proofs.DescriptiveComplexity.Hierarchy
import Lax604544Proofs.DescriptiveComplexity.OrderWalk
import Lax604544Proofs.DescriptiveComplexity.Padding
import Lax604544Proofs.DescriptiveComplexity.Problems.HornSat.Definability
import Lax604544Proofs.DescriptiveComplexity.Problems.HornSat.Defs
import Lax604544Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax604544Proofs.DescriptiveComplexity.Problems.HornSat.Unsat
import Lax604544Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax604544Proofs.DescriptiveComplexity.SecondOrderHornPull
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Lax604544Proofs.DescriptiveComplexity.ClauseDischarge
import Lax604544Proofs.DescriptiveComplexity.Complexity
import Lax604544Proofs.DescriptiveComplexity.InductiveCounting.Order
import Lax604544Proofs.DescriptiveComplexity.LogSpace
import Lax604544Proofs.DescriptiveComplexity.Ordered
import Lax604544Proofs.DescriptiveComplexity.OrderedComposition
import Lax604544Proofs.DescriptiveComplexity.Problems.TwoSat.Defs
import Lax604544Proofs.DescriptiveComplexity.Problems.TwoSat.Hardness
import Lax604544Proofs.DescriptiveComplexity.Problems.TwoSat.Membership
import Lax604544Proofs.DescriptiveComplexity.SecondOrderKrom
import Lax604544Proofs.DescriptiveComplexity.SecondOrderPull
import Lax604544Proofs.DescriptiveComplexity.Vocabulary
import Lax604544Proofs.DescriptiveComplexity.Problems.FinSat.Membership
import Lax604544Proofs.DescriptiveComplexity.Problems.FinSat.Reduction
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

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax604544Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT)
end Lax604544Proofs.DescriptiveComplexity

/-!
# The logically defined classes are the degrees of their complete problems

Each class of this library with a complete problem `Q₀` *is* the degree of `Q₀`
(`DescriptiveComplexity.ComplexityClass.below`, the file
`DescriptiveComplexity.Degree`): `NP = below SAT`, `coNP = below TAUT`,
`PTIME = below HORNSAT`, `NL = below TwoSAT` and `RE = below FINSAT`. This is
the sanity check that the degree construction is the right one – and a theorem
rather than a tautology, since the two sides are defined completely
differently: on the left a logic, on the right a closure under reductions.

The payoff is that “`Q₀`-hardness is `𝒞`-hardness” stops being folklore: since
the classes are *equal*, so are their hardness predicates, whichever way a
given hardness proof was obtained.

Each proof supplies `DescriptiveComplexity.ComplexityClass.eq_below_of_complete`
with the class's own hardness discharge, which delivers the *non-relativized*
reduction `≤ᶠᵒ[≤]` that the equality needs – cofinal hardness on its own yields
only `≤ʳᶠᵒ[≤]`. This is why the statement cannot be proved generically, for an
arbitrary class and an arbitrary complete problem of it.
-/

namespace Lax604544Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **NP is the degree of SAT**: a problem is in NP exactly when it reduces to
SAT (Cook–Levin, read as an equality of classes). -/
theorem NP_eq_below_sat : NP = .below Lax904597.Sat.SAT :=
  ComplexityClass.eq_below_of_complete Lax904597.Sat.SAT sat_mem_NP
    (fun Q hQ => sat_hard_of_sigmaSODefinable Q hQ) fun _ => Iff.rfl

/-- **coNP is the degree of TAUT**. -/
theorem coNP_eq_below_taut : coNP = .below TAUT :=
  ComplexityClass.eq_below_of_complete TAUT taut_mem_coNP
    (fun Q hQ => taut_hard_of_piSODefinable Q hQ) fun _ => Iff.rfl

/-- **PTIME is the degree of HORN-SAT**. -/
theorem PTIME_eq_below_hornSat : PTIME = .below HORNSAT :=
  ComplexityClass.eq_below_of_complete HORNSAT hornSat_mem_PTIME
    (fun Q hQ => hornSat_hard_of_sigmaSOHornDefinable Q hQ) fun _ => Iff.rfl

/-- **NL is the degree of 2SAT**. -/
theorem NL_eq_below_twoSat : NL = .below TwoSAT :=
  ComplexityClass.eq_below_of_complete TwoSAT twoSat_mem_NL
    (fun Q hQ => twoSat_hard_of_sigmaSOKromDefinable Q hQ) fun _ => Iff.rfl

/-- **RE is the degree of FINSAT**: Trakhtenbrot's theorem, read as an equality
of classes. -/
theorem RE_eq_below_finsat : RE = .below FINSAT :=
  ComplexityClass.eq_below_of_complete FINSAT finsat_mem_RE
    (fun Q hQ => FinSat.finsat_hard_of_sigmaSONewDefinable Q hQ) fun _ => Iff.rfl

end Lax604544Proofs.DescriptiveComplexity


