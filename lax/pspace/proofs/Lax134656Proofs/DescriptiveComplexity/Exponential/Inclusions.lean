/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.FixedPointHorn
import Lax134656Proofs.DescriptiveComplexity.FixedPointPartialMachine
import Lax134656Proofs.DescriptiveComplexity.Hierarchy
import Lax134656Proofs.DescriptiveComplexity.OrderedComposition
import Lax134656Proofs.DescriptiveComplexity.SecondOrderBlockHom
import Lax134656Proofs.DescriptiveComplexity.SecondOrderTransitiveClosurePull
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Lax134656Proofs.DescriptiveComplexity.ClauseDischarge
import Lax134656Proofs.DescriptiveComplexity.Complexity
import Lax134656Proofs.DescriptiveComplexity.FixedPoint
import Lax134656Proofs.DescriptiveComplexity.InductiveCounting.Order
import Lax134656Proofs.DescriptiveComplexity.Ordered
import Lax134656Proofs.DescriptiveComplexity.PSpace
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax134656Proofs.DescriptiveComplexity.SecondOrder
import Lax134656Proofs.DescriptiveComplexity.SecondOrderPull
import Lax134656Proofs.DescriptiveComplexity.Vocabulary
import Lax134656Proofs.DescriptiveComplexity.PSpaceCompl
import Lax134656Proofs.DescriptiveComplexity.PSpaceHierarchy
import Mathlib.Data.Set.Finite.Lemmas
import Lax134656Proofs.DescriptiveComplexity.Problems.HornSat
import Lax134656Proofs.DescriptiveComplexity.Problems.Sat
import Lax134656Proofs.DescriptiveComplexity.SecondOrderHorn
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

/-!
# The exponential classes: complements and inclusions

Everything in this file is *inherited* rather than proved. The two facts it
rests on are polynomial-level and each cost a large development:

* `DescriptiveComplexity.piP_zero_eq` – polynomial time is closed under
  complement, Grädel's capture theorem at level 0, through FO(LFP);
* `DescriptiveComplexity.PSPACE_eq_coPSPACE` – polynomial space is closed under
  complement, Savitch, through the deterministic QSAT walk.

`DescriptiveComplexity.ComplexityClass.exp_compl` carries both one exponential
up, and `DescriptiveComplexity.ComplexityClass.exp_mono` carries every
polynomial-level inclusion. Nothing of the two developments above is spent
twice; that is the first payoff of making `exp` an operator on an abstract
class.

Read on the definitions, the complement equalities say that **SO(LFP) and
SO(PFP) are closed under complement**, which is the form a reader of the logic
will look for; they are stated that way too.

The one construction with content is
`DescriptiveComplexity.PSPACE_subset_PTIME_exp` – an SO(TC) walk is REACH on
the expansion whose points are its states – which lives in
`DescriptiveComplexity.Exponential.Reach` and starts the whole tower.

**No claim is made for NEXPTIME**, which is not expected to be closed under
complement.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The two polynomial-level complement facts, in the form used here -/

/-! ### The complement equalities -/

/-! ### The inclusions

Every line but the first is `DescriptiveComplexity.ComplexityClass.exp_mono` on
a polynomial-level inclusion, read through the bridge theorems of
`DescriptiveComplexity.Exponential.Classes`. -/

/-- `PTIME ⊆ PSPACE`, routed through NP – the polynomial-level inclusion the
exponential ones are lifted from. -/
theorem PTIME_subset_PSPACE : PTIME ⊆ PSPACE :=
  fun _ _ _ h => NP_subset_PSPACE (PTIME_subset_NP h)

/-! ### The polynomial classes inside the exponential ones

All of these route through `PSPACE ⊆ EXPTIME`, which is the only inclusion of
this development with content. -/

end Lax134656Proofs.DescriptiveComplexity


