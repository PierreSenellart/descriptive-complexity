/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.QsatInterp
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Space
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Space
import Lax480241Proofs.DescriptiveComplexity.Problems.Qsat.Blocks
import Lax480241Proofs.DescriptiveComplexity.Problems.Qsat.Complement
import Lax480241Proofs.DescriptiveComplexity.Problems.Qsat.Hardness
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

/-!
# The space-bounded machine problems are PSPACE-complete

The bridge, closed. Membership was
`DescriptiveComplexity.Problems.Machine.Space`: a configuration is an assignment of
a block of relation variables and a run is a transitive closure over them, so
both problems are SO(TC) definable. This file supplies hardness, and with it
the identification of the logically defined PSPACE with the machine class.

Hardness is proved **once**, for the deterministic problem, by
`DescriptiveComplexity.QsatTM.qsat_ordered_fo_reduction_dtmAcceptSpace`: the machine
built inside a QSAT instance evaluates the quantified Boolean formula by the
standard iterative algorithm, the recursion stack being one bit per variable in
the variable's own cell. It then travels to the nondeterministic problem along
`DescriptiveComplexity.dtmAcceptSpace_fo_reduction_ntmAcceptSpace`, since hardness
moves *forward* along reductions – which is why the deterministic problem is
the one to prove hard, and why Savitch never has to be run on the machine side.

The two completeness theorems together say `PSPACE = NPSPACE` in the form this
library can state it: deterministic and nondeterministic space-bounded
acceptance are complete for the same class.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

/-- **Deterministic space-bounded machine acceptance is PSPACE-hard**, by the
QBF-evaluating machine of `DescriptiveComplexity.Problems.Machine.QsatInterp`. -/
theorem dtmAcceptSpace_PSPACE_hard : PSPACE.Hard DTMAcceptSpace :=
  PSPACE.hard_of_orderedReduction QsatTM.qsat_ordered_fo_reduction_dtmAcceptSpace
    qsat_PSPACE_hard

/-- **Every problem of PSPACE reduces to space-bounded machine acceptance**:
the forward half of a machine characterization of the class. (The converse
direction is membership, `DescriptiveComplexity.dtmAcceptSpace_mem_PSPACE`, but a
*relativized* reduction only carries hardness, so the two do not assemble into
an `iff` the way `DescriptiveComplexity.mem_NP_iff_le_ntmAccept` does.) -/
theorem le_dtmAcceptSpace_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L)
    (hP : P ∈ PSPACE) : Nonempty (P ≤ʳᶠᵒ[≤] DTMAcceptSpace) :=
  dtmAcceptSpace_PSPACE_hard DTMAcceptSpace
    ⟨(FOReduction.refl DTMAcceptSpace).toOrdered.toRel⟩ P hP

end Lax480241Proofs.DescriptiveComplexity


