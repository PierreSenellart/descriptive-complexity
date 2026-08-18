/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.QsatInterp
import DescriptiveComplexity.Problems.Machine.SpaceDet
import DescriptiveComplexity.Problems.Machine.Space
import DescriptiveComplexity.Problems.Qsat

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

namespace DescriptiveComplexity

open FirstOrder

/-- **Deterministic space-bounded machine acceptance is PSPACE-hard**, by the
QBF-evaluating machine of `DescriptiveComplexity.Problems.Machine.QsatInterp`. -/
theorem dtmAcceptSpace_PSPACE_hard : PSPACE.Hard DTMAcceptSpace :=
  PSPACE.hard_of_orderedReduction QsatTM.qsat_ordered_fo_reduction_dtmAcceptSpace
    qsat_PSPACE_hard

/-- **Nondeterministic space-bounded machine acceptance is PSPACE-hard**, by
transfer: determinism is a first-order promise a reduction can enforce. -/
theorem ntmAcceptSpace_PSPACE_hard : PSPACE.Hard NTMAcceptSpace :=
  PSPACE.hard_of_foReduction dtmAcceptSpace_fo_reduction_ntmAcceptSpace
    dtmAcceptSpace_PSPACE_hard

/-- **Deterministic space-bounded machine acceptance is PSPACE-complete.** The
classes of this library are definitions in logic; this theorem is the bridge
saying its PSPACE is the machine one. -/
theorem dtmAcceptSpace_PSPACE_complete : PSPACE.Complete DTMAcceptSpace :=
  ⟨dtmAcceptSpace_mem_PSPACE, dtmAcceptSpace_PSPACE_hard⟩

/-- **Nondeterministic space-bounded machine acceptance is PSPACE-complete.** -/
theorem ntmAcceptSpace_PSPACE_complete : PSPACE.Complete NTMAcceptSpace :=
  ⟨ntmAcceptSpace_mem_PSPACE, ntmAcceptSpace_PSPACE_hard⟩

/-- **Every problem of PSPACE reduces to space-bounded machine acceptance**:
the forward half of a machine characterization of the class. (The converse
direction is membership, `DescriptiveComplexity.dtmAcceptSpace_mem_PSPACE`, but a
*relativized* reduction only carries hardness, so the two do not assemble into
an `iff` the way `DescriptiveComplexity.mem_NP_iff_le_ntmAccept` does.) -/
theorem le_dtmAcceptSpace_of_mem_PSPACE {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L)
    (hP : P ∈ PSPACE) : Nonempty (P ≤ʳᶠᵒ[≤] DTMAcceptSpace) :=
  dtmAcceptSpace_PSPACE_hard DTMAcceptSpace
    ⟨(FOReduction.refl DTMAcceptSpace).toOrdered.toRel⟩ P hP

end DescriptiveComplexity
