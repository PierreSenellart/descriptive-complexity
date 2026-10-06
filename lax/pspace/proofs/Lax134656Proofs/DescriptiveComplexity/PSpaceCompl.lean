/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax134656Proofs.DescriptiveComplexity.Problems.Qsat.Blocks
import Lax134656Proofs.DescriptiveComplexity.Problems.Qsat.Complement
import Lax134656Proofs.DescriptiveComplexity.Problems.Qsat.Hardness
import Lax134656Proofs.DescriptiveComplexity.Problems.SuccinctReach
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

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656Proofs.DescriptiveComplexity.SOTCDefinable
end Lax134656Proofs.DescriptiveComplexity.SOTCDefinable

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax134656Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable)
end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax134656Proofs.DescriptiveComplexity

/-!
# `PSPACE = coPSPACE`

**The theorem**: polynomial space is closed under complement. In this library
PSPACE is *defined* by SO(TC) (`DescriptiveComplexity.PSPACE`), and the complement
of a walk is not a walk, so this is not the definitional duality that gives
`PiP k` from `SigmaP k`. It is assembled from three pieces:

* every SO(TC) definable problem reduces to SUCCINCT-REACH
  (`DescriptiveComplexity.succinctReach_hard_of_sotcDefinable`, the Tseitin
  discharge) and from there to QSAT
  (`DescriptiveComplexity.succinctReach_ordered_fo_reduction_qsat`, Savitch's
  recursive doubling);
* complementing an ordered reduction is free – the same interpretation
  (`DescriptiveComplexity.OrderedFOReduction.compl`);
* the complement of QSAT is SO(TC) definable
  (`DescriptiveComplexity.qsatCompl_sotcDefinable`), because the walk that decides
  QSAT is *deterministic* and computes the value of the formula, so reading its
  answer the other way round decides the complement.

That third piece is where the content sits, and it is the logical shadow of the
machine-theoretic reason PSPACE is closed under complement: a space-bounded
computation can be made deterministic (Savitch), and a deterministic decider is
complemented by flipping its answer. Savitch's recursive doubling is what
`DescriptiveComplexity.Problems.Qsat.Hardness` spends to turn the *nondeterministic*
walk of an arbitrary SO(TC) specification into the deterministic evaluation of a
quantified Boolean formula.
-/

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder Language

variable {L : Language.{0, 0}}

/-! ### SO(TC) is closed under complement -/

/-- **SO(TC) is closed under complement**: the complement of an SO(TC) definable
problem is SO(TC) definable.

Reduce to QSAT – through SUCCINCT-REACH and Savitch's recursive doubling – and
read the deterministic evaluation walk of QSAT backwards. -/
theorem SOTCDefinable.compl [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L} (h : Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Pᶜ := by
  obtain ⟨f⟩ := succinctReach_hard_of_sotcDefinable P h
  exact qsatCompl_sotcDefinable.of_orderedReduction
    (f.trans succinctReach_ordered_fo_reduction_qsat).compl

end Lax134656Proofs.DescriptiveComplexity

namespace Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

export Lax134656Proofs.DescriptiveComplexity.SOTCDefinable (compl)

end Lax134656.SecondOrderTransitiveClosure.SOTCDefinable

namespace Lax134656Proofs.DescriptiveComplexity

open FirstOrder Language

variable {L : Language.{0, 0}}

/-- Complementation is a bijection of the SO(TC) definable problems. -/
theorem sotcDefinable_compl_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) :
    Lax134656.SecondOrderTransitiveClosure.SOTCDefinable Pᶜ ↔ Lax134656.SecondOrderTransitiveClosure.SOTCDefinable P := by
  refine ⟨fun h => ?_, SOTCDefinable.compl⟩
  have h2 := h.compl
  rwa [DecisionProblem.compl_compl] at h2

/-! ### `PSPACE = coPSPACE` -/

/-- Membership in PSPACE is closed under complement. -/
theorem mem_PSPACE_compl_iff [L.IsRelational] (P : Lax904597.Problems.DecisionProblem L) : Pᶜ ∈ PSPACE ↔ P ∈ PSPACE :=
  sotcDefinable_compl_iff P

end Lax134656Proofs.DescriptiveComplexity


