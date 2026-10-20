/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Game
import Lax480241Proofs.DescriptiveComplexity.Exponential.TagBits
import Lax480241Proofs.DescriptiveComplexity.Exponential.Translate
import Lax480241Proofs.DescriptiveComplexity.PSpaceHierarchy
import Lax480241Proofs.DescriptiveComplexity.SecondOrderMerge
import Lax480241Proofs.DescriptiveComplexity.Exponential.Peel
import Lax480241Proofs.DescriptiveComplexity.Problems.Game.Hardness
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

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.HornFragment (SigmaSOHornDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The nodes of an interpreted AND/OR graph, as states of a game

The road from `DescriptiveComplexity.EXPTIME` to `SO-GAME` reads a `PTIME` inner
problem as the **AND/OR graph an interpretation draws on the expanded
universe**, and plays that graph. A node of the graph is a
tagged tuple of points, so a node is a *state* of a second-order game – that
correspondence is what this file builds.

Two things are settled here.

**The interpretation may be taken non-relativized.** `GAME` is PTIME-hard under
ordinary ordered reductions (`DescriptiveComplexity.game_hard_ordered`): the
composite of the Horn discharge with the unit-propagation game is a plain
`≤ᶠᵒ[≤]`, and `DescriptiveComplexity.game_PTIME_hard` only widens it to `≤ʳᶠᵒ[≤]`
at the very end. That matters here: a *definable domain* would have to be
checked by a formula over the expansion, i.e., by a whole sub-game, whereas a
non-relativized interpretation leaves the nodes guarded by nothing but “each
slot is a point”.

**A node is a guarded assignment.** The state block is
`DescriptiveComplexity.ExpExpansion.nodeBlock`: the `d` rounds of
`DescriptiveComplexity.repMerged`, each holding one point of the expanded
universe (`DescriptiveComplexity.ExpExpansion.pointBlock`), extended by tag bits
for the interpretation's tag. `DescriptiveComplexity.ExpExpansion.nodeGuardF`
says exactly that a guessed state is such a tuple
(`DescriptiveComplexity.ExpExpansion.realize_nodeGuardF`), so quantifying over
nodes of the graph is quantifying over guarded states
(`DescriptiveComplexity.ExpExpansion.exists_node_iff`).
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### GAME is PTIME-hard under ordinary ordered reductions -/

/-- **`GAME` is PTIME-hard without a definable domain**: the reduction of
`DescriptiveComplexity.game_PTIME_hard` is an ordinary ordered one, and only
becomes relativized when `DescriptiveComplexity.ComplexityClass.Hard` asks for
it. Playing the graph an interpretation draws needs this form, since a definable
domain would itself have to be decided by a sub-game. -/
theorem game_hard_ordered {L : Language.{0, 0}} [L.IsRelational] (Q : Lax904597.Problems.DecisionProblem L)
    (hQ : Lax535992.HornFragment.SigmaSOHornDefinable Q) : Nonempty (Q ≤ᶠᵒ[≤] GAME) := by
  obtain ⟨f⟩ := hornSat_hard_of_sigmaSOHornDefinable Qᶜ hQ.compl
  exact ⟨(f.compl.congrSource fun A _ _ => not_not).trans
    hornSatCompl_ordered_fo_reduction_game⟩

/-! ### Splitting a merged round assignment -/

/-- **Every assignment of the merged rounds is one assignment per round.** -/
theorem repBlockAssign_split (B : Lax904597.SecondOrder.SOBlock) (A : Type) :
    ∀ (k : ℕ) (ν : (repMerged B k).Assignment A),
      ∃ ρs : Fin k → B.Assignment A, ν = repBlockAssign B A k ρs := by
  intro k
  induction k with
  | zero =>
    intro ν
    refine ⟨fun i => i.elim0, ?_⟩
    funext i
    exact i.elim
  | succ k ih =>
    intro ν
    obtain ⟨ρs, hρs⟩ := ih fun i => ν (Sum.inr i)
    refine ⟨Fin.cons (fun i => ν (Sum.inl i)) ρs, ?_⟩
    have hs : (fun i : Fin k =>
        (Fin.cons (fun i => ν (Sum.inl i)) ρs : Fin (k + 1) → B.Assignment A) i.succ) = ρs :=
      funext fun i => Fin.cons_succ _ _ i
    have hcons : repBlockAssign B A (k + 1) (Fin.cons (fun i => ν (Sum.inl i)) ρs) =
        consAssign (fun i => ν (Sum.inl i)) (repBlockAssign B A k ρs) := by
      rw [repBlockAssign, hs]
      rfl
    rw [hcons, ← hρs]
    exact (consAssign_split ν).symm

namespace ExpExpansion

/-! ### The block a node is guessed in -/

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


