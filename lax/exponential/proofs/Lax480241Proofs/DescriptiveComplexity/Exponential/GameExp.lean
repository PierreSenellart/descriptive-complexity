/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameNodes
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

namespace Lax480241.SecondOrderFixedPoints
end Lax480241.SecondOrderFixedPoints

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity.SOLFPDefinable
end Lax480241Proofs.DescriptiveComplexity.SOLFPDefinable

namespace Lax535992.Game
end Lax535992.Game

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.SecondOrderFixedPoints (SOLFPDefinable)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.Game (AGStart GameWon)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax535992.Game (andOrGraph)
end FirstOrder.Language

/-!
# EXPTIME is second-order alternating reachability

**The theorem**: `DescriptiveComplexity.exptime_eq_soGame` –

> `P ∈ EXPTIME ↔ SOGameDefinable P`,

the deterministic exponential class *is* the value of a second-order alternating
game. One direction is `DescriptiveComplexity.SOGameDefinable.mem_EXPTIME`, the
second-order shadow of `GAME ∈ PTIME`; the other is
`DescriptiveComplexity.SOLFPDefinable.soGameDefinable`, assembled here, and it is
Chandra–Kozen–Stockmeyer's half of `APSPACE = EXPTIME`
([Chandra–Kozen–Stockmeyer 1981][chandra1981alternation]) with the machine
removed.

## How the pieces meet

`SOLFPDefinable P` is `ExpDefinable PTIME P`
(`DescriptiveComplexity.solfpDefinable_iff_expDefinable`), so `P A` is a `PTIME`
property of an exponential expansion `X.Map A`; `DescriptiveComplexity.GAME` is
PTIME-hard under ordinary ordered reductions
(`DescriptiveComplexity.game_hard_ordered`), so that property is `GameWon` of the
AND/OR graph an interpretation `I` draws **on the expanded universe**. Its four
defining relations are first-order over the expansion, hence *alternating block
prefixes* over the base (`DescriptiveComplexity.ExpExpansion.exists_translate`), and a prefix
is a sequence of moves. `DescriptiveComplexity.ExpExpansion.graphGame` plays that graph:

* `DescriptiveComplexity.ExpExpansion.wins_pre` – the prefix phases evaluate the
  six questions;
* `DescriptiveComplexity.ExpExpansion.target_of_wins` and
  `DescriptiveComplexity.ExpExpansion.wins_of_winsOn` – the node phases play the
  graph;
* `DescriptiveComplexity.ExpExpansion.graphGame_accepts_iff` – putting them
  together at the starting phase.

The one thing that never happens is a *sentence over the base* that quantifies a
point: a quantifier over the expanded universe is a second-order block over the
base, never a first-order one. That is the obstruction the whole design works
around, and it works around it by the observation that it does not apply to a
**move**.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {T : Type} [Finite T] {d n Dm : ℕ}

variable {A : Type} [instL : L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable (I : Lax904597.Interpretations.FOInterpretation (X.E.sum Language.order) Lax535992.Game.andOrGraph T d)

variable (hdn : 2 * d ≤ n)

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

variable (hK : ∀ s tx ty, KernelSpec I hdn (n - D s tx ty) (D s tx ty) s tx ty (K s tx ty))

include hK in
/-- **The graph game accepts exactly when the interpreted graph is won.** -/
theorem graphGame_accepts_iff :
    letI := X.mapLinearOrder A
    letI := I.mapStructure (X.Map A)
    ((graphGame X hn D hD K).Accepts A ↔ Lax535992.Game.GameWon (I.Map (X.Map A))) := by
  let := X.mapLinearOrder A
  let := I.mapStructure (X.Map A)
  have := X.mapNonempty A
  constructor
  · rintro ⟨τ, hstart, hwins⟩
    obtain ⟨tx, pts, rfl⟩ := (graphGame_isStart τ).mp hstart
    obtain ⟨h1, h2⟩ := target_of_wins I hdn hK _ hwins (.startPick tx) pts rfl
    exact ⟨nodeAt I hdn tx 0 pts, h1, h2⟩
  · rintro ⟨y, hstart, hwin⟩
    obtain ⟨pts, -, hy⟩ := exists_pts_of_node I hdn y fun _ => Classical.arbitrary (X.Map A)
    have hy' : nodeAt I hdn y.1 0 (fun i => pts (shiftIx d n hdn i)) = y :=
      (nodeAt_shift I hdn y.1 pts).trans hy
    refine ⟨nodeState (.startPick y.1) fun i => pts (shiftIx d n hdn i),
      (graphGame_isStart _).mpr ⟨y.1, _, rfl⟩, ?_⟩
    refine .all ((graphGame_isUniv (Ph.startPick y.1) _).mpr trivial)
      ⟨_, move_keepAll (Ph.startPick y.1) (preEntry D hD .st y.1 y.1)
        (by rw [movesFrom_startPick]; simp) rfl rfl _⟩ ?_
    intro τ hmv
    obtain ⟨q, σs, rfl⟩ := graphGame_move_shape hmv
    obtain ⟨m, hmem, htgt, hkeep, hguard⟩ := (graphGame_move _ _ _ _).mp hmv
    rw [movesFrom_startPick] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · have htgt' : (preEntry (n := n) D hD .st y.1 y.1).tgt = q := htgt
      subst htgt'
      rw [moveTo_keepAll (pts := fun i => pts (shiftIx d n hdn i)) hkeep]
      exact (wins_preEntry I hdn hK .st y.1 y.1 _).mpr
        (show Lax535992.Game.AGStart (nodeAt I hdn y.1 0 fun i => pts (shiftIx d n hdn i)) by
          rw [hy']; exact hstart)
    · rw [List.mem_singleton] at hmem2
      subst hmem2
      have htgt' : Ph.main y.1 = q := htgt
      subst htgt'
      rw [moveTo_keepAll (pts := fun i => pts (shiftIx d n hdn i)) hkeep]
      exact wins_of_winsOn I hdn hK y hwin y.1 _ hy'.symm

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_accepts_iff)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : Lax480241.Expansions.ExpExpansion L} {T : Type} [Finite T] {d n Dm : ℕ}

variable {A : Type} [instL : L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable (I : Lax904597.Interpretations.FOInterpretation (X.E.sum Language.order) Lax535992.Game.andOrGraph T d)

variable (hdn : 2 * d ≤ n)

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

variable (hK : ∀ s tx ty, KernelSpec I hdn (n - D s tx ty) (D s tx ty) s tx ty (K s tx ty))

end ExpExpansion

/-! ### `EXPTIME ⊆ SO-GAME` -/

variable {L : Language.{0, 0}} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}

/-- **A second-order least fixed point is a second-order alternating game.** The
converse of `DescriptiveComplexity.SOGameDefinable.mem_EXPTIME`, and the half of
Chandra–Kozen–Stockmeyer that has content. -/
theorem SOLFPDefinable.soGameDefinable (h : Lax480241.SecondOrderFixedPoints.SOLFPDefinable P) : SOGameDefinable P := by
  obtain ⟨X, Q, hQ, hX⟩ := (solfpDefinable_iff_expDefinable P).mp h
  obtain ⟨f⟩ := game_hard_ordered Q hQ
  let := f.tagFinite
  let := f.tagNonempty
  obtain ⟨Dm, D, hD, K, hK⟩ :=
    ExpExpansion.exists_graphKernels X f.Tag f.dim f.toInterpretation
  refine ⟨ExpExpansion.graphGame X (n := 2 * f.dim + Dm) rfl D hD K, fun A _ _ _ _ => ?_⟩
  let := X.mapLinearOrder A
  have := X.mapFinite A
  have := X.mapNonempty A
  let := f.toInterpretation.mapStructure (X.Map A)
  refine (hX A).trans ?_
  refine Iff.trans (f.correct (X.Map A)) ?_
  exact (ExpExpansion.graphGame_accepts_iff f.toInterpretation (by omega) hK).symm

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.SecondOrderFixedPoints.SOLFPDefinable

export Lax480241Proofs.DescriptiveComplexity.SOLFPDefinable (soGameDefinable)

end Lax480241.SecondOrderFixedPoints.SOLFPDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}

end Lax480241Proofs.DescriptiveComplexity


