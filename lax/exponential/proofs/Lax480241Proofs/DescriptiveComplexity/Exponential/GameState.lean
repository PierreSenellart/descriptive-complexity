/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameGraph
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

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# The states of the graph game

The game that carries `DescriptiveComplexity.EXPTIME` to SO-GAME has one
block for everything: `n`
rounds of the point block (`DescriptiveComplexity.repMerged`) extended by tag
bits naming a **phase**. This file fixes the phases and says what a state is.

## The phases

`DescriptiveComplexity.Ph` has six families, and the whole design of the game is
in the table:

| phase | owner | what its moves are |
|---|---|---|
| `startPick tx` | ∀ | prove `AGStart x`; and play from `x` |
| `main tx` | ∃ | claim `AGWon x`; or claim `x` is existential; or claim it is universal |
| `exStep tx ty` | ∀ | prove `¬AGUniv x`; prove `AGMove x y`; and win from `y` |
| `allCert tx ty` | ∀ | prove `AGUniv x`; prove `AGMove x y`; and answer every `y'` |
| `allStep tx ty` | ∃ | refute `AGMove x y`; or win from `y` |
| `pre s tx ty j pol` | `pol` | fill round `n - j`, or – at `j = 0` – be decided by the kernel |

Two of the six families are there for reasons that are easy to get wrong and
expensive to discover late.

* **`allCert` certifies a successor before the universal player moves.**
  `DescriptiveComplexity.WinsOn.all` requires a universal position to *have* a
  legal move, so a universal node with none loses; without the witness the
  simulation would let the existential player win there by refuting every
  proposed move. The convention that a stuck universal position loses is paid
  for here, once.
* **`allStep` is existential and may refute.** The universal player proposes an
  arbitrary tagged tuple of points, legal or not; the existential player escapes
  an illegal proposal by proving `¬AGMove x y` rather than by the move being
  filtered out, which no sentence over the base could do.

The claim phases (`exStep`, `allCert`) are universal with the *proof* and the
*play* as sibling moves: claiming falsely loses on the proof branch, so the
existential player is forced to tell the truth about `AGUniv x`.

## The states

A state is `DescriptiveComplexity.ExpExpansion.stateAssign`: a phase and one
assignment per round. Rounds are *not* guarded to be points in general – the play
rounds of a prefix range over all assignments, the guards living inside the
kernel (`DescriptiveComplexity.ExpExpansion.stepF`) – but the rounds of every
node-carrying phase are, which is what
`DescriptiveComplexity.ExpExpansion.allRoundsPointF` asserts at the start and
every node move preserves.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The phases -/

/-- The phases of the graph game: `tx`, `ty` are the tags of the two nodes the
state carries, `j` the number of play rounds a prefix has left and `pol` the
player whose turn it is there. -/
inductive Ph (T : Type) (Dm : ℕ)
  /-- A candidate start node has been chosen. -/
  | startPick (tx : T)
  /-- The game is at the node `x`. -/
  | main (tx : T)
  /-- The existential player claims `x` is his and moves to `y`. -/
  | exStep (tx ty : T)
  /-- The existential player claims `x` is universal, with `y` as witness. -/
  | allCert (tx ty : T)
  /-- The universal player has proposed the move to `y`. -/
  | allStep (tx ty : T)
  /-- A question is being decided, `j` play rounds left. -/
  | pre (s : Sub) (tx ty : T) (j : Fin (Dm + 1)) (pol : Bool)
  deriving DecidableEq

namespace Ph

variable {T : Type} {Dm : ℕ}

/-- The phases, coded into a sum of products, so that finiteness is
inherited. -/
private def code : Ph T Dm →
    T ⊕ T ⊕ (T × T) ⊕ (T × T) ⊕ (T × T) ⊕ (Sub × T × T × Fin (Dm + 1) × Bool)
  | .startPick tx => .inl tx
  | .main tx => .inr (.inl tx)
  | .exStep tx ty => .inr (.inr (.inl (tx, ty)))
  | .allCert tx ty => .inr (.inr (.inr (.inl (tx, ty))))
  | .allStep tx ty => .inr (.inr (.inr (.inr (.inl (tx, ty)))))
  | .pre s tx ty j pol => .inr (.inr (.inr (.inr (.inr (s, tx, ty, j, pol)))))

private theorem code_injective : Function.Injective (code (T := T) (Dm := Dm)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [code]

instance [Finite T] : Finite (Ph T Dm) :=
  Finite.of_injective _ code_injective

/-- **Who owns a phase.** The two claim phases and the start phase are
universal, a prefix position is universal exactly when its polarity says so and
it still has a round to fill, and everything else is existential. -/
def IsUniv : Ph T Dm → Prop
  | .startPick _ => True
  | .main _ => False
  | .exStep _ _ => True
  | .allCert _ _ => True
  | .allStep _ _ => False
  | .pre _ _ _ j pol => (j : ℕ) ≠ 0 ∧ pol = false

instance : DecidablePred (IsUniv (T := T) (Dm := Dm)) := by
  intro p
  cases p <;> unfold IsUniv <;> infer_instance

end Ph

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

/-- The one block of the graph game: `n` rounds of the point block, extended by
tag bits naming a phase. -/
abbrev gameBlock : Lax904597.SecondOrder.SOBlock := (repMerged X.pointBlock n).withTag (Ph T Dm)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (gameBlock)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

/-- **A state of the graph game**: a phase, and one assignment per round. -/
def stateAssign (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    (gameBlock X n T Dm).Assignment A :=
  SOBlock.tagAssign p (repBlockAssign X.pointBlock A n ρs)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (stateAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem dropTag_stateAssign (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    SOBlock.dropTag (stateAssign p ρs) = repBlockAssign X.pointBlock A n ρs :=
  rfl

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (dropTag_stateAssign)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

/-! ### Every round holds a point -/

variable (X n)

/-- **Every round of the state holds a point of the expanded universe.** True of
a starting state and preserved by every move between node phases; the play rounds
of a prefix are where it stops holding, and they are never read as parameters. -/
noncomputable def allRoundsPointF :
    ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence :=
  listInf ((List.finRange n).map (roundPointGuardF X n))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (allRoundsPointF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

variable (X n)

variable {X n} [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem realize_allRoundsPointF (ρs : Fin n → X.pointBlock.Assignment A) :
    (@Sentence.Realize _ A
        ((repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A n ρs)) (allRoundsPointF X n) ↔
      ∀ i, IsPointAssign (X := X) (ρs i)) := by
  let := (repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
    (repBlockAssign X.pointBlock A n ρs)
  rw [allRoundsPointF, Sentence.Realize, realize_listInf]
  constructor
  · intro h i
    exact (realize_roundPointGuardF ρs i).mp (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_roundPointGuardF ρs i).mpr (h i)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_allRoundsPointF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

variable (X n)

variable {X n} [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- **A state all of whose rounds are points carries a tuple of points.** -/
theorem exists_points_of_allRoundsPoint {ρs : Fin n → X.pointBlock.Assignment A}
    (h : ∀ i, IsPointAssign (X := X) (ρs i)) :
    ∃ pts : Fin n → X.Map A, ρs = fun i => pointAssign (pts i) := by
  classical
  refine ⟨fun i => Lax480241.Expansions.ExpExpansion.pt (Classical.choose (h i)) (Classical.choose (Classical.choose_spec (h i)))
    (Classical.choose_spec (Classical.choose_spec (h i))).2, ?_⟩
  funext i
  exact (Classical.choose_spec (Classical.choose_spec (h i))).1

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (exists_points_of_allRoundsPoint)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

variable (X n)

variable {X n} [Finite A] [Nonempty A]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


