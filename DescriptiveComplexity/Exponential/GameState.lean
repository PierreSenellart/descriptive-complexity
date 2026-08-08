/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameGraph

/-!
# The states of the graph game

The game `APSPACE-HARDNESS.md` §1.5 plays has one block for everything: `n`
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
| `pre s tx ty j pol` | `pol` | fill round `n - j`, or — at `j = 0` — be decided by the kernel |

Two of the six families are there for reasons that are easy to get wrong and
expensive to discover late.

* **`allCert` certifies a successor before the universal player moves.**
  `DescriptiveComplexity.WinsOn.all` requires a universal position to *have* a
  legal move, so a universal node with none loses; without the witness the
  simulation would let the existential player win there by refuting every
  proposed move. This is the stuck-universal convention of `EXPONENTIAL.md`
  §6(2), paid for once.
* **`allStep` is existential and may refute.** The universal player proposes an
  arbitrary tagged tuple of points, legal or not; the existential player escapes
  an illegal proposal by proving `¬AGMove x y` rather than by the move being
  filtered out, which no sentence over the base could do.

The claim phases (`exStep`, `allCert`) are universal with the *proof* and the
*play* as sibling moves: claiming falsely loses on the proof branch, so the
existential player is forced to tell the truth about `AGUniv x`.

## The states

A state is `DescriptiveComplexity.ExpExpansion.stateAssign`: a phase and one
assignment per round. Rounds are *not* guarded to be points in general — the play
rounds of a prefix range over all assignments, the guards living inside the
kernel (`DescriptiveComplexity.ExpExpansion.stepF`) — but the rounds of every
node-carrying phase are, which is what
`DescriptiveComplexity.ExpExpansion.allRoundsPointF` asserts at the start and
every node move preserves.
-/

namespace DescriptiveComplexity

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

variable {L : Language.{0, 0}} (X : ExpExpansion L) (n : ℕ) (T : Type) [Finite T] (Dm : ℕ)

/-- The one block of the graph game: `n` rounds of the point block, extended by
tag bits naming a phase. -/
abbrev gameBlock : SOBlock := (repMerged X.pointBlock n).withTag (Ph T Dm)

variable {X n T Dm} {A : Type} [L.Structure A] [LinearOrder A]

/-- **A state of the graph game**: a phase, and one assignment per round. -/
def stateAssign (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    (gameBlock X n T Dm).Assignment A :=
  SOBlock.tagAssign p (repBlockAssign X.pointBlock A n ρs)

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem dropTag_stateAssign (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    SOBlock.dropTag (stateAssign p ρs) = repBlockAssign X.pointBlock A n ρs :=
  rfl

/-- **Every state whose tag bits name a phase is one of these.** The junk
assignments — two tag bits set, or none — are the ones no move enters and no
start sentence admits. -/
theorem exists_stateAssign (τ : (gameBlock X n T Dm).Assignment A)
    (h : @Sentence.Realize _ A
      ((gameBlock X n T Dm).structure₁ (L := L.sum Language.order) τ)
      (SOBlock.tagGuardF (L := L.sum Language.order) (repMerged X.pointBlock n) (Ph T Dm))) :
    ∃ (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A), τ = stateAssign p ρs := by
  obtain ⟨p, ν, rfl⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) τ).mp h
  obtain ⟨ρs, rfl⟩ := repBlockAssign_split X.pointBlock A n ν
  exact ⟨p, ρs, rfl⟩

/-! ### Every round holds a point -/

variable (X n)

/-- **Every round of the state holds a point of the expanded universe.** True of
a starting state and preserved by every move between node phases; the play rounds
of a prefix are where it stops holding, and they are never read as parameters. -/
noncomputable def allRoundsPointF :
    ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence :=
  listInf ((List.finRange n).map (roundPointGuardF X n))

variable {X n} [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem realize_allRoundsPointF (ρs : Fin n → X.pointBlock.Assignment A) :
    (@Sentence.Realize _ A
        ((repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A n ρs)) (allRoundsPointF X n) ↔
      ∀ i, IsPointAssign (X := X) (ρs i)) := by
  letI := (repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
    (repBlockAssign X.pointBlock A n ρs)
  rw [allRoundsPointF, Sentence.Realize, realize_listInf]
  constructor
  · intro h i
    exact (realize_roundPointGuardF ρs i).mp (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_roundPointGuardF ρs i).mpr (h i)

omit [Finite A] [Nonempty A] in
/-- **A state all of whose rounds are points carries a tuple of points.** -/
theorem exists_points_of_allRoundsPoint {ρs : Fin n → X.pointBlock.Assignment A}
    (h : ∀ i, IsPointAssign (X := X) (ρs i)) :
    ∃ pts : Fin n → X.Map A, ρs = fun i => pointAssign (pts i) := by
  classical
  refine ⟨fun i => pt (Classical.choose (h i)) (Classical.choose (Classical.choose_spec (h i)))
    (Classical.choose_spec (Classical.choose_spec (h i))).2, ?_⟩
  funext i
  exact (Classical.choose_spec (Classical.choose_spec (h i))).1

end ExpExpansion

end DescriptiveComplexity
