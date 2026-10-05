import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: GAME, alternating reachability
type: definition
---
An instance is an and-or graph: a directed graph of positions with moves
between them, some positions marked as universal, the others being
existential, some marked as starting positions and some as won outright.
The winning positions are the least set such that a position won outright
is winning, an existential position with a move to a winning position is
winning, and a universal position that has a move and all of whose moves
lead to winning positions is winning. The instance is a yes-instance of GAME
when some starting position is winning; GAME is the decision problem of the
structures isomorphic to such an instance. It is reachability in an
alternating graph.
-/

namespace Lax535992.Game

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive andOrGraphRel : ℕ → Type where
/-- `move a b`: the player to move at `a` may move to `b`. -/
  | move : andOrGraphRel 2
/-- `univ a`: the node `a` belongs to the universal player. -/
  | univ : andOrGraphRel 1
/-- `start a`: the node `a` is a marked starting position. -/
  | start : andOrGraphRel 1
/-- `won a`: the node `a` wins outright. -/
  | won : andOrGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
def andOrGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, andOrGraphRel⟩

instance instIsRelationalAndOrGraph : FirstOrder.Language.IsRelational andOrGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `move a b`: the player to move at `a` may move to `b`. -/
abbrev agMove : andOrGraph.Relations 2 :=
  .move

/-- `univ a`: the node `a` belongs to the universal player. -/
abbrev agUniv : andOrGraph.Relations 1 :=
  .univ

/-- `start a`: the node `a` is a marked starting position. -/
abbrev agStart : andOrGraph.Relations 1 :=
  .start

/-- `won a`: the node `a` wins outright. -/
abbrev agWon : andOrGraph.Relations 1 :=
  .won

open FirstOrder

open Language Structure

section Defs

variable {A : Type} [andOrGraph.Structure A]

/-- `move a b`: the player to move at `a` may move to `b`.  -/
def AGMove {A : Type} [andOrGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agMove ![a0, a1]

/-- `univ a`: the node `a` belongs to the universal player.  -/
def AGUniv {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agUniv ![a0]

/-- `start a`: the node `a` is a marked starting position.  -/
def AGStart {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agStart ![a0]

/-- `won a`: the node `a` wins outright.  -/
def AGWon {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agWon ![a0]

variable (A) in
/-- **The winning positions of an AND/OR graph**, as a least fixed point: a
position that wins outright, an existential position with a winning successor,
or a universal position that has a successor and all of whose successors
win. -/
inductive WinsOn : A → Prop
  /-- A position that wins outright. -/
  | won {a : A} : AGWon a → WinsOn a
  /-- An existential position with a winning successor. -/
  | ex {a b : A} : ¬AGUniv a → AGMove a b → WinsOn b → WinsOn a
  /-- A universal position with a successor, all of whose successors win. -/
  | all {a : A} : AGUniv a → (∃ b, AGMove a b) → (∀ b, AGMove a b → WinsOn b) → WinsOn a

variable (A) in
/-- Some marked starting position is winning. -/
def GameWon : Prop := ∃ s : A, AGStart s ∧ WinsOn A s

end Defs

/-- GAME, alternating reachability: does the existential player win from some
starting position? -/
def GAME : DecisionProblem andOrGraph := DecisionProblem.ofPred fun A _ => GameWon A

end Lax535992.Game
