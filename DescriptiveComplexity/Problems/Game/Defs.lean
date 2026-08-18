/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Problems.Reachability

/-!
# GAME: alternating reachability

The natural PTIME-complete problem the catalog was missing. An **AND/OR graph**
is a directed graph whose nodes are split between two players, together with a
set of nodes that win outright; a node is *winning* when

* it wins outright, or
* it belongs to the existential player and **some** successor is winning, or
* it belongs to the universal player, it **has** a successor, and **every**
  successor is winning.

`DescriptiveComplexity.GAME` asks whether some marked source is winning. Reading
the three clauses with the universal player removed gives
`DescriptiveComplexity.REACH` back, so this is alternating reachability in the
same sense that `DescriptiveComplexity.PSPACE` is `DescriptiveComplexity.NL`
with alternation: one operator more, one class up.

## The stuck-universal convention

A universal node with no successor **loses**. The other convention – vacuous
universal quantification, so that a stuck universal node wins – is equally
standard; this one is chosen because it is the convention
`DescriptiveComplexity.ATMData.AltWin` already uses, and matching them is what
lets the alternating machine's configuration graph be read as an instance of
this problem with nothing to adjust. A node that *should* win vacuously is
marked as winning outright instead, which is what the reduction from HORN-SAT
does with a clause that has no body.

## Winning as an inductive predicate

`DescriptiveComplexity.WinsOn` is an inductive predicate, i.e. the least fixed
point of the game operator, so an infinite play is a loss for the existential
player. That is also the presentation the FO(LFP) membership proof mirrors
clause by clause – with one twist, since a Horn rule cannot carry a universally
quantified body atom; see `DescriptiveComplexity.Problems.Game.Membership`.
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the vocabulary of AND/OR graphs. -/
inductive andOrRel : ℕ → Type
  /-- `move a b`: the player to move at `a` may move to `b`. -/
  | move : andOrRel 2
  /-- `univ a`: the node `a` belongs to the universal player. -/
  | univ : andOrRel 1
  /-- `start a`: the node `a` is a marked starting position. -/
  | start : andOrRel 1
  /-- `won a`: the node `a` wins outright. -/
  | won : andOrRel 1
  deriving DecidableEq

/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
protected def andOrGraph : Language :=
  ⟨fun _ => Empty, andOrRel⟩
  deriving IsRelational

/-- The move symbol. -/
abbrev agMove : Language.andOrGraph.Relations 2 := .move

/-- The universal-player symbol. -/
abbrev agUniv : Language.andOrGraph.Relations 1 := .univ

/-- The marked-start symbol. -/
abbrev agStart : Language.andOrGraph.Relations 1 := .start

/-- The won-outright symbol. -/
abbrev agWon : Language.andOrGraph.Relations 1 := .won

/-- The move symbol in the ordered expansion. -/
abbrev agMoveO : (Language.andOrGraph.sum Language.order).Relations 2 := Sum.inl agMove

/-- The universal-player symbol in the ordered expansion. -/
abbrev agUnivO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agUniv

/-- The marked-start symbol in the ordered expansion. -/
abbrev agStartO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agStart

/-- The won-outright symbol in the ordered expansion. -/
abbrev agWonO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agWon

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The semantics -/

section Defs

variable {A : Type} [Language.andOrGraph.Structure A]

/-- The move relation of an AND/OR graph. -/
def AGMove (a b : A) : Prop := RelMap agMove ![a, b]

/-- Belonging to the universal player. -/
def AGUniv (a : A) : Prop := RelMap agUniv ![a]

/-- Being a marked starting position. -/
def AGStart (a : A) : Prop := RelMap agStart ![a]

/-- Winning outright. -/
def AGWon (a : A) : Prop := RelMap agWon ![a]

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

/-! ### Without the universal player, the game is reachability -/

section Collapse

variable {A : Type} [Language.andOrGraph.Structure A]

end Collapse

/-! ### Isomorphism-invariance -/

section Iso

variable {A B : Type} [Language.andOrGraph.Structure A] [Language.andOrGraph.Structure B]

private theorem agMove_map (e : A ≃[Language.andOrGraph] B) (a b : A) :
    AGMove a b ↔ AGMove (e a) (e b) :=
  relMap_equiv₂ e agMove a b

private theorem winsOn_of_iso (e : A ≃[Language.andOrGraph] B) {a : A} (h : WinsOn A a) :
    WinsOn B (e a) := by
  induction h with
  | won hw => exact .won ((relMap_equiv₁ e agWon _).mp hw)
  | @ex a b hu hm _ ih =>
    exact .ex (fun hc => hu ((relMap_equiv₁ e agUniv a).mpr hc)) ((agMove_map e a b).mp hm) ih
  | @all a hu hex _ ih =>
    refine .all ((relMap_equiv₁ e agUniv a).mp hu) ?_ ?_
    · obtain ⟨b, hb⟩ := hex
      exact ⟨e b, (agMove_map e a b).mp hb⟩
    · intro b hb
      obtain ⟨b₀, rfl⟩ : ∃ b₀ : A, e b₀ = b := ⟨e.symm b, e.toEquiv.apply_symm_apply b⟩
      exact ih b₀ ((agMove_map e a b₀).mpr hb)

private theorem gameWon_of_iso (e : A ≃[Language.andOrGraph] B) (h : GameWon A) : GameWon B := by
  obtain ⟨s, hs, hw⟩ := h
  exact ⟨e s, (relMap_equiv₁ e agStart s).mp hs, winsOn_of_iso e hw⟩

/-- Being won is isomorphism-invariant. -/
theorem gameWon_iso (e : A ≃[Language.andOrGraph] B) : GameWon A ↔ GameWon B :=
  ⟨gameWon_of_iso e, gameWon_of_iso e.symm⟩

end Iso

/-- **GAME**, alternating reachability: is some marked starting position of the
AND/OR graph winning? -/
def GAME : DecisionProblem Language.andOrGraph where
  Holds := fun A inst => @GameWon A inst
  iso_invariant := fun e => gameWon_iso e

@[simp]
theorem game_holds_iff (A : Type) [Language.andOrGraph.Structure A] :
    GAME A ↔ GameWon A :=
  Iff.rfl

end DescriptiveComplexity
