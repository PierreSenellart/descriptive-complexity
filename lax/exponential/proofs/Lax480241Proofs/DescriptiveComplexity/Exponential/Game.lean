/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.Copies
import Lax480241Proofs.DescriptiveComplexity.Exponential.Classes
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

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.Expansions
end Lax480241.Expansions

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax535992.Game
end Lax535992.Game

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

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
export Lax535992.Game (AGMove AGStart AGUniv AGWon GameWon WinsOn)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

namespace FirstOrder.Language
export Lax535992.Game (andOrGraph)
end FirstOrder.Language

/-!
# A second-order alternating game is GAME on an exponential expansion

The alternating counterpart of `DescriptiveComplexity.Exponential.Reach`, and
the way into EXPTIME that needs no succinctness argument. Compare the two
definitions, which are the same sentence up to the name of the universe:

```
SOGameSpec.Accepts A = ∃ ρ, spec.IsStart ρ ∧ spec.Wins ρ
GameWon            M = ∃ s, AGStart s   ∧ WinsOn M s
```

A `DescriptiveComplexity.SOGameSpec` is the game
`DescriptiveComplexity.GAME` reads on *assignments of a second-order block*:
four first-order sentences say which assignments the existential player owns,
which win outright, which start the game, and which moves are legal – the
transition seeing two copies of the block, as an
`DescriptiveComplexity.SOTCSpec` does. Its expansion
(`DescriptiveComplexity.SOGameSpec.toExp`) therefore takes `Tag := Unit`, no
domain restriction, the block of the specification, and the vocabulary of
AND/OR graphs, and its points are the states
(`DescriptiveComplexity.SOGameSpec.toExpEquiv`).

Since `DescriptiveComplexity.GAME` is in `DescriptiveComplexity.PTIME`, this
gives at once

* `DescriptiveComplexity.SOGameDefinable.mem_EXPTIME`: **a second-order
  alternating game is in EXPTIME**,

which read on the definitions is **SO-GAME ⊆ SO(LFP)** – the second-order
shadow of `GAME ∈ PTIME`, exactly as
`DescriptiveComplexity.PSPACE_subset_EXPTIME` is the second-order shadow of
`REACH ∈ PTIME`.

## What this is for

Writing a machine's configuration graph as an expansion by hand means writing
its transition relation as a sentence over the base plus two copies of a block,
and nothing else: this file takes care of everything that is *not* those four
sentences. It is what an alternating space-bounded machine
(`DescriptiveComplexity.ATMAcceptSpace`) consumes, its configurations being the
assignments of a block with one variable for the state, one for the head and one
for the tape.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The specification -/

/-- **A second-order alternating game**: the states of the game are the
assignments of a block `B`, and four first-order sentences over the base
vocabulary expanded by the order and by copies of the block say which states are
universal, which win outright, which start the game, and which moves are legal.
The move sentence sees two copies of the block – the current state and the next
one – exactly as `DescriptiveComplexity.SOTCSpec.step` does.

The order is visible to all four sentences, as the ordered setting of the
capture theorems allows; the problem itself does not see it. -/
structure SOGameSpec (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the game. -/
  B : Lax904597.SecondOrder.SOBlock
  /-- The move sentence, over two copies of the block: the current state reads
  the first copy, the next state the second. -/
  move : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the states of the universal player. -/
  univ : ((L.sum Language.order).sum B.lang).Sentence
  /-- The sentence defining the states that win outright. -/
  won : ((L.sum Language.order).sum B.lang).Sentence
  /-- The sentence defining the starting states. -/
  start : ((L.sum Language.order).sum B.lang).Sentence

namespace SOGameSpec

section Semantics

variable {L : Language.{0, 0}} (spec : SOGameSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A state of the game: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- A legal move: the move sentence, read with the current state in the first
copy of the block and the next state in the second. -/
def Move (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₂ (L := L.sum Language.order) ρ σ) spec.move

/-- A state belongs to the universal player. -/
def IsUniv (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L.sum Language.order) ρ) spec.univ

/-- A state wins outright. -/
def IsWon (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L.sum Language.order) ρ) spec.won

/-- A state starts the game. -/
def IsStart (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L.sum Language.order) ρ) spec.start

/-- **The winning states**, as a least fixed point: a state that wins outright,
an existential state with a winning move, or a universal state that has a move
and all of whose moves are winning. -/
inductive Wins : spec.State A → Prop
  /-- A state that wins outright. -/
  | won {ρ : spec.State A} : spec.IsWon ρ → Wins ρ
  /-- An existential state with a winning move. -/
  | ex {ρ σ : spec.State A} : ¬spec.IsUniv ρ → spec.Move ρ σ → Wins σ → Wins ρ
  /-- A universal state with a move, all of whose moves are winning. -/
  | all {ρ : spec.State A} : spec.IsUniv ρ → (∃ σ, spec.Move ρ σ) →
      (∀ σ, spec.Move ρ σ → Wins σ) → Wins ρ

variable (A) in
/-- The structure is accepted: some starting state is winning. -/
def Accepts : Prop := ∃ ρ : spec.State A, spec.IsStart ρ ∧ spec.Wins ρ

end Semantics

/-! ### The expansion of a specification -/

variable {L : Language.{0, 0}} (spec : SOGameSpec L)

/-- **The expansion whose points are the states of the game**: no tags, no
domain restriction, and the four sentences of the specification defining the
four symbols of the vocabulary of AND/OR graphs. -/
def toExp : Lax480241.Expansions.ExpExpansion L where
  Tag := Unit
  B := spec.B
  E := Lax535992.Game.andOrGraph
  dom _ := ⊤
  relSentence {n} r _ :=
    match n, r with
    | _, .move => (spec.B.twoLHom (L.sum Language.order)).onSentence spec.move
    | _, .univ => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.univ
    | _, .start => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.start
    | _, .won => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.won
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨(), spec.B.botAssign A, ?_⟩
    let := spec.B.structure₁ (L := L.sum Language.order) (spec.B.botAssign A)
    exact Formula.realize_top.mpr trivial

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- The expanded structure of `DescriptiveComplexity.SOGameSpec.toExp`, at the
vocabulary of AND/OR graphs – equal to the expansion's own by definition, but
not syntactically, so instance search has to be handed it. -/
@[instance_reducible]
def toExpStructure : Lax535992.Game.andOrGraph.Structure (spec.toExp.Map A) :=
  spec.toExp.mapStructure A

/-- The domain of `DescriptiveComplexity.SOGameSpec.toExp` is the whole space of
tagged assignments: its domain sentence is `⊤`. -/
theorem domHolds_toExp (p : spec.toExp.Point A) : Lax480241.Expansions.ExpExpansion.DomHolds p := by
  let := spec.toExp.B.structure₁ (L := L.sum Language.order) p.2
  exact Formula.realize_top.mpr trivial

/-- **The points of the expansion are the states of the game.** -/
def toExpEquiv : spec.toExp.Map A ≃ spec.State A where
  toFun x := x.1.2
  invFun ρ := ⟨((), ρ), spec.domHolds_toExp A ((), ρ)⟩
  left_inv _ := ExpExpansion.map_ext rfl rfl
  right_inv _ := rfl

/-! ### The four symbols -/

variable {A}

/-- **The move symbol is the move sentence.** -/
theorem agMove_toExp (x y : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax535992.Game.AGMove x y ↔ spec.Move x.1.2 y.1.2 :=
  SOBlock.realize_twoLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x, y] : Fin 2 → spec.toExp.Map A) i).1.2) spec.move

/-- **The universal nodes are the universal states.** -/
theorem agUniv_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax535992.Game.AGUniv x ↔ spec.IsUniv x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.univ

/-- **The nodes that win outright are the states that do.** -/
theorem agWon_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax535992.Game.AGWon x ↔ spec.IsWon x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.won

/-- **The marked starts are the starting states.** -/
theorem agStart_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    Lax535992.Game.AGStart x ↔ spec.IsStart x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.start

/-! ### Winning is winning -/

private theorem wins_of_winsOn :
    letI := spec.toExpStructure A
    ∀ {x : spec.toExp.Map A}, Lax535992.Game.WinsOn (spec.toExp.Map A) x → spec.Wins x.1.2 := by
  let := spec.toExpStructure A
  intro x h
  induction h with
  | won hw => exact .won ((spec.agWon_toExp _).mp hw)
  | @ex a b hu hm _ ih =>
    exact .ex (fun hc => hu ((spec.agUniv_toExp a).mpr hc)) ((spec.agMove_toExp a b).mp hm) ih
  | @all a hu hex _ ih =>
    refine .all ((spec.agUniv_toExp a).mp hu) ?_ ?_
    · obtain ⟨b, hb⟩ := hex
      exact ⟨b.1.2, (spec.agMove_toExp a b).mp hb⟩
    · intro σ hσ
      exact ih ((spec.toExpEquiv A).symm σ) ((spec.agMove_toExp a _).mpr hσ)

private theorem winsOn_of_wins :
    letI := spec.toExpStructure A
    ∀ {ρ : spec.State A}, spec.Wins ρ →
      Lax535992.Game.WinsOn (spec.toExp.Map A) ((spec.toExpEquiv A).symm ρ) := by
  let := spec.toExpStructure A
  intro ρ h
  induction h with
  | won hw => exact .won ((spec.agWon_toExp _).mpr hw)
  | @ex ρ σ hu hm _ ih =>
    refine .ex (b := (spec.toExpEquiv A).symm σ) (fun hc => hu ((spec.agUniv_toExp _).mp hc))
      ((spec.agMove_toExp _ _).mpr hm) ih
  | @all ρ hu hex _ ih =>
    refine .all ((spec.agUniv_toExp _).mpr hu) ?_ ?_
    · obtain ⟨σ, hσ⟩ := hex
      exact ⟨(spec.toExpEquiv A).symm σ, (spec.agMove_toExp _ _).mpr hσ⟩
    · intro y hy
      have hy' : spec.Move ρ y.1.2 := (spec.agMove_toExp _ y).mp hy
      have := ih y.1.2 hy'
      rwa [show (spec.toExpEquiv A).symm y.1.2 = y from
        (spec.toExpEquiv A).symm_apply_apply y] at this

variable (A)

/-- **The game accepts exactly when GAME holds of the expansion.** -/
theorem gameWon_toExp_iff :
    letI := spec.toExpStructure A
    Lax535992.Game.GameWon (spec.toExp.Map A) ↔ spec.Accepts A := by
  let := spec.toExpStructure A
  constructor
  · rintro ⟨s, hs, hw⟩
    exact ⟨s.1.2, (spec.agStart_toExp s).mp hs, spec.wins_of_winsOn hw⟩
  · rintro ⟨ρ, hρ, hw⟩
    exact ⟨(spec.toExpEquiv A).symm ρ, (spec.agStart_toExp _).mpr hρ, spec.winsOn_of_wins hw⟩

end SOGameSpec

/-! ### Definability, and the class -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **SO-GAME definability**: the problem is the value of a second-order
alternating game, on nonempty finite ordered structures. -/
def SOGameDefinable (P : Lax904597.Problems.DecisionProblem L) : Prop :=
  ∃ spec : SOGameSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

/-- **A second-order alternating game is GAME over an expanded universe**: the
game is the AND/OR graph the expansion draws, so any class containing GAME
contains the problem one exponential up. -/
theorem SOGameDefinable.expDefinable {C : ComplexityClass} (hgame : GAME ∈ C)
    {P : Lax904597.Problems.DecisionProblem L} (h : SOGameDefinable P) : ExpDefinable C P := by
  obtain ⟨spec, hspec⟩ := h
  let hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      Lax535992.Game.andOrGraph.Structure (spec.toExp.Map A) := fun A => spec.toExpStructure A
  refine ⟨spec.toExp, GAME, hgame, ?_⟩
  intro A _ _ _ _
  exact (hspec A).trans (spec.gameWon_toExp_iff A).symm

/-- **A second-order alternating game is in EXPTIME.** Read on the definitions
this is **SO-GAME ⊆ SO(LFP)** – the second-order shadow of `GAME ∈ PTIME`, and
the way into EXPTIME that needs no succinctness argument. -/
theorem SOGameDefinable.mem_EXPTIME {P : Lax904597.Problems.DecisionProblem L} (h : SOGameDefinable P) :
    P ∈ EXPTIME := by
  rw [EXPTIME_eq_PTIME_exp]
  exact h.expDefinable game_mem_PTIME

end Lax480241Proofs.DescriptiveComplexity


