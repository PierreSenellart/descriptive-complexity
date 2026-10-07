/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameState
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

namespace Lax480241Proofs.DescriptiveComplexity.ExpExpansion
end Lax480241Proofs.DescriptiveComplexity.ExpExpansion

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax480241Proofs.DescriptiveComplexity
export Lax480241.Expansions (ExpExpansion)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

/-!
# The graph game, as a second-order alternating game

The four sentences of `DescriptiveComplexity.ExpExpansion.graphGame`, and what
each of them says. Every one is a **static disjunction over the phase type**,
which is finite: the phases carry the tags of the two nodes a state holds, so
naming a tag costs a disjunct rather than a quantifier.

* `univ` – the phases `DescriptiveComplexity.Ph.IsUniv` selects, and nothing
  else;
* `won` – a leaf `pre s tx ty 0 pol`, conjoined with that question's kernel. The
  leaf is existential and has **no move**, so a false kernel loses: a player who
  asked for a proof he cannot give is stuck there;
* `start` – a `startPick` phase whose rounds all hold points
  (`DescriptiveComplexity.ExpExpansion.allRoundsPointF`), which is the invariant
  every node move preserves and every prefix consumes;
* `move` – one disjunct per pair of a phase and one of the moves
  `DescriptiveComplexity.ExpExpansion.movesFrom` allows out of it. A move names
  its target phase exactly (`DescriptiveComplexity.atTagTwoF`, so no junk state
  is reachable), lists the rounds it carries over – kept, shifted, or neither –
  and lists the rounds of the state it enters that it guards to be points.

The one asymmetry worth naming: the move that fills a **play** round guards
nothing. `DescriptiveComplexity.altBlockQuant` ranges over *all* assignments and
the point guards of a prefix live inside its kernel
(`DescriptiveComplexity.ExpExpansion.stepF`), so guarding there would count them
twice and break the correspondence with
`DescriptiveComplexity.ExpExpansion.exists_paramKernel`.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The rounds a move carries over -/

section Rounds

variable (d n : ℕ)

/-- Carry over every round: the move freezes the state. -/
def keepAll : List (Fin n × Fin n) := (List.finRange n).map fun i => (i, i)

/-- Carry over every round outside `S`, in place. -/
def keepOff (S : Fin n → Bool) : List (Fin n × Fin n) :=
  ((List.finRange n).filter fun i => !S i).map fun i => (i, i)

/-- The rounds holding the second node's points. -/
def isMid : Fin n → Bool := fun i => decide (d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d)

/-- The rounds holding the second node's points, as a list. -/
def midRounds : List (Fin n) := (List.finRange n).filter (isMid d n)

/-- Where round `i` of the state a shifting move enters reads from: the second
node's points become the first node's. -/
def shiftIx (h : 2 * d ≤ n) (i : Fin n) : Fin n :=
  if hi : (i : ℕ) < d then ⟨(i : ℕ) + d, by omega⟩ else i

/-- Carry the second node's points onto the first node's slots. -/
def keepShift (h : 2 * d ≤ n) : List (Fin n × Fin n) :=
  (List.finRange n).map fun i => (shiftIx d n h i, i)

variable {d n}

theorem forall_keepAll {α : Type} (ρs σs : Fin n → α) :
    (∀ e ∈ keepAll n, ρs e.1 = σs e.2) ↔ ρs = σs := by
  constructor
  · intro h
    funext i
    exact h (i, i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · rintro rfl e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
    rfl

theorem forall_keepOff {α : Type} (S : Fin n → Bool) (ρs σs : Fin n → α) :
    (∀ e ∈ keepOff n S, ρs e.1 = σs e.2) ↔ ∀ i, S i = false → ρs i = σs i := by
  constructor
  · intro h i hi
    refine h (i, i) (List.mem_map.mpr ⟨i, ?_, rfl⟩)
    exact List.mem_filter.mpr ⟨List.mem_finRange i, by simp [hi]⟩
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    obtain ⟨-, hS⟩ := List.mem_filter.mp hi
    exact h i (by simpa using hS)

theorem forall_keepShift {α : Type} (h : 2 * d ≤ n) (ρs σs : Fin n → α) :
    (∀ e ∈ keepShift d n h, ρs e.1 = σs e.2) ↔ ∀ i, ρs (shiftIx d n h i) = σs i := by
  constructor
  · intro hh i
    exact hh _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · intro hh e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
    exact hh i

theorem mem_midRounds (i : Fin n) :
    i ∈ midRounds d n ↔ d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d := by
  rw [midRounds, List.mem_filter]
  simp [isMid, List.mem_finRange]

theorem isMid_eq_false (i : Fin n) : isMid d n i = false ↔ ¬(d ≤ (i : ℕ) ∧ (i : ℕ) < 2 * d) := by
  simp [isMid]

end Rounds

/-! ### The moves out of a phase -/

/-- A move of the graph game, seen from the phase it leaves: where it goes,
which rounds it carries over – as pairs (round of the state left, round of the
state entered) – and which rounds of the state entered it guards to hold a
point. -/
structure MoveTo (T : Type) (Dm n : ℕ) where
  /-- The phase the move enters. -/
  tgt : Ph T Dm
  /-- The rounds it carries over. -/
  keep : List (Fin n × Fin n)
  /-- The rounds of the state it enters that it guards to hold a point. -/
  guard : List (Fin n)

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

/-- Entering the prefix that decides the question `s` about the nodes tagged
`tx`, `ty`: nothing moves, and all `D s tx ty` play rounds are still to
fill. -/
def preEntry (D : Sub → T → T → ℕ) (hD : ∀ s tx ty, D s tx ty ≤ Dm) (s : Sub) (tx ty : T) :
    MoveTo T Dm n :=
  ⟨.pre s tx ty ⟨D s tx ty, by have := hD s tx ty; omega⟩ true, keepAll n, []⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (preEntry)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

/-- **The moves out of each phase.** This is the game. -/
noncomputable def movesFrom (hn : n = 2 * d + Dm) (D : Sub → T → T → ℕ)
    (hD : ∀ s tx ty, D s tx ty ≤ Dm) : Ph T Dm → List (MoveTo T Dm n)
  | .startPick tx => [preEntry D hD .st tx tx, ⟨.main tx, keepAll n, []⟩]
  | .main tx =>
      preEntry D hD .won tx tx ::
        (finEnum T).flatMap fun ty =>
          [⟨.exStep tx ty, keepOff n (isMid d n), midRounds d n⟩,
            ⟨.allCert tx ty, keepOff n (isMid d n), midRounds d n⟩]
  | .exStep tx ty =>
      [preEntry D hD .notuniv tx tx, preEntry D hD .mv tx ty,
        ⟨.main ty, keepShift d n (by omega), []⟩]
  | .allCert tx ty =>
      preEntry D hD .univ tx tx :: preEntry D hD .mv tx ty ::
        (finEnum T).map fun ty' => ⟨.allStep tx ty', keepOff n (isMid d n), midRounds d n⟩
  | .allStep tx ty =>
      [preEntry D hD .notmv tx ty, ⟨.main ty, keepShift d n (by omega), []⟩]
  | .pre s tx ty j pol =>
      if h : (j : ℕ) = 0 then []
      else
        [⟨.pre s tx ty ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ (!pol),
          keepOff n (fun i => decide (i = ⟨n - (j : ℕ), by have := j.isLt; omega⟩)), []⟩]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (movesFrom)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

/-! ### The four sentences -/

/-- The sentence of one move: it names the phase it leaves and the phase it
enters, carries its rounds over, and guards the rounds it says are points. -/
noncomputable def moveOf (p : Ph T Dm) (m : MoveTo T Dm n) :
    (((L.sum Language.order).sum (gameBlock X n T Dm).lang).sum
      (gameBlock X n T Dm).lang).Sentence :=
  LHom.sumInl.onSentence (atTagF L (repMerged X.pointBlock n) (Ph T Dm) p) ⊓
    (atTagTwoF L (repMerged X.pointBlock n) (Ph T Dm) m.tgt ⊓
      (roundsAgreeS L X.pointBlock n (Ph T Dm) m.keep ⊓
        listInf (m.guard.map fun i =>
          (moveSndLHom L (repMerged X.pointBlock n) (Ph T Dm)).onSentence
            (roundPointGuardF X n i))))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (moveOf)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

/-- **The graph game**: the game whose positions are the nodes of the AND/OR
graph an interpretation draws on the expanded universe, together with the
prefix positions that decide the six questions about them. -/
noncomputable def graphGame (hn : n = 2 * d + Dm) (D : Sub → T → T → ℕ)
    (hD : ∀ s tx ty, D s tx ty ≤ Dm)
    (K : ∀ (_s : Sub) (_tx _ty : T),
      ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence) :
    SOGameSpec L where
  B := gameBlock X n T Dm
  move := listSup ((finEnum (Ph T Dm)).flatMap fun p =>
    (movesFrom hn D hD p).map (moveOf X p))
  univ := listSup (((finEnum (Ph T Dm)).filter fun p => decide (Ph.IsUniv p)).map
    (atTagF L (repMerged X.pointBlock n) (Ph T Dm)))
  won := listSup ((finEnum (Sub × T × T × Bool)).map fun e =>
    atTagF L (repMerged X.pointBlock n) (Ph T Dm)
        (.pre e.1 e.2.1 e.2.2.1 ⟨0, Nat.succ_pos Dm⟩ e.2.2.2) ⊓
      (withTagLHom L (repMerged X.pointBlock n) (Ph T Dm)).onSentence (K e.1 e.2.1 e.2.2.1))
  start := listSup ((finEnum T).map fun tx =>
    atTagF L (repMerged X.pointBlock n) (Ph T Dm) (.startPick tx) ⊓
      (withTagLHom L (repMerged X.pointBlock n) (Ph T Dm)).onSentence (allRoundsPointF X n))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

/-! ### What the four sentences say -/

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

theorem realize_moveOf (p' p q : Ph T Dm) (m : MoveTo T Dm n)
    (ρs σs : Fin n → X.pointBlock.Assignment A) :
    (@Sentence.Realize _ A
        (@Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
          (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) (stateAssign q σs))
        (moveOf X p' m) ↔
      p' = p ∧ m.tgt = q ∧ (∀ e ∈ m.keep, ρs e.1 = σs e.2) ∧
        (∀ i ∈ m.guard, IsPointAssign (X := X) (σs i))) := by
  let := @Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
    (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) (stateAssign q σs)
  rw [moveOf, Sentence.Realize, Formula.realize_inf]
  refine and_congr ?_ ?_
  · exact (realize_tagFst _ _ _).trans (realize_atTagF p' p _)
  · rw [Formula.realize_inf]
    refine and_congr (realize_atTagTwoF m.tgt q _ _) ?_
    rw [Formula.realize_inf]
    refine and_congr (realize_roundsAgreeS p q ρs σs m.keep) ?_
    rw [realize_listInf]
    constructor
    · intro h i hi
      exact (realize_roundPointGuardF σs i).mp
        ((realize_moveSndLHom _ _ _).mp (h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)))
    · intro h ψ hψ
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hψ
      exact (realize_moveSndLHom _ _ _).mpr ((realize_roundPointGuardF σs i).mpr (h i hi))

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_moveOf)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- The one-copy structure a state of the graph game is read against. -/
@[instance_reducible]
noncomputable def stateStructure (σ : (gameBlock X n T Dm).Assignment A) :
    ((L.sum Language.order).sum (gameBlock X n T Dm).lang).Structure A :=
  @Lax480241.Expansions.SOBlock.structure₁ (L.sum Language.order) (gameBlock X n T Dm) A
    (@Lax904597.Interpretations.sumOrderStructure L A instL _) σ

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (stateStructure)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

theorem realize_listSup_atTagF (p : Ph T Dm)
    (ρs : Fin n → X.pointBlock.Assignment A) (l : List (Ph T Dm)) :
    (@Sentence.Realize _ A (stateStructure (stateAssign p ρs))
        (listSup (l.map (atTagF L (repMerged X.pointBlock n) (Ph T Dm)))) ↔ p ∈ l) := by
  let := stateStructure (X := X) (stateAssign p ρs)
  rw [Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hψ
    exact (realize_atTagF q p _).mp hr ▸ hq
  · intro hp
    exact ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, (realize_atTagF p p _).mpr rfl⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (realize_listSup_atTagF)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- **The universal positions are the phases `Ph.IsUniv` names.** -/
theorem graphGame_isUniv (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    ((graphGame X hn D hD K).IsUniv (stateAssign p ρs) ↔ Ph.IsUniv p) := by
  have hrw : (graphGame X hn D hD K).IsUniv (stateAssign p ρs) ↔
      @Sentence.Realize _ A (stateStructure (stateAssign p ρs))
        (listSup (((finEnum (Ph T Dm)).filter fun q => decide (Ph.IsUniv q)).map
          (atTagF L (repMerged X.pointBlock n) (Ph T Dm)))) := Iff.rfl
  rw [hrw, realize_listSup_atTagF, List.mem_filter]
  simp [mem_finEnum p]

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_isUniv)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- **The positions that win outright are the leaves whose kernel holds.** -/
theorem graphGame_isWon (p : Ph T Dm) (ρs : Fin n → X.pointBlock.Assignment A) :
    ((graphGame X hn D hD K).IsWon (stateAssign p ρs) ↔
      ∃ (s : Sub) (tx ty : T) (pol : Bool), p = .pre s tx ty ⟨0, Nat.succ_pos Dm⟩ pol ∧
        @Sentence.Realize _ A
          ((repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
            (repBlockAssign X.pointBlock A n ρs)) (K s tx ty)) := by
  let := stateStructure (X := X) (stateAssign p ρs)
  have hrw : (graphGame X hn D hD K).IsWon (stateAssign p ρs) ↔
      @Sentence.Realize _ A (stateStructure (stateAssign p ρs))
        (listSup ((finEnum (Sub × T × T × Bool)).map fun e =>
          atTagF L (repMerged X.pointBlock n) (Ph T Dm)
              (.pre e.1 e.2.1 e.2.2.1 ⟨0, Nat.succ_pos Dm⟩ e.2.2.2) ⊓
            (withTagLHom L (repMerged X.pointBlock n) (Ph T Dm)).onSentence
              (K e.1 e.2.1 e.2.2.1))) := Iff.rfl
  rw [hrw, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hψ
    obtain ⟨h1, h2⟩ := Formula.realize_inf.mp hr
    exact ⟨e.1, e.2.1, e.2.2.1, e.2.2.2, ((realize_atTagF _ p _).mp h1).symm,
      (realize_withTagLHom _ _).mp h2⟩
  · rintro ⟨s, tx, ty, pol, rfl, hK⟩
    refine ⟨_, List.mem_map.mpr ⟨(s, tx, ty, pol), mem_finEnum _, rfl⟩,
      Formula.realize_inf.mpr ⟨(realize_atTagF _ _ _).mpr rfl, ?_⟩⟩
    exact (realize_withTagLHom _ _).mpr hK

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_isWon)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- **The starting positions are the `startPick` states whose rounds are all
points.** -/
theorem graphGame_isStart (τ : (gameBlock X n T Dm).Assignment A) :
    ((graphGame X hn D hD K).IsStart τ ↔
      ∃ (tx : T) (pts : Fin n → X.Map A),
        τ = stateAssign (.startPick tx) fun i => pointAssign (pts i)) := by
  let := stateStructure (X := X) τ
  have hrw : (graphGame X hn D hD K).IsStart τ ↔
      @Sentence.Realize _ A (stateStructure τ)
        (listSup ((finEnum T).map fun tx =>
          atTagF L (repMerged X.pointBlock n) (Ph T Dm) (.startPick tx) ⊓
            (withTagLHom L (repMerged X.pointBlock n) (Ph T Dm)).onSentence
              (allRoundsPointF X n))) := Iff.rfl
  rw [hrw, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨tx, -, rfl⟩ := List.mem_map.mp hψ
    obtain ⟨h1, h2⟩ := Formula.realize_inf.mp hr
    have hτ := eq_tagAssign_of_atTagF (Ph.startPick tx) τ h1
    obtain ⟨ρs, hρs⟩ := repBlockAssign_split X.pointBlock A n (SOBlock.dropTag τ)
    have h3 : @Sentence.Realize _ A
        ((repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
          (repBlockAssign X.pointBlock A n ρs)) (allRoundsPointF X n) := by
      rw [← hρs]
      exact (realize_withTagLHom τ _).mp h2
    obtain ⟨pts, rfl⟩ := exists_points_of_allRoundsPoint ((realize_allRoundsPointF ρs).mp h3)
    exact ⟨tx, pts, hτ.trans (congrArg (SOBlock.tagAssign _) hρs)⟩
  · rintro ⟨tx, pts, rfl⟩
    refine ⟨_, List.mem_map.mpr ⟨tx, mem_finEnum tx, rfl⟩,
      Formula.realize_inf.mpr ⟨(realize_atTagF _ _ _).mpr rfl, ?_⟩⟩
    exact (realize_withTagLHom _ _).mpr
      ((realize_allRoundsPointF _).mpr fun i => isPointAssign_pointAssign _)

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_isStart)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- **The moves are the listed ones.** -/
theorem graphGame_move (p q : Ph T Dm) (ρs σs : Fin n → X.pointBlock.Assignment A) :
    ((graphGame X hn D hD K).Move (stateAssign p ρs) (stateAssign q σs) ↔
      ∃ m ∈ movesFrom hn D hD p, m.tgt = q ∧ (∀ e ∈ m.keep, ρs e.1 = σs e.2) ∧
        (∀ i ∈ m.guard, IsPointAssign (X := X) (σs i))) := by
  let := @Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
    (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) (stateAssign q σs)
  have hrw : (graphGame X hn D hD K).Move (stateAssign p ρs) (stateAssign q σs) ↔
      @Sentence.Realize _ A
        (@Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
          (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) (stateAssign q σs))
        (listSup ((finEnum (Ph T Dm)).flatMap fun p' =>
          (movesFrom hn D hD p').map (moveOf X p'))) := Iff.rfl
  rw [hrw, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨p', -, hmem⟩ := List.mem_flatMap.mp hψ
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hpp, h2, h3, h4⟩ := (realize_moveOf p' p q m ρs σs).mp hr
    subst hpp
    exact ⟨m, hm, h2, h3, h4⟩
  · rintro ⟨m, hm, h2, h3, h4⟩
    exact ⟨_, List.mem_flatMap.mpr ⟨p, mem_finEnum p, List.mem_map.mpr ⟨m, hm, rfl⟩⟩,
      (realize_moveOf p p q m ρs σs).mpr ⟨rfl, h2, h3, h4⟩⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_move)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

/-- **Every move lands on a state**: each disjunct pins the tag bits of the
state it enters, so a junk assignment is never reachable. -/
theorem graphGame_move_shape {p : Ph T Dm} {ρs : Fin n → X.pointBlock.Assignment A}
    {τ : (gameBlock X n T Dm).Assignment A}
    (h : (graphGame X hn D hD K).Move (stateAssign p ρs) τ) :
    ∃ (q : Ph T Dm) (σs : Fin n → X.pointBlock.Assignment A), τ = stateAssign q σs := by
  let := @Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
    (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) τ
  have hrw : (graphGame X hn D hD K).Move (stateAssign p ρs) τ ↔
      @Sentence.Realize _ A
        (@Lax134656.SecondOrderTransitiveClosure.SOBlock.structure₂ (L.sum Language.order) (gameBlock X n T Dm) A
          (@Lax904597.Interpretations.sumOrderStructure L A instL _) (stateAssign p ρs) τ)
        (listSup ((finEnum (Ph T Dm)).flatMap fun p' =>
          (movesFrom hn D hD p').map (moveOf X p'))) := Iff.rfl
  rw [hrw, Sentence.Realize, realize_listSup] at h
  obtain ⟨ψ, hψ, hr⟩ := h
  obtain ⟨p', -, hmem⟩ := List.mem_flatMap.mp hψ
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hmem
  rw [moveOf, Formula.realize_inf] at hr
  obtain ⟨-, hr2⟩ := hr
  obtain ⟨hr3, -⟩ := Formula.realize_inf.mp hr2
  have hτ := exists_tagAssign_two m.tgt (stateAssign p ρs) τ hr3
  obtain ⟨σs, hσs⟩ := repBlockAssign_split X.pointBlock A n (SOBlock.dropTag τ)
  exact ⟨m.tgt, σs, hτ.trans (congrArg (SOBlock.tagAssign _) hσs)⟩

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241.Expansions.ExpExpansion

export Lax480241Proofs.DescriptiveComplexity.ExpExpansion (graphGame_move_shape)

end Lax480241.Expansions.ExpExpansion

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : Lax480241.Expansions.ExpExpansion L) {T : Type} [Finite T] {d n Dm : ℕ}

variable {X} {A : Type} [instL : L.Structure A] [LinearOrder A]

variable {hn : n = 2 * d + Dm} {D : Sub → T → T → ℕ} {hD : ∀ s tx ty, D s tx ty ≤ Dm}

variable {K : ∀ (_s : Sub) (_tx _ty : T),
  ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}

end ExpExpansion

end Lax480241Proofs.DescriptiveComplexity


