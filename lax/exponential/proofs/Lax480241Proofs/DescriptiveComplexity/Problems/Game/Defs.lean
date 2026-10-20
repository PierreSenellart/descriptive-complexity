/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Vocabulary
import Lax480241Proofs.DescriptiveComplexity.Interpretation
import Lax480241Proofs.DescriptiveComplexity.Problems.Reachability
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

namespace Lax480241Proofs.Foreign.FirstOrder.Language
end Lax480241Proofs.Foreign.FirstOrder.Language

namespace Lax535992.Game
end Lax535992.Game

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.Game (AGMove AGStart AGUniv AGWon GameWon WinsOn)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax535992.Game (agMove agStart agUniv agWon andOrGraph)
end FirstOrder.Language

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

`DescriptiveComplexity.WinsOn` is an inductive predicate, i.e., the least fixed
point of the game operator, so an infinite play is a loss for the existential
player. That is also the presentation the FO(LFP) membership proof mirrors
clause by clause – with one twist, since a Horn rule cannot carry a universally
quantified body atom; see `DescriptiveComplexity.Problems.Game.Membership`.
-/

namespace FirstOrder

namespace Language

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The move symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.agMoveO : (Lax535992.Game.andOrGraph.sum Language.order).Relations 2 := Sum.inl Lax535992.Game.agMove

export Lax480241Proofs.Foreign.FirstOrder.Language (agMoveO)

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The universal-player symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.agUnivO : (Lax535992.Game.andOrGraph.sum Language.order).Relations 1 := Sum.inl Lax535992.Game.agUniv

export Lax480241Proofs.Foreign.FirstOrder.Language (agUnivO)

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The marked-start symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.agStartO : (Lax535992.Game.andOrGraph.sum Language.order).Relations 1 := Sum.inl Lax535992.Game.agStart

export Lax480241Proofs.Foreign.FirstOrder.Language (agStartO)

open Lax480241Proofs.Foreign.FirstOrder.Language in
/-- The won-outright symbol in the ordered expansion. -/
abbrev _root_.Lax480241Proofs.Foreign.FirstOrder.Language.agWonO : (Lax535992.Game.andOrGraph.sum Language.order).Relations 1 := Sum.inl Lax535992.Game.agWon

export Lax480241Proofs.Foreign.FirstOrder.Language (agWonO)

end Language

end FirstOrder

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The semantics -/

section Defs

variable {A : Type} [Lax535992.Game.andOrGraph.Structure A]

end Defs

/-! ### Without the universal player, the game is reachability -/

section Collapse

end Collapse

/-! ### Isomorphism-invariance -/

section Iso

variable {A B : Type} [Lax535992.Game.andOrGraph.Structure A] [Lax535992.Game.andOrGraph.Structure B]

private theorem agMove_map (e : A ≃[Lax535992.Game.andOrGraph] B) (a b : A) :
    Lax535992.Game.AGMove a b ↔ Lax535992.Game.AGMove (e a) (e b) :=
  relMap_equiv₂ e Lax535992.Game.agMove a b

private theorem winsOn_of_iso (e : A ≃[Lax535992.Game.andOrGraph] B) {a : A} (h : Lax535992.Game.WinsOn A a) :
    Lax535992.Game.WinsOn B (e a) := by
  induction h with
  | won hw => exact .won ((relMap_equiv₁ e Lax535992.Game.agWon _).mp hw)
  | @ex a b hu hm _ ih =>
    exact .ex (fun hc => hu ((relMap_equiv₁ e Lax535992.Game.agUniv a).mpr hc)) ((agMove_map e a b).mp hm) ih
  | @all a hu hex _ ih =>
    refine .all ((relMap_equiv₁ e Lax535992.Game.agUniv a).mp hu) ?_ ?_
    · obtain ⟨b, hb⟩ := hex
      exact ⟨e b, (agMove_map e a b).mp hb⟩
    · intro b hb
      obtain ⟨b₀, rfl⟩ : ∃ b₀ : A, e b₀ = b := ⟨e.symm b, e.toEquiv.apply_symm_apply b⟩
      exact ih b₀ ((agMove_map e a b₀).mpr hb)

private theorem gameWon_of_iso (e : A ≃[Lax535992.Game.andOrGraph] B) (h : Lax535992.Game.GameWon A) : Lax535992.Game.GameWon B := by
  obtain ⟨s, hs, hw⟩ := h
  exact ⟨e s, (relMap_equiv₁ e Lax535992.Game.agStart s).mp hs, winsOn_of_iso e hw⟩

/-- Being won is isomorphism-invariant. -/
theorem gameWon_iso (e : A ≃[Lax535992.Game.andOrGraph] B) : Lax535992.Game.GameWon A ↔ Lax535992.Game.GameWon B :=
  ⟨gameWon_of_iso e, gameWon_of_iso e.symm⟩

end Iso

/-- **GAME**, alternating reachability: is some marked starting position of the
AND/OR graph winning? -/
def GAME : Lax904597.Problems.DecisionProblem Lax535992.Game.andOrGraph where
  Holds := fun A inst => @Lax535992.Game.GameWon A inst
  iso_invariant := fun e => gameWon_iso e

@[simp]
theorem game_holds_iff (A : Type) [Lax535992.Game.andOrGraph.Structure A] :
    GAME A ↔ Lax535992.Game.GameWon A :=
  Iff.rfl

end Lax480241Proofs.DescriptiveComplexity


