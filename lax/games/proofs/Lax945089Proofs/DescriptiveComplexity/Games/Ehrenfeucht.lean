/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Invariant.EquivK
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax945089.EhrenfeuchtGames
end Lax945089.EhrenfeuchtGames

namespace Lax945089Proofs.DescriptiveComplexity.EFEquiv
end Lax945089Proofs.DescriptiveComplexity.EFEquiv

namespace Lax945089Proofs.DescriptiveComplexity.PartialIso
end Lax945089Proofs.DescriptiveComplexity.PartialIso

namespace Lax945089Proofs.DescriptiveComplexity.efStage
end Lax945089Proofs.DescriptiveComplexity.efStage

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.EhrenfeuchtGames (EFEquiv PartialIso efStage qdepth)
end Lax945089Proofs.DescriptiveComplexity

/-!
# Ehrenfeucht–Fraïssé games on finite structures

The graded back-and-forth refinement between *two* structures
([Ehrenfeucht 1961][ehrenfeucht1961application];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 2), and the one lemma the
whole inexpressibility toolkit rests on: surviving `n` rounds implies agreeing
on every sentence of quantifier rank at most `n`
(`DescriptiveComplexity.realize_efStage`), so a property distinguishing two
structures the duplicator can play forever is not first-order.

A position (`DescriptiveComplexity.PartialIso`) is a pair of tuples of equal
length, one on each side, satisfying the same equalities between coordinates
and the same base relations at every selection of coordinates – agreement on
the atomic type (`DescriptiveComplexity.atomicAgreeOn`) read across two
structures. A round appends one element, chosen on either side by the spoiler
and answered on the other by the duplicator, and
`DescriptiveComplexity.efStage L n` is the set of positions from which the
duplicator survives `n` of them.

The stages are *not* an instance of the abstract pebble refinement
(`DescriptiveComplexity.Invariant.Pebble`), although the two chains look
alike: there the two tuples live in the same structure and a round *replaces*
one of `k` fixed pebbles, here they live in two different structures – the
spoiler's move is a quantifier over one of them, the duplicator's answer a
quantifier over the other – and a round *appends* a coordinate, so a position
is not a point of a fixed relation but of a family indexed by the number of
rounds already played. What the two do share is the measure they are graded
by, `DescriptiveComplexity.qdepth`, and the shape of the proof: the atomic
case is settled by the position, the quantifier case by one round of the game.
The vocabulary is relational, as everywhere in this library, so that atomic
formulas read coordinates rather than terms
(`DescriptiveComplexity.exists_eq_var_of_isRelational`).
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

/-! ### Positions -/

/-! ### The refinement chain -/

variable {n j : ℕ} {a : Fin j → M} {b : Fin j → N}

/-- A position from which the duplicator survives any number of rounds is
legal. -/
theorem efStage.partialIso : ∀ {n : ℕ}, Lax945089.EhrenfeuchtGames.efStage L n a b → Lax945089.EhrenfeuchtGames.PartialIso L a b
  | 0, h => h
  | _ + 1, h => h.1

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.EhrenfeuchtGames.efStage

export Lax945089Proofs.DescriptiveComplexity.efStage (partialIso)

end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

variable {n j : ℕ} {a : Fin j → M} {b : Fin j → N}

/-- **The spoiler moves on the left**: from a position surviving `n + 1`
rounds, an element appended on the left is answered on the right. -/
theorem efStage.forth (h : Lax945089.EhrenfeuchtGames.efStage L (n + 1) a b) (c : M) :
    ∃ d : N, Lax945089.EhrenfeuchtGames.efStage L n (Fin.snoc a c) (Fin.snoc b d) :=
  h.2.1 c

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.EhrenfeuchtGames.efStage

export Lax945089Proofs.DescriptiveComplexity.efStage (forth)

end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

variable {n j : ℕ} {a : Fin j → M} {b : Fin j → N}

/-- **The spoiler moves on the right**: from a position surviving `n + 1`
rounds, an element appended on the right is answered on the left. -/
theorem efStage.back (h : Lax945089.EhrenfeuchtGames.efStage L (n + 1) a b) (d : N) :
    ∃ c : M, Lax945089.EhrenfeuchtGames.efStage L n (Fin.snoc a c) (Fin.snoc b d) :=
  h.2.2 d

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.EhrenfeuchtGames.efStage

export Lax945089Proofs.DescriptiveComplexity.efStage (back)

end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

variable {n j : ℕ} {a : Fin j → M} {b : Fin j → N}

/-! ### `n`-round equivalence of structures -/

/-! ### The methodology lemma -/

section Relational

variable [L.IsRelational]

/-- **The Ehrenfeucht–Fraïssé method.** A formula whose quantifier rank fits
in the duplicator's remaining budget cannot separate the two sides of a
position: each quantifier spends one round of the game, and atomic formulas
are decided by the position itself.

The free-variable context is empty (`Empty`): the tuples of the position play
the role of the free variables, exactly as the bound variables of Mathlib's
`FirstOrder.Language.BoundedFormula` are read off the valuation tuple. -/
theorem realize_efStage : ∀ {j : ℕ} (φ : L.BoundedFormula Empty j) {n : ℕ}, Lax945089.EhrenfeuchtGames.qdepth φ ≤ n →
    ∀ {a : Fin j → M} {b : Fin j → N}, Lax945089.EhrenfeuchtGames.efStage L n a b →
      (φ.Realize default a ↔ φ.Realize default b) := by
  intro j φ
  induction φ with
  | falsum =>
    intro _ _ _ _ _
    exact Iff.rfl
  | @equal n t₁ t₂ =>
    intro _ _ a b h
    obtain ⟨x₁, rfl⟩ := exists_eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := exists_eq_var_of_isRelational t₂
    rcases x₁ with e | i₁
    · exact e.elim
    rcases x₂ with e | i₂
    · exact e.elim
    exact h.partialIso.1 i₁ i₂
  | @rel n l R ts =>
    intro _ _ a b h
    have hts : ∀ p, ∃ i : Fin n, ts p = Term.var (Sum.inr i) := by
      intro p
      obtain ⟨x, hx⟩ := exists_eq_var_of_isRelational (ts p)
      rcases x with e | i
      · exact e.elim
      · exact ⟨i, hx⟩
    choose g hg using hts
    have hsub : ts = fun p => Term.var (Sum.inr (g p)) := funext hg
    subst hsub
    exact h.partialIso.2 l R g
  | @imp n f₁ f₂ ih₁ ih₂ =>
    intro m hm a b h
    simp only [Lax945089.EhrenfeuchtGames.qdepth] at hm
    exact imp_congr (ih₁ (le_trans (le_max_left _ _) hm) h)
      (ih₂ (le_trans (le_max_right _ _) hm) h)
  | @all n ψ ih =>
    intro m hm a b h
    simp only [Lax945089.EhrenfeuchtGames.qdepth] at hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hψ : Lax945089.EhrenfeuchtGames.qdepth ψ ≤ m := by omega
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    constructor
    · intro hall d
      obtain ⟨c, hc⟩ := h.back d
      exact (ih hψ hc).mp (hall c)
    · intro hall c
      obtain ⟨d, hd⟩ := h.forth c
      exact (ih hψ hd).mpr (hall d)

/-- **The methodology lemma**: `n`-round equivalent structures satisfy the
same sentences of quantifier rank at most `n`. Everything the inexpressibility
toolkit proves is a contrapositive of this. -/
theorem realize_sentence_of_efEquiv (h : Lax945089.EhrenfeuchtGames.EFEquiv L M N n) (φ : L.Sentence)
    (hφ : Lax945089.EhrenfeuchtGames.qdepth φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  realize_efStage φ hφ h

end Relational

end Lax945089Proofs.DescriptiveComplexity


