/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Invariant.Bare
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

namespace Lax945089.PebbleGames
end Lax945089.PebbleGames

namespace Lax945089Proofs.DescriptiveComplexity.EquivK₂
end Lax945089Proofs.DescriptiveComplexity.EquivK₂

namespace Lax945089Proofs.DescriptiveComplexity
export Lax945089.PebbleGames (EquivK₂ PebbleBackForth₂ PebbleRel₂ atomicAgreeOn₂ pebbleRefine₂ pebbleStage₂)
end Lax945089Proofs.DescriptiveComplexity

/-!
# The `k`-pebble game between two structures

`DescriptiveComplexity.Invariant.Pebble` refines a relation between `k`-tuples
of *one* structure, which is all the Abiteboul–Vianu development needs: it
asks which tuples a definition can tell apart. Separating a *Boolean* query
needs the same game played across *two* structures, and that is what this file
builds – the same chain, the same coinduction, the same stabilization, with
the two sides now living in different types.

The pieces mirror their one-structure originals one for one:
`DescriptiveComplexity.EquivK₂` is the limit of
`DescriptiveComplexity.pebbleStage₂`, greatest by
`DescriptiveComplexity.le_equivK₂`, a fixed point on finite types
(`DescriptiveComplexity.equivK₂_iff`, whence the game moves
`DescriptiveComplexity.EquivK₂.update`), and unchanged by expanding both sides
with relations it already refines (`DescriptiveComplexity.equivK₂_inf_eq`) –
the lemma that carries invariance through the stages of an induction.

Instantiated at agreement on the atomic type
(`DescriptiveComplexity.atomicAgreeOn₂`) and at *bare* sets, it collapses:
`DescriptiveComplexity.equivK₂_bare` – over the empty vocabulary, `k`-tuples
of two sets with `k` elements each are equivalent as soon as they have the
same equality pattern, whatever the two sizes. That is the sentence-level
counterpart of `DescriptiveComplexity.equivK_bare`, and the reason a
`k`-variable induction cannot count.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The chain -/

variable {M N : Type} {k : ℕ}

theorem pebbleBackForth₂_mono {E E' : Lax945089.PebbleGames.PebbleRel₂ M N k} (h : E.Le E') :
    (Lax945089.PebbleGames.PebbleBackForth₂ E).Le (Lax945089.PebbleGames.PebbleBackForth₂ E') := by
  intro a b hab i
  exact ⟨fun c => (hab i).1 c |>.imp fun _ hd => h _ _ hd,
    fun d => (hab i).2 d |>.imp fun _ hc => h _ _ hc⟩

theorem pebbleRefine₂_mono (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) {E E' : Lax945089.PebbleGames.PebbleRel₂ M N k} (h : E.Le E') :
    (Lax945089.PebbleGames.pebbleRefine₂ E₀ E).Le (Lax945089.PebbleGames.pebbleRefine₂ E₀ E') :=
  fun a b hab => ⟨hab.1, pebbleBackForth₂_mono h a b hab.2⟩

variable {E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k}

theorem pebbleStage₂_succ_le (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) (n : ℕ) :
    (Lax945089.PebbleGames.pebbleStage₂ E₀ (n + 1)).Le (Lax945089.PebbleGames.pebbleStage₂ E₀ n) := by
  induction n with
  | zero => exact fun _ _ _ => trivial
  | succ n ih => exact pebbleRefine₂_mono E₀ ih

theorem pebbleStage₂_le_of_le (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) {m n : ℕ} (hmn : m ≤ n) :
    (Lax945089.PebbleGames.pebbleStage₂ E₀ n).Le (Lax945089.PebbleGames.pebbleStage₂ E₀ m) := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ h => h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact fun a b h => ih (Nat.lt_succ_iff.mp hlt) a b (pebbleStage₂_succ_le E₀ n a b h)
    · rw [heq]; exact fun _ _ h => h

/-- The limit is below the initial relation. -/
theorem EquivK₂.initial {a : Fin k → M} {b : Fin k → N} (h : Lax945089.PebbleGames.EquivK₂ E₀ a b) : E₀ a b :=
  (h 1).1

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.PebbleGames.EquivK₂

export Lax945089Proofs.DescriptiveComplexity.EquivK₂ (initial)

end Lax945089.PebbleGames.EquivK₂

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M N : Type} {k : ℕ}

variable {E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k}

/-- **Coinduction**: a relation below its own refinement is below the limit –
how a pair is ever proved equivalent. -/
theorem le_equivK₂ {E : Lax945089.PebbleGames.PebbleRel₂ M N k} (h : E.Le (Lax945089.PebbleGames.pebbleRefine₂ E₀ E)) :
    E.Le (Lax945089.PebbleGames.EquivK₂ E₀) := by
  intro a b hab n
  induction n generalizing a b with
  | zero => trivial
  | succ n ih => exact pebbleRefine₂_mono E₀ ih a b (h a b hab)

/-! ### Stabilization -/

section Finite

variable [Finite M] [Finite N]

theorem exists_pebbleStage₂_succ_eq (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) :
    ∃ n ≤ Nat.card ((Fin k → M) × (Fin k → N)),
      Lax945089.PebbleGames.pebbleStage₂ E₀ (n + 1) = Lax945089.PebbleGames.pebbleStage₂ E₀ n := by
  obtain ⟨n, hn, heq⟩ := exists_succ_eq_of_antitone_subset
    (c := fun n => {p : (Fin k → M) × (Fin k → N) | Lax945089.PebbleGames.pebbleStage₂ E₀ n p.1 p.2})
    (fun n p hp => pebbleStage₂_succ_le E₀ n p.1 p.2 hp)
  refine ⟨n, hn, ?_⟩
  funext a b
  exact propext ⟨fun h => (Set.ext_iff.mp heq (a, b)).mp h,
    fun h => (Set.ext_iff.mp heq (a, b)).mpr h⟩

omit [Finite M] [Finite N] in
private theorem pebbleStage₂_eq_of_succ_eq {n : ℕ}
    (hn : Lax945089.PebbleGames.pebbleStage₂ E₀ (n + 1) = Lax945089.PebbleGames.pebbleStage₂ E₀ n) {m : ℕ} (hm : n ≤ m) :
    Lax945089.PebbleGames.pebbleStage₂ E₀ m = Lax945089.PebbleGames.pebbleStage₂ E₀ n := by
  induction m with
  | zero => rw [Nat.le_zero.mp hm]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · have hm' : Lax945089.PebbleGames.pebbleStage₂ E₀ m = Lax945089.PebbleGames.pebbleStage₂ E₀ n := ih (by omega)
      calc Lax945089.PebbleGames.pebbleStage₂ E₀ (m + 1) = Lax945089.PebbleGames.pebbleRefine₂ E₀ (Lax945089.PebbleGames.pebbleStage₂ E₀ m) := rfl
        _ = Lax945089.PebbleGames.pebbleRefine₂ E₀ (Lax945089.PebbleGames.pebbleStage₂ E₀ n) := by rw [hm']
        _ = Lax945089.PebbleGames.pebbleStage₂ E₀ n := hn
    · rw [le_antisymm hm h]

/-- **On finite structures the limit is a fixed point of the refinement.** -/
theorem pebbleRefine₂_equivK₂ (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) :
    Lax945089.PebbleGames.pebbleRefine₂ E₀ (Lax945089.PebbleGames.EquivK₂ E₀) = Lax945089.PebbleGames.EquivK₂ E₀ := by
  obtain ⟨n, -, hn⟩ := exists_pebbleStage₂_succ_eq E₀
  have hlim : Lax945089.PebbleGames.EquivK₂ E₀ = Lax945089.PebbleGames.pebbleStage₂ E₀ n := by
    funext a b
    refine propext ⟨fun h => h n, fun h m => ?_⟩
    rcases Nat.le_total m n with hmn | hmn
    · exact pebbleStage₂_le_of_le E₀ hmn a b h
    · rw [pebbleStage₂_eq_of_succ_eq hn hmn]; exact h
  rw [hlim]
  exact hn

/-- The interface characterization: consumers use this, never the stages. -/
theorem equivK₂_iff (E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k) (a : Fin k → M) (b : Fin k → N) :
    Lax945089.PebbleGames.EquivK₂ E₀ a b ↔ E₀ a b ∧ Lax945089.PebbleGames.PebbleBackForth₂ (Lax945089.PebbleGames.EquivK₂ E₀) a b := by
  conv_lhs => rw [← pebbleRefine₂_equivK₂ E₀]
  exact Iff.rfl

/-- **The game move**, from the left. -/
theorem EquivK₂.update {a : Fin k → M} {b : Fin k → N} (h : Lax945089.PebbleGames.EquivK₂ E₀ a b) (i : Fin k) (c : M) :
    ∃ d : N, Lax945089.PebbleGames.EquivK₂ E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK₂_iff E₀ a b).mp h).2 i).1 c

end Finite

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.PebbleGames.EquivK₂

export Lax945089Proofs.DescriptiveComplexity.EquivK₂ (update)

end Lax945089.PebbleGames.EquivK₂

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M N : Type} {k : ℕ}

variable {E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k}

section Finite

variable [Finite M] [Finite N]

/-- **The game move**, from the right. -/
theorem EquivK₂.update_right {a : Fin k → M} {b : Fin k → N} (h : Lax945089.PebbleGames.EquivK₂ E₀ a b) (i : Fin k)
    (d : N) : ∃ c : M, Lax945089.PebbleGames.EquivK₂ E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK₂_iff E₀ a b).mp h).2 i).2 d

end Finite

end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089.PebbleGames.EquivK₂

export Lax945089Proofs.DescriptiveComplexity.EquivK₂ (update_right)

end Lax945089.PebbleGames.EquivK₂

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {M N : Type} {k : ℕ}

variable {E₀ : Lax945089.PebbleGames.PebbleRel₂ M N k}

section Finite

variable [Finite M] [Finite N]

end Finite

/-! ### Monotonicity and expansion -/

theorem pebbleStage₂_mono {E₀ E₀' : Lax945089.PebbleGames.PebbleRel₂ M N k} (h : E₀'.Le E₀) (n : ℕ) :
    (Lax945089.PebbleGames.pebbleStage₂ E₀' n).Le (Lax945089.PebbleGames.pebbleStage₂ E₀ n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun a b hab => ⟨h a b hab.1, pebbleBackForth₂_mono ih a b hab.2⟩

theorem equivK₂_mono {E₀ E₀' : Lax945089.PebbleGames.PebbleRel₂ M N k} (h : E₀'.Le E₀) :
    (Lax945089.PebbleGames.EquivK₂ E₀').Le (Lax945089.PebbleGames.EquivK₂ E₀) :=
  fun a b hab n => pebbleStage₂_mono h n a b (hab n)

/-- **The expansion lemma**: refining the initial relation by anything the
limit already refines does not change the limit – so expanding both structures
by relations the equivalence cannot see leaves it alone. -/
theorem equivK₂_inf_eq [Finite M] [Finite N] {E₀ E₀' : Lax945089.PebbleGames.PebbleRel₂ M N k} (hle : E₀'.Le E₀)
    (hinv : (Lax945089.PebbleGames.EquivK₂ E₀).Le E₀') : Lax945089.PebbleGames.EquivK₂ E₀' = Lax945089.PebbleGames.EquivK₂ E₀ := by
  funext a b
  refine propext ⟨fun h => equivK₂_mono hle a b h, fun h => ?_⟩
  refine le_equivK₂ (E₀ := E₀') (E := Lax945089.PebbleGames.EquivK₂ E₀) (fun a b hab => ?_) a b h
  exact ⟨hinv a b hab, ((equivK₂_iff E₀ a b).mp hab).2⟩

/-! ### Agreement on the atomic type, across two structures -/

variable {L : Language.{0, 0}}

/-! ### The bare case -/

/-- **Two bare sets with `k` elements each are indistinguishable by `k`
pebbles**: over the empty vocabulary, tuples with the same equality pattern
are `≡ᵏ`-equivalent *across* the two sets, however far apart their sizes. The
strategy is the one of `DescriptiveComplexity.exists_update_pattern`, played
on both sides at once. -/
theorem equivK₂_bare [Language.empty.Structure M] [Language.empty.Structure N]
    [Finite M] [Finite N] {S : Set (Σ n, Language.empty.Relations n)}
    (hM : k ≤ Nat.card M) (hN : k ≤ Nat.card N) {v : Fin k → M} {w : Fin k → N}
    (hpat : ∀ p q, v p = v q ↔ w p = w q) :
    Lax945089.PebbleGames.EquivK₂ (Lax945089.PebbleGames.atomicAgreeOn₂ S M N k) v w := by
  refine le_equivK₂ (E := fun v w => ∀ p q, v p = v q ↔ w p = w q) ?_ v w hpat
  intro v w hvw
  refine ⟨⟨hvw, ?_⟩, fun i => ⟨fun c => ?_, fun d => ?_⟩⟩
  · intro l R _ _
    exact (R : Empty).elim
  · -- the spoiler plays on the left: answer by the matching repetition, or fresh
    classical
    by_cases hc : ∃ j, j ≠ i ∧ v j = c
    · obtain ⟨j₀, -, hvj₀⟩ := hc
      refine ⟨w j₀, update_pattern hvw i fun j _ => ?_⟩
      rw [← hvj₀]
      exact hvw j j₀
    · have hc' : ∀ j, j ≠ i → v j ≠ c := fun j hj hvj => hc ⟨j, hj, hvj⟩
      obtain ⟨d, hd⟩ := exists_notMem_image_erase w i hN
      exact ⟨d, update_pattern hvw i fun j hj => iff_of_false (hc' j hj) (hd j hj)⟩
  · -- and on the right
    classical
    by_cases hd : ∃ j, j ≠ i ∧ w j = d
    · obtain ⟨j₀, -, hwj₀⟩ := hd
      refine ⟨v j₀, update_pattern hvw i fun j _ => ?_⟩
      rw [← hwj₀]
      exact hvw j j₀
    · have hd' : ∀ j, j ≠ i → w j ≠ d := fun j hj hwj => hd ⟨j, hj, hwj⟩
      obtain ⟨c, hc⟩ := exists_notMem_image_erase v i hM
      exact ⟨c, update_pattern hvw i fun j hj => iff_of_false (hc j hj) (hd' j hj)⟩

end Lax945089Proofs.DescriptiveComplexity


