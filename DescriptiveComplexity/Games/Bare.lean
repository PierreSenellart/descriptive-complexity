/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FirstOrderDefinable
import DescriptiveComplexity.Games.Ehrenfeucht

/-!
# The game on bare sets

The duplicator's strategy on structures over the *empty* vocabulary – bare
finite sets, the simplest structures there are. A position is legal there as
soon as the two tuples have the same equality pattern
(`DescriptiveComplexity.partialIso_bare`: there is no relation to check), and
the strategy is the obvious one: answer a repetition by the matching
repetition, a fresh element by a fresh element. Fresh elements last as long as
the sets do, so `DescriptiveComplexity.efEquiv_bare` – two bare sets with at
least `n` elements each are `n`-round equivalent, *whatever their sizes*.

By the methodology lemma (`DescriptiveComplexity.realize_sentence_of_efEquiv`)
first-order logic therefore cannot compare the sizes of two bare sets beyond
its quantifier rank: it counts up to a constant and no further. That is the
whole content of the inexpressibility of `DescriptiveComplexity.EVEN`
(`DescriptiveComplexity.Problems.Even`), and the reason the same problem must
be attacked with a much finer game once a linear order is available.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### Fresh elements -/

/-- A tuple shorter than the finite set it lives in misses an element. -/
theorem exists_notMem_range {N : Type} [Finite N] {j : ℕ} (b : Fin j → N)
    (h : j < Nat.card N) : ∃ d : N, ∀ i, b i ≠ d := by
  classical
  let := Fintype.ofFinite N
  have hcard : (Finset.image b Finset.univ).card < (Finset.univ : Finset N).card := by
    calc (Finset.image b Finset.univ).card
        ≤ (Finset.univ : Finset (Fin j)).card := Finset.card_image_le
      _ = j := by simp
      _ < Nat.card N := h
      _ = (Finset.univ : Finset N).card := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨d, fun i heq => hd (heq ▸ Finset.mem_image_of_mem b (Finset.mem_univ i))⟩

/-! ### Extending a position -/

/-- Extending two tuples with the same equality pattern by a matching pair of
elements – matching in the sense that each coordinate hits the new element on
the left exactly when it does on the right – preserves the pattern. -/
theorem snoc_pattern {M N : Type} {j : ℕ} {a : Fin j → M} {b : Fin j → N} {c : M} {d : N}
    (hpat : ∀ i i', a i = a i' ↔ b i = b i') (hc : ∀ i, a i = c ↔ b i = d) :
    ∀ i i' : Fin (j + 1),
      (Fin.snoc a c : Fin (j + 1) → M) i = (Fin.snoc a c : Fin (j + 1) → M) i' ↔
        (Fin.snoc b d : Fin (j + 1) → N) i = (Fin.snoc b d : Fin (j + 1) → N) i' := by
  intro i i'
  induction i using Fin.lastCases with
  | last =>
    induction i' using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_last]
      exact iff_of_true rfl rfl
    | cast q =>
      rw [Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
      exact ⟨fun h => ((hc q).mp h.symm).symm, fun h => ((hc q).mpr h.symm).symm⟩
  | cast q =>
    induction i' using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
      exact hc q
    | cast q' =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hpat q q'

/-! ### The strategy -/

variable {M N : Type} [Language.empty.Structure M] [Language.empty.Structure N]

/-- Over the empty vocabulary a position is legal as soon as the two tuples
have the same equality pattern: there is no relation to check. -/
theorem partialIso_bare {j : ℕ} {a : Fin j → M} {b : Fin j → N}
    (hpat : ∀ i i', a i = a i' ↔ b i = b i') : PartialIso Language.empty a b :=
  ⟨hpat, fun _ R _ => (R : Empty).elim⟩

variable [Finite M] [Finite N]

/-- **The duplicator's strategy on bare sets**: from a position whose tuples
have the same equality pattern, the duplicator survives as many rounds as
either set has elements to spare. A repetition is answered by the matching
repetition, a fresh element by a fresh element
(`DescriptiveComplexity.exists_notMem_range`), which is where the budget is
spent. -/
theorem efStage_bare : ∀ (n : ℕ) {j : ℕ} (a : Fin j → M) (b : Fin j → N),
    (∀ i i', a i = a i' ↔ b i = b i') → n + j ≤ Nat.card M → n + j ≤ Nat.card N →
    efStage Language.empty n a b := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ hpat _ _
    exact partialIso_bare hpat
  | succ n ih =>
    intro j a b hpat hM hN
    refine ⟨partialIso_bare hpat, fun c => ?_, fun d => ?_⟩
    · by_cases hc : ∃ i, a i = c
      · obtain ⟨i₀, hi₀⟩ := hc
        refine ⟨b i₀, ih _ _ (snoc_pattern hpat fun i => by rw [← hi₀]; exact hpat i i₀)
          (by omega) (by omega)⟩
      · have hc : ∀ i, a i ≠ c := not_exists.mp hc
        obtain ⟨d, hd⟩ := exists_notMem_range b (by omega)
        exact ⟨d, ih _ _ (snoc_pattern hpat fun i => iff_of_false (hc i) (hd i))
          (by omega) (by omega)⟩
    · by_cases hd : ∃ i, b i = d
      · obtain ⟨i₀, hi₀⟩ := hd
        refine ⟨a i₀, ih _ _ (snoc_pattern hpat fun i => by rw [← hi₀]; exact hpat i i₀)
          (by omega) (by omega)⟩
      · have hd : ∀ i, b i ≠ d := not_exists.mp hd
        obtain ⟨c, hc⟩ := exists_notMem_range a (by omega)
        exact ⟨c, ih _ _ (snoc_pattern hpat fun i => iff_of_false (hc i) (hd i))
          (by omega) (by omega)⟩

/-- **Two bare sets with at least `n` elements each are `n`-round
equivalent** – however different their sizes. -/
theorem efEquiv_bare (n : ℕ) (hM : n ≤ Nat.card M) (hN : n ≤ Nat.card N) :
    EFEquiv Language.empty M N n :=
  efStage_bare n default default (fun i => i.elim0) (by simpa using hM) (by simpa using hN)

/-! ### What first-order logic can say about a bare set -/

/-- **First-order logic counts up to a constant**: an order-free first-order
definable property of bare sets has a threshold beyond which it no longer
depends on the size of the set. The threshold is the quantifier rank of a
defining sentence – one round of the game per quantifier
(`DescriptiveComplexity.efEquiv_bare`,
`DescriptiveComplexity.realize_sentence_of_efEquiv`).

Every inexpressibility result over the empty vocabulary is an instance:
exhibit two large sets of different sizes the problem separates. -/
theorem exists_card_bound_of_foDefinableFree {P : DecisionProblem Language.empty}
    (h : FODefinableFree P) :
    ∃ N : ℕ, ∀ (A B : Type) [Language.empty.Structure A] [Language.empty.Structure B],
      ∀ [Finite A] [Finite B] [Nonempty A] [Nonempty B],
        N ≤ Nat.card A → N ≤ Nat.card B → (P A ↔ P B) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨qdepth φ, fun A B _ _ _ _ _ _ hA hB => ?_⟩
  rw [hφ A, hφ B]
  exact realize_sentence_of_efEquiv (efEquiv_bare _ hA hB) φ le_rfl

end DescriptiveComplexity
