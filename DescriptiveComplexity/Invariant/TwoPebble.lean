/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Bare

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The chain -/

/-- A relation between `k`-tuples of two types: the positions of the
two-structure `k`-pebble game. -/
abbrev PebbleRel₂ (M N : Type) (k : ℕ) : Type :=
  (Fin k → M) → (Fin k → N) → Prop

variable {M N : Type} {k : ℕ}

/-- Pointwise implication of two-structure relations. -/
def PebbleRel₂.Le (E E' : PebbleRel₂ M N k) : Prop :=
  ∀ a b, E a b → E' a b

/-- The back-and-forth condition of the two-structure `k`-pebble game: the
pebble the spoiler moves, on either structure, can be answered on the other. -/
def PebbleBackForth₂ (E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => ∀ i : Fin k,
    (∀ c : M, ∃ d : N, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : N, ∃ c : M, E (Function.update a i c) (Function.update b i d))

/-- One round of refinement. -/
def pebbleRefine₂ (E₀ E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => E₀ a b ∧ PebbleBackForth₂ E a b

theorem pebbleBackForth₂_mono {E E' : PebbleRel₂ M N k} (h : E.Le E') :
    (PebbleBackForth₂ E).Le (PebbleBackForth₂ E') := by
  intro a b hab i
  exact ⟨fun c => (hab i).1 c |>.imp fun _ hd => h _ _ hd,
    fun d => (hab i).2 d |>.imp fun _ hc => h _ _ hc⟩

theorem pebbleRefine₂_mono (E₀ : PebbleRel₂ M N k) {E E' : PebbleRel₂ M N k} (h : E.Le E') :
    (pebbleRefine₂ E₀ E).Le (pebbleRefine₂ E₀ E') :=
  fun a b hab => ⟨hab.1, pebbleBackForth₂_mono h a b hab.2⟩

/-- The descending refinement chain. -/
def pebbleStage₂ (E₀ : PebbleRel₂ M N k) : ℕ → PebbleRel₂ M N k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine₂ E₀ (pebbleStage₂ E₀ n)

/-- **`k`-pebble equivalence between two structures**: the limit of the
refinement chain. -/
def EquivK₂ (E₀ : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => ∀ n, pebbleStage₂ E₀ n a b

variable {E₀ : PebbleRel₂ M N k}

theorem pebbleStage₂_succ_le (E₀ : PebbleRel₂ M N k) (n : ℕ) :
    (pebbleStage₂ E₀ (n + 1)).Le (pebbleStage₂ E₀ n) := by
  induction n with
  | zero => exact fun _ _ _ => trivial
  | succ n ih => exact pebbleRefine₂_mono E₀ ih

theorem pebbleStage₂_le_of_le (E₀ : PebbleRel₂ M N k) {m n : ℕ} (hmn : m ≤ n) :
    (pebbleStage₂ E₀ n).Le (pebbleStage₂ E₀ m) := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ h => h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact fun a b h => ih (Nat.lt_succ_iff.mp hlt) a b (pebbleStage₂_succ_le E₀ n a b h)
    · rw [heq]; exact fun _ _ h => h

/-- The limit is below the initial relation. -/
theorem EquivK₂.initial {a : Fin k → M} {b : Fin k → N} (h : EquivK₂ E₀ a b) : E₀ a b :=
  (h 1).1

/-- **Coinduction**: a relation below its own refinement is below the limit –
how a pair is ever proved equivalent. -/
theorem le_equivK₂ {E : PebbleRel₂ M N k} (h : E.Le (pebbleRefine₂ E₀ E)) :
    E.Le (EquivK₂ E₀) := by
  intro a b hab n
  induction n generalizing a b with
  | zero => trivial
  | succ n ih => exact pebbleRefine₂_mono E₀ ih a b (h a b hab)

/-! ### Stabilization -/

section Finite

variable [Finite M] [Finite N]

theorem exists_pebbleStage₂_succ_eq (E₀ : PebbleRel₂ M N k) :
    ∃ n ≤ Nat.card ((Fin k → M) × (Fin k → N)),
      pebbleStage₂ E₀ (n + 1) = pebbleStage₂ E₀ n := by
  obtain ⟨n, hn, heq⟩ := exists_succ_eq_of_antitone_subset
    (c := fun n => {p : (Fin k → M) × (Fin k → N) | pebbleStage₂ E₀ n p.1 p.2})
    (fun n p hp => pebbleStage₂_succ_le E₀ n p.1 p.2 hp)
  refine ⟨n, hn, ?_⟩
  funext a b
  exact propext ⟨fun h => (Set.ext_iff.mp heq (a, b)).mp h,
    fun h => (Set.ext_iff.mp heq (a, b)).mpr h⟩

omit [Finite M] [Finite N] in
private theorem pebbleStage₂_eq_of_succ_eq {n : ℕ}
    (hn : pebbleStage₂ E₀ (n + 1) = pebbleStage₂ E₀ n) {m : ℕ} (hm : n ≤ m) :
    pebbleStage₂ E₀ m = pebbleStage₂ E₀ n := by
  induction m with
  | zero => rw [Nat.le_zero.mp hm]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · have hm' : pebbleStage₂ E₀ m = pebbleStage₂ E₀ n := ih (by omega)
      calc pebbleStage₂ E₀ (m + 1) = pebbleRefine₂ E₀ (pebbleStage₂ E₀ m) := rfl
        _ = pebbleRefine₂ E₀ (pebbleStage₂ E₀ n) := by rw [hm']
        _ = pebbleStage₂ E₀ n := hn
    · rw [le_antisymm hm h]

/-- **On finite structures the limit is a fixed point of the refinement.** -/
theorem pebbleRefine₂_equivK₂ (E₀ : PebbleRel₂ M N k) :
    pebbleRefine₂ E₀ (EquivK₂ E₀) = EquivK₂ E₀ := by
  obtain ⟨n, -, hn⟩ := exists_pebbleStage₂_succ_eq E₀
  have hlim : EquivK₂ E₀ = pebbleStage₂ E₀ n := by
    funext a b
    refine propext ⟨fun h => h n, fun h m => ?_⟩
    rcases Nat.le_total m n with hmn | hmn
    · exact pebbleStage₂_le_of_le E₀ hmn a b h
    · rw [pebbleStage₂_eq_of_succ_eq hn hmn]; exact h
  rw [hlim]
  exact hn

/-- The interface characterization: consumers use this, never the stages. -/
theorem equivK₂_iff (E₀ : PebbleRel₂ M N k) (a : Fin k → M) (b : Fin k → N) :
    EquivK₂ E₀ a b ↔ E₀ a b ∧ PebbleBackForth₂ (EquivK₂ E₀) a b := by
  conv_lhs => rw [← pebbleRefine₂_equivK₂ E₀]
  exact Iff.rfl

/-- **The game move**, from the left. -/
theorem EquivK₂.update {a : Fin k → M} {b : Fin k → N} (h : EquivK₂ E₀ a b) (i : Fin k) (c : M) :
    ∃ d : N, EquivK₂ E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK₂_iff E₀ a b).mp h).2 i).1 c

/-- **The game move**, from the right. -/
theorem EquivK₂.update_right {a : Fin k → M} {b : Fin k → N} (h : EquivK₂ E₀ a b) (i : Fin k)
    (d : N) : ∃ c : M, EquivK₂ E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK₂_iff E₀ a b).mp h).2 i).2 d

end Finite

/-! ### Monotonicity and expansion -/

theorem pebbleStage₂_mono {E₀ E₀' : PebbleRel₂ M N k} (h : E₀'.Le E₀) (n : ℕ) :
    (pebbleStage₂ E₀' n).Le (pebbleStage₂ E₀ n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun a b hab => ⟨h a b hab.1, pebbleBackForth₂_mono ih a b hab.2⟩

theorem equivK₂_mono {E₀ E₀' : PebbleRel₂ M N k} (h : E₀'.Le E₀) :
    (EquivK₂ E₀').Le (EquivK₂ E₀) :=
  fun a b hab n => pebbleStage₂_mono h n a b (hab n)

/-- **The expansion lemma**: refining the initial relation by anything the
limit already refines does not change the limit – so expanding both structures
by relations the equivalence cannot see leaves it alone. -/
theorem equivK₂_inf_eq [Finite M] [Finite N] {E₀ E₀' : PebbleRel₂ M N k} (hle : E₀'.Le E₀)
    (hinv : (EquivK₂ E₀).Le E₀') : EquivK₂ E₀' = EquivK₂ E₀ := by
  funext a b
  refine propext ⟨fun h => equivK₂_mono hle a b h, fun h => ?_⟩
  refine le_equivK₂ (E₀ := E₀') (E := EquivK₂ E₀) (fun a b hab => ?_) a b h
  exact ⟨hinv a b hab, ((equivK₂_iff E₀ a b).mp hab).2⟩

/-! ### Agreement on the atomic type, across two structures -/

variable {L : Language.{0, 0}}

/-- Agreement on the atomic type between tuples of two structures: the same
equalities between coordinates, and the same base relations of the family `S`
at every selection of coordinates. -/
def atomicAgreeOn₂ (S : Set (Σ n, L.Relations n)) (M N : Type) [L.Structure M] [L.Structure N]
    (k : ℕ) : PebbleRel₂ M N k :=
  fun v w =>
    (∀ i j : Fin k, v i = v j ↔ w i = w j) ∧
    ∀ {l : ℕ} (R : L.Relations l), ⟨l, R⟩ ∈ S → ∀ g : Fin l → Fin k,
      ((RelMap R fun p => v (g p)) ↔ RelMap R fun p => w (g p))

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
    EquivK₂ (atomicAgreeOn₂ S M N k) v w := by
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

end DescriptiveComplexity
