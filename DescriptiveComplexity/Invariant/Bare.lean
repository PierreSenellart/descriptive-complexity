/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Stages

/-!
# `≡ᵏ` on a bare set, and the order an induction cannot define

The invariant layer, read over the *empty* vocabulary. There `≡ᵏ` collapses as
far as it can: two `k`-tuples are equivalent as soon as they satisfy the same
equalities between coordinates (`DescriptiveComplexity.equivK_bare`), provided
the set has `k` elements to spare – the duplicator answers a repeated pebble by
the matching repetition and a fresh one by a fresh one, and only `k - 1`
pebbles constrain the answer since the moved one is being replaced.

The consequence is the theorem this file exists for
(`DescriptiveComplexity.not_isLinearOrder_inflLimit`): **no order-free
inflationary induction defines a linear order on a bare set**. Every stage of
such an induction is `≡ᵏ`-invariant
(`DescriptiveComplexity.StepDef.inflLimit_invariant`), and a transposition of
the universe carries any pair to the swapped pair without changing the
equality pattern, so a binary variable of the limit is *symmetric* – which no
antisymmetric total relation on two distinct points can be.

This is what turns the order-invariant convention of this library into a
theorem: the linear order that `DescriptiveComplexity.IFPDefinable`,
`DescriptiveComplexity.TCDefinable` and the rest are handed is not a
convenience, it is something no isomorphism-invariant logic can produce for
itself.

What it is *not* is a statement about a complexity class. It concerns a
defined *relation*; a Boolean query is separated by comparing two structures
of different sizes, which nothing in this layer does – `≡ᵏ` relates tuples
inside one structure. The class-level statement (order-free FO(IFP) does not
capture PTIME, at `DescriptiveComplexity.EVEN`) needs the two-structure pebble
game and is a separate development.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### Every induction reads every symbol -/

variable {L : Language.{0, 0}}

/-- Over the full agreement family there is nothing to check: every formula's
relation symbols lie in it. -/
theorem relsIn_blockRelsExtend_univ {B : SOBlock} {α : Type*} {n : ℕ}
    (φ : (L.sum B.lang).BoundedFormula α n) :
    RelsIn (blockRelsExtend (Set.univ : Set (Σ n, L.Relations n)) B) φ := by
  induction φ with
  | falsum => trivial
  | equal => trivial
  | rel R _ => rcases R with r | r <;> trivial
  | imp _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | all _ ih => exact ih

/-- Every induction uses symbols of the full family: the hypothesis of the
invariance theorems is free when one does not care which symbols are read. -/
theorem StepDef.usesRels_univ (d : StepDef L) :
    d.UsesRels (Set.univ : Set (Σ n, L.Relations n)) :=
  ⟨fun _ => relsIn_blockRelsExtend_univ _, relsIn_blockRelsExtend_univ _⟩

/-! ### Moving a pebble on a bare set -/

variable {A : Type} {k : ℕ}

/-- A tuple of `k` elements leaves a `k`-element set an element to spare once
one of its pebbles is freed. -/
theorem exists_notMem_image_erase [Finite A] (w : Fin k → A) (i : Fin k)
    (hA : k ≤ Nat.card A) : ∃ d : A, ∀ j, j ≠ i → w j ≠ d := by
  classical
  letI := Fintype.ofFinite A
  have hcard : ((Finset.univ.erase i).image w).card < (Finset.univ : Finset A).card := by
    calc ((Finset.univ.erase i).image w).card
        ≤ (Finset.univ.erase i).card := Finset.card_image_le
      _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
      _ < Nat.card A := by have := i.isLt; omega
      _ = (Finset.univ : Finset A).card := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨d, fun j hj heq => hd (heq ▸ Finset.mem_image_of_mem w
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))⟩

/-- Replacing a pebble on both sides by a matching pair of elements –
matching in the sense that each *other* coordinate hits the new element on the
left exactly when it does on the right – preserves the equality pattern. -/
theorem update_pattern {B : Type} {v : Fin k → A} {w : Fin k → B} {c : A} {d : B}
    (hpat : ∀ p q, v p = v q ↔ w p = w q) (i : Fin k)
    (hc : ∀ j, j ≠ i → (v j = c ↔ w j = d)) :
    ∀ p q, Function.update v i c p = Function.update v i c q ↔
      Function.update w i d p = Function.update w i d q := by
  intro p q
  by_cases hp : p = i <;> by_cases hq : q = i
  · rw [hp, hq]
    exact iff_of_true rfl rfl
  · rw [hp, Function.update_self, Function.update_self, Function.update_of_ne hq,
      Function.update_of_ne hq]
    exact ⟨fun h => ((hc q hq).mp h.symm).symm, fun h => ((hc q hq).mpr h.symm).symm⟩
  · rw [hq, Function.update_self, Function.update_self, Function.update_of_ne hp,
      Function.update_of_ne hp]
    exact hc p hp
  · rw [Function.update_of_ne hp, Function.update_of_ne hq, Function.update_of_ne hp,
      Function.update_of_ne hq]
    exact hpat p q

/-- **The duplicator's answer on a bare set**: whichever pebble is moved
wherever, the equality pattern can be restored – by the matching repetition,
or by a fresh element, of which there is one since the moved pebble no longer
constrains the answer. -/
theorem exists_update_pattern [Finite A] (hA : k ≤ Nat.card A) {v w : Fin k → A}
    (hpat : ∀ p q, v p = v q ↔ w p = w q) (i : Fin k) (c : A) :
    ∃ d : A, ∀ p q, Function.update v i c p = Function.update v i c q ↔
      Function.update w i d p = Function.update w i d q := by
  classical
  by_cases hc : ∃ j, j ≠ i ∧ v j = c
  · obtain ⟨j₀, hj₀, hvj₀⟩ := hc
    refine ⟨w j₀, update_pattern hpat i fun j _ => ?_⟩
    rw [← hvj₀]
    exact hpat j j₀
  · have hc' : ∀ j, j ≠ i → v j ≠ c := fun j hj hvj => hc ⟨j, hj, hvj⟩
    obtain ⟨d, hd⟩ := exists_notMem_image_erase w i hA
    exact ⟨d, update_pattern hpat i fun j hj => iff_of_false (hc' j hj) (hd j hj)⟩

/-! ### `≡ᵏ` over the empty vocabulary -/

/-- **On a bare set, `≡ᵏ` is the equality pattern**: two `k`-tuples over the
empty vocabulary satisfying the same equalities between coordinates are
`≡ᵏ`-equivalent, as soon as the set has `k` elements. The strategy is
`DescriptiveComplexity.exists_update_pattern`, fed to the coinduction
principle `DescriptiveComplexity.le_equivK`. -/
theorem equivK_bare [Language.empty.Structure A] [Finite A]
    {S : Set (Σ n, Language.empty.Relations n)} (hA : k ≤ Nat.card A) {v w : Fin k → A}
    (hpat : ∀ p q, v p = v q ↔ w p = w q) :
    EquivK (atomicAgreeOn S A k) v w := by
  refine le_equivK (E := fun v w => ∀ p q, v p = v q ↔ w p = w q) ?_ v w hpat
  intro v w hvw
  refine ⟨⟨hvw, ?_⟩, fun i => ⟨fun c => ?_, fun d => ?_⟩⟩
  · intro l R _ _
    exact (R : Empty).elim
  · exact exists_update_pattern hA hvw i c
  · obtain ⟨c, hc⟩ := exists_update_pattern hA (fun p q => (hvw p q).symm) i d
    exact ⟨c, fun p q => (hc p q).symm⟩

/-! ### The order no order-free induction defines -/

section LinearOrder

variable (d : StepDef Language.empty) {i : d.B.ι}

/-- **A binary variable of an order-free induction is symmetric on a bare
set**: the transposition exchanging the two arguments leaves the equality
pattern of the tuple alone, so `≡ᵏ`-invariance
(`DescriptiveComplexity.StepDef.inflLimit_invariant`) cannot tell the pair
from the swapped pair. -/
theorem inflLimit_swap_bare (hd : d.VarBound k) (harity : d.B.arity i = 2)
    (A : Type) [Language.empty.Structure A] [Finite A] (hA : k ≤ Nat.card A) (x y : A) :
    d.inflLimit A i (fun p => ![x, y] (Fin.cast harity p)) ↔
      d.inflLimit A i (fun p => ![y, x] (Fin.cast harity p)) := by
  classical
  have hk2 : 2 ≤ k := by have := hd i; omega
  -- two distinct coordinates, and a tuple carrying `x` and `y` there
  have hne : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  obtain ⟨v, hv₀, hv₁⟩ : ∃ v : Fin k → A,
      v ⟨0, by omega⟩ = x ∧ v ⟨1, by omega⟩ = y :=
    ⟨fun t => if t = ⟨1, by omega⟩ then y else x, if_neg hne, if_pos rfl⟩
  -- the swapped tuple has the same equality pattern: a transposition is a bijection
  have hpat : ∀ p q, v p = v q ↔ Equiv.swap x y (v p) = Equiv.swap x y (v q) :=
    fun p q => ⟨fun h => by rw [h], fun h => (Equiv.swap x y).injective h⟩
  -- read the two arguments of the variable off the two coordinates
  have hkey : ∀ t : Fin 2,
      v (![(⟨0, by omega⟩ : Fin k), ⟨1, by omega⟩] t) = ![x, y] t ∧
        Equiv.swap x y (v (![(⟨0, by omega⟩ : Fin k), ⟨1, by omega⟩] t)) = ![y, x] t := by
    intro t
    fin_cases t
    · refine ⟨hv₀, ?_⟩
      change Equiv.swap x y (v ⟨0, by omega⟩) = y
      rw [hv₀, Equiv.swap_apply_left]
    · refine ⟨hv₁, ?_⟩
      change Equiv.swap x y (v ⟨1, by omega⟩) = x
      rw [hv₁, Equiv.swap_apply_right]
  have hinv := d.inflLimit_invariant (A := A) (k := k) hd d.usesRels_univ i
    (fun p => ![(⟨0, by omega⟩ : Fin k), ⟨1, by omega⟩] (Fin.cast harity p))
    (equivK_bare hA hpat)
  rwa [funext fun p => (hkey (Fin.cast harity p)).1,
    funext fun p => (hkey (Fin.cast harity p)).2] at hinv

/-- **No order-free inflationary induction defines a linear order on a bare
set.** On a set with at least `k` elements – `k` a variable budget of the
induction – every binary variable of the limit is symmetric
(`DescriptiveComplexity.inflLimit_swap_bare`), and a symmetric relation on two
distinct points is not both antisymmetric and total. The two distinct points
are there because a binary variable forces `2 ≤ k ≤ Nat.card A`.

This is the order-invariance of the library's definability notions, as a
theorem: what a first-order induction is handed with the order, it cannot
build. -/
theorem not_isLinearOrder_inflLimit (hd : d.VarBound k) (harity : d.B.arity i = 2)
    (A : Type) [Language.empty.Structure A] [Finite A] (hA : k ≤ Nat.card A) :
    ¬IsLinearOrder A fun x y => d.inflLimit A i (fun p => ![x, y] (Fin.cast harity p)) := by
  intro hlin
  have hk2 : 2 ≤ k := by have := hd i; omega
  letI := Fintype.ofFinite A
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne A
  have hsymm := inflLimit_swap_bare d hd harity A hA x y
  rcases hlin.total x y with h | h
  · exact hxy (hlin.antisymm x y h (hsymm.mp h))
  · exact hxy (hlin.antisymm x y (hsymm.mpr h) h)

end LinearOrder

end DescriptiveComplexity
