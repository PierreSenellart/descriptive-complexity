/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Games.Distance
import DescriptiveComplexity.Games.Ehrenfeucht
import DescriptiveComplexity.OrderWalk

/-!
# The game on finite linear orders

**Ehrenfeucht's theorem** ([Ehrenfeucht 1961][ehrenfeucht1961application];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 2): two finite linear orders
with at least `2 ^ n` elements each are `n`-round equivalent
(`DescriptiveComplexity.efEquiv_linearOrder`), whatever their sizes. First-order
logic can therefore count the elements of an ordered set no further than
exponentially in its quantifier rank – and, since the bound depends on the
sentence only, not at all in the limit.

This is the order-invariant half of the inexpressibility of
`DescriptiveComplexity.EVEN`, and the reason it is a real theorem rather than
the observation that a bare set carries no information: here the structure
carries *all* the information about the position of every point, and the
duplicator still wins.

## The strategy

A position is read through the *ranks* of its points
(`DescriptiveComplexity.orank`, the number of strict predecessors, shared with
the order-walk machinery) and two sentinels, `-1` below everything and the cardinality
above everything (`DescriptiveComplexity.extRank`); the duplicator's invariant
(`DescriptiveComplexity.OrdInv`) is then one equation per pair of points:
their distances agree up to truncation at `2 ^ n`
(`DescriptiveComplexity.truncAt`). The sentinels are what makes it *one*
equation: the distance to the ends of the order is the distance to a point
like any other.

Everything the invariant is used for is arithmetic and lives in
`DescriptiveComplexity.Games.Distance`, in particular the answer to a move
(`DescriptiveComplexity.exists_answer`), where the budget halves. What is left
here is the translation between the game and the arithmetic: a position is
legal exactly when the ranks are in the same order, and a round is one
application of the answer lemma.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The invariant -/

section Invariant

variable {A B : Type} [LinearOrder A] [LinearOrder B] {j n : ℕ}

/-- The ranks of a position, extended by two sentinels: `-1`, below every
element, and the cardinality, above every element. The distances to the two
ends of the order thereby become distances between points, so that the whole
invariant is one equation. -/
noncomputable def extRank {A : Type} [LinearOrder A] {j : ℕ} (a : Fin j → A) :
    Fin j ⊕ Bool → ℤ
  | Sum.inl i => (orank (a i) : ℤ)
  | Sum.inr false => -1
  | Sum.inr true => (Nat.card A : ℤ)

/-- **The duplicator's invariant on two finite linear orders**: any two points
of the position – sentinels included – are at the same distance on both sides,
up to truncation at `2 ^ n`. -/
def OrdInv (n : ℕ) (a : Fin j → A) (b : Fin j → B) : Prop :=
  ∀ i i' : Fin j ⊕ Bool,
    truncAt n (extRank a i - extRank a i') = truncAt n (extRank b i - extRank b i')

variable {a : Fin j → A} {b : Fin j → B}

/-- The invariant is symmetric. -/
theorem OrdInv.symm (h : OrdInv n a b) : OrdInv n b a :=
  fun i i' => (h i i').symm

/-- The invariant weakens as the budget is spent. -/
theorem OrdInv.mono {m : ℕ} (hmn : m ≤ n) (h : OrdInv n a b) : OrdInv m a b :=
  fun i i' => truncAt_eq_of_le hmn (h i i')

/-! ### One round -/

/-- The extended tuple of a position lengthened by one point, at an old
coordinate. -/
theorem extRank_snoc_lift (a : Fin j → A) (c : A) (i : Fin j ⊕ Bool) :
    extRank (Fin.snoc a c) (Sum.map Fin.castSucc id i) = extRank a i := by
  rcases i with i | β
  · change ((orank ((Fin.snoc a c : Fin (j + 1) → A) i.castSucc) : ℤ)) = (orank (a i) : ℤ)
    rw [Fin.snoc_castSucc]
  · cases β <;> rfl

/-- The extended tuple of a position lengthened by one point, at the new
coordinate. -/
theorem extRank_snoc_last (a : Fin j → A) (c : A) :
    extRank (Fin.snoc a c) (Sum.inl (Fin.last j)) = (orank c : ℤ) := by
  change ((orank ((Fin.snoc a c : Fin (j + 1) → A) (Fin.last j)) : ℤ)) = (orank c : ℤ)
  rw [Fin.snoc_last]

/-- An extended coordinate of a lengthened position is either an old one or
the new one. -/
theorem extIndex_cases (i : Fin (j + 1) ⊕ Bool) :
    (∃ i₀ : Fin j ⊕ Bool, i = Sum.map Fin.castSucc id i₀) ∨ i = Sum.inl (Fin.last j) := by
  rcases i with k | β
  · induction k using Fin.lastCases with
    | last => exact Or.inr rfl
    | cast q => exact Or.inl ⟨Sum.inl q, rfl⟩
  · exact Or.inl ⟨Sum.inr β, rfl⟩

/-- The empty position satisfies the invariant as soon as both orders have at
least `2 ^ n` elements: the only distance to check is the one between the two
sentinels, and it is beyond the truncation on both sides. -/
theorem ordInv_default (n : ℕ) (hA : 2 ^ n ≤ Nat.card A) (hB : 2 ^ n ≤ Nat.card B) :
    OrdInv n (default : Fin 0 → A) (default : Fin 0 → B) := by
  have hA' : (2 : ℤ) ^ n ≤ (Nat.card A : ℤ) := by
    simpa using (Nat.cast_le (α := ℤ)).mpr hA
  have hB' : (2 : ℤ) ^ n ≤ (Nat.card B : ℤ) := by
    simpa using (Nat.cast_le (α := ℤ)).mpr hB
  have hneg : truncAt n (-1 - (Nat.card A : ℤ)) = truncAt n (-1 - (Nat.card B : ℤ)) := by
    rw [truncAt_of_le_neg (by omega), truncAt_of_le_neg (by omega)]
  have hpos : truncAt n ((Nat.card A : ℤ) - -1) = truncAt n ((Nat.card B : ℤ) - -1) := by
    rw [truncAt_of_le (by omega), truncAt_of_le (by omega)]
  rintro (i | β) (i' | β')
  · exact i.elim0
  · exact i.elim0
  · exact i'.elim0
  · cases β <;> cases β' <;> simp only [extRank] <;> first | rfl | exact hneg | exact hpos | simp

variable [Finite A] [Finite B]

/-- **One round of the game**: whatever point the spoiler adds on the left,
the duplicator has an answer on the right keeping the invariant, at the cost
of one unit of budget. The answer is computed in the integers
(`DescriptiveComplexity.exists_answer`) and comes back into the structure
because it lands strictly between the two sentinels. -/
theorem exists_ordInv_snoc (h : OrdInv (n + 1) a b) (c : A) :
    ∃ d : B, OrdInv n (Fin.snoc a c) (Fin.snoc b d) := by
  have hcA : extRank a (Sum.inr true) = (Nat.card A : ℤ) := rfl
  have hcB : extRank b (Sum.inr true) = (Nat.card B : ℤ) := rfl
  have hcard := orank_lt_card c
  obtain ⟨z, hz⟩ := exists_answer (U := extRank a) (V := extRank b) h
    (c := (orank c : ℤ)) (i₀ := Sum.inr false) (i₁ := Sum.inr true)
    (by simp only [extRank]; omega) (by rw [hcA]; omega)
  -- the answer lies strictly between the two sentinels, so it is a rank
  have hlow : 0 ≤ z := by
    have h' := lt_zero_congr_of_truncAt (hz (Sum.inr false))
    have h'' := eq_zero_congr_of_truncAt (hz (Sum.inr false))
    simp only [extRank] at h' h''
    omega
  have hhigh : z.toNat < Nat.card B := by
    have h' := le_zero_congr_of_truncAt (hz (Sum.inr true))
    rw [hcA, hcB] at h'
    omega
  obtain ⟨d, hd'⟩ := exists_orank_eq hhigh
  have hd : (orank d : ℤ) = z := by omega
  refine ⟨d, fun i i' => ?_⟩
  rcases extIndex_cases i with ⟨i₀, rfl⟩ | rfl <;>
    rcases extIndex_cases i' with ⟨i₀', rfl⟩ | rfl
  · rw [extRank_snoc_lift, extRank_snoc_lift, extRank_snoc_lift, extRank_snoc_lift]
    exact truncAt_eq_of_le (Nat.le_succ n) (h i₀ i₀')
  · rw [extRank_snoc_lift, extRank_snoc_last, extRank_snoc_lift, extRank_snoc_last, hd]
    exact hz i₀
  · rw [extRank_snoc_lift, extRank_snoc_last, extRank_snoc_lift, extRank_snoc_last, hd]
    have := neg_congr_of_truncAt (hz i₀')
    have he₁ : -(extRank a i₀' - (orank c : ℤ)) = (orank c : ℤ) - extRank a i₀' := by omega
    have he₂ : -(extRank b i₀' - z) = z - extRank b i₀' := by omega
    rwa [he₁, he₂] at this
  · rw [extRank_snoc_last, extRank_snoc_last]
    simp

/-! ### The game -/

variable [Language.empty.Structure A] [Language.empty.Structure B]

/-- **A position satisfying the invariant is legal**: the equalities between
coordinates and the order between them are read off the ranks, which the
invariant preserves. -/
theorem partialIso_of_ordInv (h : OrdInv n a b) :
    PartialIso (Language.empty.sum Language.order) a b := by
  constructor
  · intro i i'
    rw [← orank_inj_iff (x := a i) (y := a i'), ← orank_inj_iff (x := b i) (y := b i')]
    have := eq_zero_congr_of_truncAt (h (Sum.inl i) (Sum.inl i'))
    simp only [extRank] at this
    omega
  · rintro l (R | R) g
    · exact (R : Empty).elim
    · cases R
      change a (g 0) ≤ a (g 1) ↔ b (g 0) ≤ b (g 1)
      rw [← orank_le_iff (x := a (g 0)) (y := a (g 1)),
        ← orank_le_iff (x := b (g 0)) (y := b (g 1))]
      have := le_zero_congr_of_truncAt (h (Sum.inl (g 0)) (Sum.inl (g 1)))
      simp only [extRank] at this
      omega

/-- **The duplicator survives on a line**: a position satisfying the invariant
with budget `n` survives `n` rounds. -/
theorem efStage_of_ordInv : ∀ (n : ℕ) {j : ℕ} (a : Fin j → A) (b : Fin j → B),
    OrdInv n a b → efStage (Language.empty.sum Language.order) n a b := by
  intro n
  induction n with
  | zero => exact fun _ _ h => partialIso_of_ordInv h
  | succ n ih =>
    intro _ a b h
    refine ⟨partialIso_of_ordInv h, fun c => ?_, fun d => ?_⟩
    · obtain ⟨d, hd⟩ := exists_ordInv_snoc h c
      exact ⟨d, ih _ _ hd⟩
    · obtain ⟨c, hc⟩ := exists_ordInv_snoc h.symm d
      exact ⟨c, ih _ _ hc.symm⟩

end Invariant

/-! ### Ehrenfeucht's theorem -/

variable {A B : Type} [Language.empty.Structure A] [Language.empty.Structure B]
  [LinearOrder A] [LinearOrder B] [Finite A] [Finite B]

/-- **Ehrenfeucht's theorem**: two finite linear orders with at least `2 ^ n`
elements each are `n`-round equivalent, however far apart their sizes. By the
methodology lemma (`DescriptiveComplexity.realize_sentence_of_efEquiv`) a
sentence of quantifier rank `n` over the ordered vocabulary cannot separate
them: first-order logic counts the elements of an ordered set only up to
`2 ^ n`. -/
theorem efEquiv_linearOrder (n : ℕ) (hA : 2 ^ n ≤ Nat.card A) (hB : 2 ^ n ≤ Nat.card B) :
    EFEquiv (Language.empty.sum Language.order) A B n :=
  efStage_of_ordInv n default default (ordInv_default n hA hB)

end DescriptiveComplexity
