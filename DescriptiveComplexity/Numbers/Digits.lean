/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel

/-!
# Numbers written in base `B` on a relation-ordered index set

`DescriptiveComplexity.binNum` writes a number in base two, one bit per position. The
reduction that proves Knapsack NP-hard needs the same reading in a larger
base: the ground elements of a set system become *blocks* of bits, and the
number of sets covering an element becomes the digit of that block. Choosing
the base above the number of sets is what stops carries from crossing a block
boundary, and then a sum of weights equals the target exactly when every
element is covered once – which is uniqueness of base-`B` expansions,
`DescriptiveComplexity.digitNum_inj` here.

The development mirrors the binary one: a peeling lemma for the lowest block
(`DescriptiveComplexity.digitNum_peel_min`) and an induction on the number of blocks.
`DescriptiveComplexity.binNum` is the special case of base two with digits `0` and `1`
(`DescriptiveComplexity.binNum_eq_digitNum`).
-/

namespace DescriptiveComplexity

/-- A sum of `0`s and `1`s counts. -/
theorem finsum_mem_ite_one {ι : Type} [Finite ι] (S : Set ι) (p : ι → Prop)
    [DecidablePred p] :
    (∑ᶠ i ∈ S, if p i then 1 else 0) = ({i | i ∈ S ∧ p i} : Set ι).ncard := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite S), Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, mul_one, add_zero,
    ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

section Digits

variable {A : Type} [Finite A]

/-- The number written by the digits `c` in base `B`, the place values being
fixed by the rank of a block among the blocks. -/
noncomputable def digitNum (Le : A → A → Prop) (Blk : A → Prop) (B : ℕ) (c : A → ℕ) : ℕ :=
  ∑ᶠ e ∈ {e : A | Blk e}, c e * B ^ bitRank Le Blk e

omit [Finite A] in
theorem digitNum_congr_on {Le : A → A → Prop} {Blk : A → Prop} {B : ℕ} {c c' : A → ℕ}
    (h : ∀ e, Blk e → c e = c' e) : digitNum Le Blk B c = digitNum Le Blk B c' := by
  refine finsum_mem_congr rfl fun e he => ?_
  rw [h e he]

/-- **Peeling the lowest block**: the value is the lowest digit plus `B` times
the value of the rest. -/
theorem digitNum_peel_min {Le : A → A → Prop} {Blk : A → Prop} {B : ℕ} {c : A → ℕ}
    {e₀ : A} (hlin : IsLinOrd Le) (h₀ : Blk e₀) (hmin : ∀ q, Blk q → Le e₀ q) :
    digitNum Le Blk B c =
      c e₀ + B * digitNum Le (fun q => Blk q ∧ q ≠ e₀) B c := by
  classical
  have hrank₀ : bitRank Le Blk e₀ = 0 := by
    have hset : {q : A | Blk q ∧ Le q e₀ ∧ q ≠ e₀} = (∅ : Set A) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hq, hle, hne⟩
      exact hne (hlin.2.2.1 q e₀ hle (hmin q hq))
    rw [bitRank, hset, Set.ncard_empty]
  have hsplit : {e : A | Blk e} = {e : A | Blk e ∧ e ≠ e₀} ∪ {e : A | e = e₀} := by
    ext e
    constructor
    · intro he
      rcases eq_or_ne e e₀ with rfl | hne
      · exact Or.inr rfl
      · exact Or.inl ⟨he, hne⟩
    · rintro (⟨he, -⟩ | rfl)
      · exact he
      · exact h₀
  have hdisj : Disjoint {e : A | Blk e ∧ e ≠ e₀} {e : A | e = e₀} := by
    rw [Set.disjoint_left]
    rintro e ⟨-, hne⟩ rfl
    exact hne rfl
  rw [digitNum, hsplit, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)]
  have hlow : (∑ᶠ e ∈ {e : A | e = e₀}, c e * B ^ bitRank Le Blk e) = c e₀ := by
    have hset : {e : A | e = e₀} = {e₀} := by
      ext e
      simp
    rw [hset, finsum_mem_singleton, hrank₀, pow_zero, Nat.mul_one]
  have hhigh : (∑ᶠ e ∈ {e : A | Blk e ∧ e ≠ e₀}, c e * B ^ bitRank Le Blk e) =
      B * digitNum Le (fun q => Blk q ∧ q ≠ e₀) B c := by
    rw [digitNum, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : Blk e ∧ e ≠ e₀ := by simpa using he
    rw [bitRank_erase_min h₀ hmin he'.1 he'.2, pow_succ]
    ring
  rw [hlow, hhigh, Nat.add_comm]

/-- **Uniqueness of base-`B` expansions**: digits below the base are
determined by the number they write. -/
theorem digitNum_inj {Le : A → A → Prop} {B : ℕ} (hlin : IsLinOrd Le)
    (hB : 0 < B) :
    ∀ (n : ℕ) (Blk : A → Prop), ({e : A | Blk e} : Set A).ncard = n →
      ∀ c d : A → ℕ, (∀ e, c e < B) → (∀ e, d e < B) →
        digitNum Le Blk B c = digitNum Le Blk B d → ∀ e, Blk e → c e = d e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Blk hn c d hc hd heq e he
    obtain ⟨e₀, h₀, hmin⟩ := exists_minPos hlin ⟨e, he⟩
    have hset' : {q : A | Blk q ∧ q ≠ e₀} = {q : A | Blk q} \ {e₀} := by
      ext q
      simp
    have hpos : 0 < ({q : A | Blk q} : Set A).ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨e, he⟩
    have hcard : ({q : A | Blk q ∧ q ≠ e₀} : Set A).ncard + 1 = n := by
      rw [hset', Set.ncard_sdiff_singleton_of_mem (show e₀ ∈ {q : A | Blk q} from h₀), ← hn]
      omega
    rw [digitNum_peel_min hlin h₀ hmin, digitNum_peel_min hlin h₀ hmin] at heq
    -- the lowest digits agree, being the remainders
    have hmod : ∀ x y : ℕ, x < B → (x + B * y) % B = x := by
      intro x y hx
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have hlow : c e₀ = d e₀ := by
      rw [← hmod (c e₀) (digitNum Le (fun q => Blk q ∧ q ≠ e₀) B c) (hc e₀), heq,
        hmod (d e₀) _ (hd e₀)]
    have hrest : digitNum Le (fun q => Blk q ∧ q ≠ e₀) B c =
        digitNum Le (fun q => Blk q ∧ q ≠ e₀) B d := by
      rw [hlow] at heq
      exact Nat.eq_of_mul_eq_mul_left hB (by omega)
    rcases eq_or_ne e e₀ with rfl | hne
    · exact hlow
    · exact IH ({q : A | Blk q ∧ q ≠ e₀} : Set A).ncard (by omega)
        (fun q => Blk q ∧ q ≠ e₀) rfl c d hc hd hrest e ⟨he, hne⟩

open Classical in
/-- **Selecting blocks**: the sum of the place values of the blocks satisfying
`sub` is the number whose digits are `1` there and `0` elsewhere. -/
theorem finsum_pow_eq_digitNum {Le : A → A → Prop} {Blk sub : A → Prop} {B : ℕ}
    (h : ∀ e, sub e → Blk e) :
    (∑ᶠ e ∈ {e : A | sub e}, B ^ bitRank Le Blk e) =
      digitNum Le Blk B (fun e => if sub e then 1 else 0) := by
  classical
  have h1 : (∑ᶠ e ∈ {e : A | sub e}, B ^ bitRank Le Blk e) =
      ∑ᶠ e ∈ {e : A | sub e}, (if sub e then 1 else 0) * B ^ bitRank Le Blk e := by
    refine finsum_mem_congr rfl fun e he => ?_
    have he' : sub e := he
    simp [he']
  rw [h1, digitNum, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  refine Finset.sum_subset (fun e he => ?_) (fun e he he' => ?_)
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at he ⊢
    exact h e he
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at he he'
    simp [he']

open Classical in
/-- Base two with digits `0` and `1` is the binary reading. -/
theorem binNum_eq_digitNum {Le : A → A → Prop} {Posn b : A → Prop} :
    binNum Le Posn b = digitNum Le Posn 2 (fun p => if b p then 1 else 0) := by
  rw [binNum]
  refine (finsum_pow_eq_digitNum fun p hp => hp.1).trans (digitNum_congr_on fun e he => ?_)
  by_cases hb : b e <;> simp [hb, he]

open Classical in
/-- **Digit-wise addition**: a sum of numbers written on the same blocks is
written by the sums of the digits – before any carrying, which is what the
bound on the digits then rules out. -/
theorem digitNum_finsum {ι : Type} [Finite ι] {Le : A → A → Prop} {Blk : A → Prop} {B : ℕ}
    (S : Set ι) (c : ι → A → ℕ) :
    (∑ᶠ i ∈ S, digitNum Le Blk B (c i)) = digitNum Le Blk B fun e => ∑ᶠ i ∈ S, c i e := by
  classical
  have hS : S.Finite := Set.toFinite S
  have hB : ({e : A | Blk e}).Finite := Set.toFinite _
  have hfun : (fun e => ∑ᶠ i ∈ S, c i e) = fun e => ∑ i ∈ hS.toFinset, c i e :=
    funext fun e => finsum_mem_eq_finite_toFinset_sum _ hS
  have hone : ∀ i, digitNum Le Blk B (c i) =
      ∑ e ∈ hB.toFinset, c i e * B ^ bitRank Le Blk e := fun i => by
    rw [digitNum, finsum_mem_eq_finite_toFinset_sum _ hB]
  rw [hfun, digitNum, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hB]
  simp only [hone, Finset.sum_mul]
  exact Finset.sum_comm

end Digits

end DescriptiveComplexity
