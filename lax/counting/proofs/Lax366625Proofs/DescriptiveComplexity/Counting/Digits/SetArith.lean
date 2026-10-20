/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.OrderWalk
import Mathlib.Algebra.BigOperators.Finprod
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

/-!
# Binary numbers as sets of positions, and sweeps along an order

The semantic layer of the normal form of FP
(`DescriptiveComplexity.Counting.Digits`): no formula appears here.

* **Carries**: `DescriptiveComplexity.Digits.testBit_add_iff` reads a binary digit of
  a sum off the digits of the summands, the carry being given by lookahead
  (`DescriptiveComplexity.Digits.Carry`) rather than by a ripple – a condition with
  one existential and one universal quantifier over positions, hence
  first-order over an ordered set of positions.
* **Numbers over a finite linear order** `P` of positions:
  `DescriptiveComplexity.Digits.bitsOf N` is the set of positions whose rank
  (`DescriptiveComplexity.orank`) is a digit `1` of `N`. Only the digits of
  rank below the number of positions are seen, so this is `N` modulo
  `2 ^ |P|` (`DescriptiveComplexity.Digits.bitsOf_congr`), and addition, doubling and
  the choice between a number and zero are operations on such sets with no
  side condition.
* **Sweeps** (`DescriptiveComplexity.Digits.sweep_stage`): a family of rows indexed
  by a finite linear order, each a function of the rows before it, is computed
  by an inflationary iteration that marks a row *done* in the very step that
  writes it, and writes a row only when the previous one is done and it is not
  itself. A row is thus written once, in full, from rows that are complete –
  which is what lets its defining condition be an arbitrary one, negations
  included.
-/

namespace Lax366625Proofs.DescriptiveComplexity

namespace Digits

/-! ### Carries -/

/-- The carry into the digit of rank `i` of `M + N`, by lookahead: some lower
rank generates a carry, and every rank in between propagates it. -/
def Carry (M N i : ℕ) : Prop :=
  ∃ k, k < i ∧ M.testBit k = true ∧ N.testBit k = true ∧
    ∀ l, k < l → l < i → M.testBit l = true ∨ N.testBit l = true

theorem carry_zero (M N : ℕ) : ¬Carry M N 0 := fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)

theorem carry_succ (M N i : ℕ) :
    Carry M N (i + 1) ↔ (M.testBit i = true ∧ N.testBit i = true) ∨
      ((M.testBit i = true ∨ N.testBit i = true) ∧ Carry M N i) := by
  constructor
  · rintro ⟨k, hk, hM, hN, hall⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact Or.inr ⟨hall i hlt (Nat.lt_succ_self i),
        k, hlt, hM, hN, fun l hl hli => hall l hl (Nat.lt_succ_of_lt hli)⟩
    · exact Or.inl ⟨hM, hN⟩
  · rintro (⟨hM, hN⟩ | ⟨hi, k, hk, hM, hN, hall⟩)
    · exact ⟨i, Nat.lt_succ_self i, hM, hN, fun l hl hli => absurd hl (by omega)⟩
    · refine ⟨k, Nat.lt_succ_of_lt hk, hM, hN, fun l hl hli => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hli with hlt | rfl
      · exact hall l hl hlt
      · exact hi

/-- The carry, arithmetically: the low parts of the two numbers overflow. -/
theorem carry_iff (M N i : ℕ) : Carry M N i ↔ 2 ^ i ≤ M % 2 ^ i + N % 2 ^ i := by
  induction i with
  | zero =>
    refine iff_of_false (carry_zero M N) ?_
    simp [Nat.mod_one]
  | succ i ih =>
    rw [carry_succ, ih, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.mod_pow_succ (x := M), Nat.mod_pow_succ (x := N), pow_succ]
    have hM := Nat.mod_lt M (Nat.two_pow_pos i)
    have hN := Nat.mod_lt N (Nat.two_pow_pos i)
    have hm := Nat.mod_two_eq_zero_or_one (M / 2 ^ i)
    have hn := Nat.mod_two_eq_zero_or_one (N / 2 ^ i)
    generalize 2 ^ i = b at *
    generalize M % b = m₀ at *
    generalize N % b = n₀ at *
    generalize M / b % 2 = m at *
    generalize N / b % 2 = n at *
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;> simp <;> omega

/-- **A digit of a sum**: the exclusive or of the digits of the summands and
of the carry. -/
theorem testBit_add_iff (M N i : ℕ) :
    (M + N).testBit i = true ↔
      Xor (Xor (M.testBit i = true) (N.testBit i = true)) (Carry M N i) := by
  rw [carry_iff, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq, Nat.add_div (Nat.two_pow_pos i)]
  have hm := Nat.mod_two_eq_zero_or_one (M / 2 ^ i)
  have hn := Nat.mod_two_eq_zero_or_one (N / 2 ^ i)
  generalize M / 2 ^ i = m at *
  generalize N / 2 ^ i = n at *
  by_cases hc : 2 ^ i ≤ M % 2 ^ i + N % 2 ^ i <;>
    rcases hm with hm | hm <;> rcases hn with hn | hn <;>
      simp [Xor, hm, hn, hc, Nat.add_mod]

/-! ### Numbers over a finite linear order of positions -/

section Bits

variable {P : Type} [LinearOrder P]

/-- The positions holding a digit `1` of `N`, the rank of a position being
the rank of its digit. -/
def bitsOf (N : ℕ) (p : P) : Prop :=
  N.testBit (Lax895169.BitPredicate.orank p) = true

theorem bitsOf_zero (p : P) : ¬bitsOf 0 p := by
  simp [bitsOf]

/-- The choice between a number and zero. -/
theorem bitsOf_ite (c : Prop) [Decidable c] (N : ℕ) (p : P) :
    bitsOf (if c then N else 0) p ↔ c ∧ bitsOf N p := by
  split_ifs with h
  · exact (and_iff_right h).symm
  · exact iff_of_false (bitsOf_zero p) fun h' => h h'.1

variable [Finite P]

theorem orank_lt_iff {x y : P} : Lax895169.BitPredicate.orank x < Lax895169.BitPredicate.orank y ↔ x < y := by
  rw [← not_le, ← not_le, orank_le_iff]

/-- An element that is not least has an immediate predecessor. -/
theorem exists_covBy_of_not_min {z : P} (hz : ¬∀ a : P, z ≤ a) : ∃ w : P, w ⋖ z := by
  obtain ⟨w, hw, hnb⟩ := exists_succ_of_not_min hz
  exact ⟨w, hw, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩

/-- The number one: its only digit is at the least position. -/
theorem bitsOf_one (p : P) : bitsOf 1 p ↔ ∀ a : P, p ≤ a := by
  rw [bitsOf, Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · intro h a
    rw [← orank_le_iff, h]
    exact Nat.zero_le _
  · exact orank_eq_zero

/-- **Addition**, by carry lookahead over the positions. -/
theorem bitsOf_add (M N : ℕ) (p : P) :
    bitsOf (M + N) p ↔ Xor (Xor (bitsOf M p) (bitsOf N p))
      (∃ q, q < p ∧ bitsOf M q ∧ bitsOf N q ∧ ∀ r, q < r → r < p → bitsOf M r ∨ bitsOf N r) := by
  rw [bitsOf, testBit_add_iff]
  refine iff_of_eq (congrArg _ (propext ?_))
  constructor
  · rintro ⟨k, hk, hM, hN, hall⟩
    obtain ⟨q, rfl⟩ := exists_orank_eq (hk.trans (orank_lt_card p))
    exact ⟨q, orank_lt_iff.mp hk, hM, hN, fun r hqr hrp =>
      hall (Lax895169.BitPredicate.orank r) (orank_lt_iff.mpr hqr) (orank_lt_iff.mpr hrp)⟩
  · rintro ⟨q, hq, hM, hN, hall⟩
    refine ⟨Lax895169.BitPredicate.orank q, orank_lt_iff.mpr hq, hM, hN, fun l hl hlp => ?_⟩
    obtain ⟨r, rfl⟩ := exists_orank_eq (hlp.trans (orank_lt_card p))
    exact hall r (orank_lt_iff.mp hl) (orank_lt_iff.mp hlp)

/-- **Doubling**: a shift by one position. -/
theorem bitsOf_two_mul (N : ℕ) (p : P) : bitsOf (2 * N) p ↔ ∃ q, q ⋖ p ∧ bitsOf N q := by
  constructor
  · intro h
    by_cases hp : ∀ a : P, p ≤ a
    · rw [bitsOf, orank_eq_zero hp] at h
      simp at h
    · obtain ⟨q, hq⟩ := exists_covBy_of_not_min hp
      refine ⟨q, hq, ?_⟩
      rw [bitsOf, orank_covBy hq, Nat.testBit_succ] at h
      rwa [Nat.mul_div_cancel_left N (by norm_num : 0 < 2)] at h
  · rintro ⟨q, hq, h⟩
    rw [bitsOf, orank_covBy hq, Nat.testBit_succ,
      Nat.mul_div_cancel_left N (by norm_num : 0 < 2)]
    exact h

/-- Only the digits of rank below the number of positions are seen. -/
theorem bitsOf_congr {M N : ℕ} (h : M % 2 ^ Nat.card P = N % 2 ^ Nat.card P) :
    (bitsOf M : P → Prop) = bitsOf N := by
  funext p
  have hM := Nat.testBit_mod_two_pow M (Nat.card P) (Lax895169.BitPredicate.orank p)
  have hN := Nat.testBit_mod_two_pow N (Nat.card P) (Lax895169.BitPredicate.orank p)
  rw [decide_eq_true (orank_lt_card p), Bool.true_and] at hM hN
  rw [bitsOf, bitsOf, ← hM, ← hN, h]

end Bits

/-! ### Sums and products along an order -/

section Prefix

variable {I : Type} [LinearOrder I] [Finite I]

open Classical in
/-- The sum of a family up to an index. -/
noncomputable def sumUpTo (f : I → ℕ) (u : I) : ℕ :=
  ∑ᶠ u' : I, if u' ≤ u then f u' else 0

open Classical in
/-- The product of a family strictly before an index. -/
noncomputable def prodBefore (f : I → ℕ) (u : I) : ℕ :=
  ∏ᶠ u' : I, if u' < u then f u' else 1

theorem sumUpTo_bot (f : I → ℕ) {u : I} (hu : ∀ c, u ≤ c) : sumUpTo f u = f u := by
  classical
  let := Fintype.ofFinite I
  rw [sumUpTo, finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  have : (Finset.univ.filter fun u' : I => u' ≤ u) = {u} := by
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h (hu u'), fun h => h ▸ le_rfl⟩
  rw [this, Finset.sum_singleton]

theorem sumUpTo_covBy (f : I → ℕ) {u₀ u : I} (h : u₀ ⋖ u) :
    sumUpTo f u = sumUpTo f u₀ + f u := by
  classical
  let := Fintype.ofFinite I
  rw [sumUpTo, sumUpTo, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_filter, ← Finset.sum_filter]
  have : (Finset.univ.filter fun u' : I => u' ≤ u) =
      insert u (Finset.univ.filter fun u' : I => u' ≤ u₀) := by
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr (h.le_of_lt hlt)
    · rintro (rfl | hle)
      · exact le_rfl
      · exact hle.trans h.le
  rw [this, Finset.sum_insert, add_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  exact h.lt

omit [Finite I] in
theorem sumUpTo_top (f : I → ℕ) {u : I} (hu : ∀ c, c ≤ u) : sumUpTo f u = ∑ᶠ u' : I, f u' := by
  classical
  rw [sumUpTo]
  exact finsum_congr fun u' => if_pos (hu u')

omit [Finite I] in
theorem prodBefore_bot (f : I → ℕ) {u : I} (hu : ∀ c, u ≤ c) : prodBefore f u = 1 := by
  classical
  rw [prodBefore]
  exact (finprod_congr fun u' => if_neg (not_lt.mpr (hu u'))).trans finprod_one

theorem prodBefore_covBy (f : I → ℕ) {u₀ u : I} (h : u₀ ⋖ u) :
    prodBefore f u = prodBefore f u₀ * f u₀ := by
  classical
  let := Fintype.ofFinite I
  rw [prodBefore, prodBefore, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← Finset.prod_filter, ← Finset.prod_filter]
  have : (Finset.univ.filter fun u' : I => u' < u) =
      insert u₀ (Finset.univ.filter fun u' : I => u' < u₀) := by
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hlt
      rcases eq_or_lt_of_le (h.le_of_lt hlt) with rfl | hlt'
      · exact Or.inl rfl
      · exact Or.inr hlt'
    · rintro (rfl | hlt)
      · exact h.lt
      · exact hlt.trans h.lt
  rw [this, Finset.prod_insert, mul_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false, not_false_eq_true]

theorem prodBefore_top_mul (f : I → ℕ) {u : I} (hu : ∀ c, c ≤ u) :
    prodBefore f u * f u = ∏ᶠ u' : I, f u' := by
  classical
  let := Fintype.ofFinite I
  rw [prodBefore, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← Finset.prod_filter]
  have : (Finset.univ : Finset I) = insert u (Finset.univ.filter fun u' : I => u' < u) := by
    ext u'
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, Finset.mem_insert, true_iff]
    exact (eq_or_lt_of_le (hu u'))
  conv_rhs => rw [this]
  rw [Finset.prod_insert, mul_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false, not_false_eq_true]

end Prefix

/-! ### Reading a number back from its digits -/

/-- A number below `2 ^ c` is the sum of the place values of its first `c`
digits. -/
theorem sum_range_testBit (N c : ℕ) :
    ∑ i ∈ Finset.range c, (if N.testBit i = true then 2 ^ i else 0) = N % 2 ^ c := by
  induction c with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (N / 2 ^ c) with h | h <;> simp [h]

section ReadBack

variable {P : Type} [LinearOrder P] [Finite P]

open Classical in
/-- **A number with fewer digits than there are positions is the sum of the
place values of the positions of its digits `1`.** -/
theorem finsum_bitsOf {N : ℕ} (hN : N < 2 ^ Nat.card P) :
    ∑ᶠ p : P, (if bitsOf N p then 2 ^ Lax895169.BitPredicate.orank p else 0) = N := by
  let := Fintype.ofFinite P
  have hbij : Function.Bijective (fun p : P => (⟨Lax895169.BitPredicate.orank p, orank_lt_card p⟩ : Fin (Nat.card P))) :=
    ⟨fun x y hxy => orank_inj (congrArg Fin.val hxy), fun i => by
      obtain ⟨x, hx⟩ := exists_orank_eq i.isLt
      exact ⟨x, Fin.ext hx⟩⟩
  rw [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_equiv (Equiv.ofBijective _ hbij)
    (fun p : P => if bitsOf N p then 2 ^ Lax895169.BitPredicate.orank p else 0)
    (fun i : Fin (Nat.card P) => if N.testBit i = true then 2 ^ (i : ℕ) else 0)
      fun p => if_congr Iff.rfl rfl rfl,
    Fin.sum_univ_eq_sum_range (fun i => if N.testBit i = true then 2 ^ i else 0) (Nat.card P),
    sum_range_testBit, Nat.mod_eq_of_lt hN]

end ReadBack

/-- **The rank in a lexicographic product**: the rank of the head, times the
size of the tail order, plus the rank of the tail. -/
theorem orank_prodLex {J B : Type} [LinearOrder J] [LinearOrder B] [Finite J] [Finite B]
    (a : J) (b : B) :
    Lax895169.BitPredicate.orank (toLex (a, b)) = Lax895169.BitPredicate.orank a * Nat.card B + Lax895169.BitPredicate.orank b := by
  have hset : (ofLex '' {q : J ×ₗ B | q < toLex (a, b)}) =
      ({a' : J | a' < a} ×ˢ (Set.univ : Set B)) ∪ ((fun b' => (a, b')) '' {b' : B | b' < b}) := by
    ext q₀
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases prodLex_lt_iff.mp (show toLex ((ofLex q).1, (ofLex q).2) < toLex (a, b) from hq)
        with h | ⟨h1, h2⟩
      · exact Or.inl (Set.mem_prod.mpr ⟨h, Set.mem_univ _⟩)
      · exact Or.inr ⟨(ofLex q).2, h2, Prod.ext h1.symm rfl⟩
    · rintro (h | ⟨b'', h2, rfl⟩)
      · exact ⟨toLex q₀, prodLex_lt_iff.mpr (Or.inl (Set.mem_prod.mp h).1), rfl⟩
      · exact ⟨toLex (a, b''), prodLex_lt_iff.mpr (Or.inr ⟨rfl, h2⟩), rfl⟩
  have hdisj : Disjoint ({a' : J | a' < a} ×ˢ (Set.univ : Set B))
      ((fun b' => (a, b')) '' {b' : B | b' < b}) := by
    rw [Set.disjoint_left]
    rintro q₀ h1 ⟨b'', -, rfl⟩
    exact lt_irrefl a (Set.mem_prod.mp h1).1
  rw [Lax895169.BitPredicate.orank, ← Set.ncard_image_of_injective _ ofLex.injective, hset,
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_prod,
    Set.ncard_image_of_injective _ fun x y h => (Prod.mk.inj h).2, Set.ncard_univ]
  rfl

/-! ### Sweeps -/

section Sweep

variable {W Idx Pos : Type} [LinearOrder Idx] [Finite Idx]

/-- **The stages of a sweep.** Rows `T w i` indexed by a finite linear order,
each determined by the rows before it through `Φ`, are computed by the
iteration whose step marks a row done when it is the first or follows a done
one, and writes a row under the same condition when it is not yet done: after
`s` steps, the rows of rank below `s` are done and written, and nothing else
is. -/
theorem sweep_stage (Φ : W → Idx → (Idx → Pos → Prop) → Pos → Prop) (T : W → Idx → Pos → Prop)
    (hΦ : ∀ w i (R : Idx → Pos → Prop), (∀ i', i' < i → R i' = T w i') → Φ w i R = T w i)
    (Dn : ℕ → W → Idx → Prop) (Rw : ℕ → W → Idx → Pos → Prop)
    (hD0 : ∀ w i, ¬Dn 0 w i) (hR0 : ∀ w i p, ¬Rw 0 w i p)
    (hD : ∀ s w i, Dn (s + 1) w i ↔
      Dn s w i ∨ ((∀ a, i ≤ a) ∨ ∃ i₀, i₀ ⋖ i ∧ Dn s w i₀))
    (hR : ∀ s w i p, Rw (s + 1) w i p ↔ Rw s w i p ∨
      (¬Dn s w i ∧ ((∀ a, i ≤ a) ∨ ∃ i₀, i₀ ⋖ i ∧ Dn s w i₀) ∧ Φ w i (Rw s w) p)) :
    ∀ s w i, (Dn s w i ↔ Lax895169.BitPredicate.orank i < s) ∧ ∀ p, (Rw s w i p ↔ Lax895169.BitPredicate.orank i < s ∧ T w i p) := by
  intro s
  induction s with
  | zero =>
    exact fun w i => ⟨iff_of_false (hD0 w i) (Nat.not_lt_zero _),
      fun p => iff_of_false (hR0 w i p) fun h => Nat.not_lt_zero _ h.1⟩
  | succ s ih =>
    intro w i
    have hready : ((∀ a, i ≤ a) ∨ ∃ i₀, i₀ ⋖ i ∧ Dn s w i₀) ↔ Lax895169.BitPredicate.orank i ≤ s := by
      constructor
      · rintro (hmin | ⟨i₀, hcov, hd⟩)
        · rw [orank_eq_zero hmin]
          exact Nat.zero_le s
        · rw [orank_covBy hcov]
          exact (ih w i₀).1.mp hd
      · intro h
        by_cases hmin : ∀ a, i ≤ a
        · exact Or.inl hmin
        · obtain ⟨i₀, hcov⟩ := exists_covBy_of_not_min hmin
          refine Or.inr ⟨i₀, hcov, (ih w i₀).1.mpr ?_⟩
          have := orank_covBy hcov
          omega
    refine ⟨?_, fun p => ?_⟩
    · rw [hD, hready, (ih w i).1]
      omega
    · rw [hR, hready, (ih w i).1, (ih w i).2 p]
      constructor
      · rintro (⟨h, hT⟩ | ⟨h1, h2, hΦp⟩)
        · exact ⟨Nat.lt_succ_of_lt h, hT⟩
        · refine ⟨Nat.lt_succ_of_le h2, ?_⟩
          have hrows : ∀ i', i' < i → Rw s w i' = T w i' := fun i' hi' =>
            funext fun p' => propext (((ih w i').2 p').trans
              (and_iff_right (lt_of_lt_of_le (orank_lt_orank hi') h2)))
          rwa [hΦ w i _ hrows] at hΦp
      · rintro ⟨h, hT⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
        · exact Or.inl ⟨hlt, hT⟩
        · refine Or.inr ⟨by omega, by omega, ?_⟩
          have hrows : ∀ i', i' < i → Rw s w i' = T w i' := fun i' hi' =>
            funext fun p' => propext (((ih w i').2 p').trans
              (and_iff_right (heq ▸ orank_lt_orank hi')))
          rwa [hΦ w i _ hrows]

/-- **The limit of a sweep**: every row is eventually written, and written
right. -/
theorem sweep_limit (Φ : W → Idx → (Idx → Pos → Prop) → Pos → Prop) (T : W → Idx → Pos → Prop)
    (hΦ : ∀ w i (R : Idx → Pos → Prop), (∀ i', i' < i → R i' = T w i') → Φ w i R = T w i)
    (Dn : ℕ → W → Idx → Prop) (Rw : ℕ → W → Idx → Pos → Prop)
    (hD0 : ∀ w i, ¬Dn 0 w i) (hR0 : ∀ w i p, ¬Rw 0 w i p)
    (hD : ∀ s w i, Dn (s + 1) w i ↔
      Dn s w i ∨ ((∀ a, i ≤ a) ∨ ∃ i₀, i₀ ⋖ i ∧ Dn s w i₀))
    (hR : ∀ s w i p, Rw (s + 1) w i p ↔ Rw s w i p ∨
      (¬Dn s w i ∧ ((∀ a, i ≤ a) ∨ ∃ i₀, i₀ ⋖ i ∧ Dn s w i₀) ∧ Φ w i (Rw s w) p))
    (w : W) (i : Idx) (p : Pos) : (∃ s, Rw s w i p) ↔ T w i p := by
  have h := sweep_stage Φ T hΦ Dn Rw hD0 hR0 hD hR
  exact ⟨fun ⟨s, hs⟩ => (((h s w i).2 p).mp hs).2,
    fun hT => ⟨Lax895169.BitPredicate.orank i + 1, ((h _ w i).2 p).mpr ⟨Nat.lt_succ_self _, hT⟩⟩⟩

end Sweep

end Digits

end Lax366625Proofs.DescriptiveComplexity


