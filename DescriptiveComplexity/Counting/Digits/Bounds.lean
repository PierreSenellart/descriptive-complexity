/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Quantitative
import DescriptiveComplexity.Padding

/-!
# The size of the value of a quantitative term

Two facts about a term of quantitative first-order logic
(`DescriptiveComplexity.QTerm`), needed to write its value digit by digit.

* **A polynomial number of digits**
  (`DescriptiveComplexity.QTerm.exists_bound`): for some `ℓ`, the value is
  below `2 ^ (n ^ ℓ)` on every structure with `n ≥ 2` elements. So the
  `ℓ`-tuples of elements are enough positions for its binary digits.
* **One-element structures** (`DescriptiveComplexity.QTerm.exists_formulas`):
  there, a term takes finitely many values, and “the value is `N`” is a formula.
  A one-element structure has a single tuple of each length, hence too few
  positions, and is treated apart.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QTerm

variable {L : Language.{0, 0}}

/-! ### A polynomial number of digits -/

private theorem pow_add_pow_le {n : ℕ} (hn : 2 ≤ n) (M : ℕ) : n ^ M + n ^ M ≤ n ^ (M + 1) := by
  rw [pow_succ, ← mul_two]
  exact Nat.mul_le_mul_left _ hn

private theorem exp_mono {n : ℕ} (hn : 2 ≤ n) {a b : ℕ} (h : a ≤ b) :
    2 ^ (n ^ a) ≤ 2 ^ (n ^ b) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) h)

/-- **The value of a term has polynomially many digits**: it is at most
`2 ^ (n ^ ℓ)` on the structures with `n ≥ 2` elements. -/
theorem exists_bound_le {α : Type} (t : QTerm L α) :
    ∃ ℓ : ℕ, ∀ (A : Type) [L.Structure A] [Finite A], 2 ≤ Nat.card A →
      ∀ v : α → A, t.eval v ≤ 2 ^ (Nat.card A ^ ℓ) := by
  induction t with
  | ind φ =>
    refine ⟨0, fun A _ _ _ v => ?_⟩
    simp only [eval]
    split_ifs <;> simp
  | const s =>
    refine ⟨s, fun A _ _ hn v => ?_⟩
    have h1 : s ≤ Nat.card A ^ s :=
      (Nat.lt_two_pow_self (n := s)).le.trans (Nat.pow_le_pow_left hn s)
    exact (Nat.lt_two_pow_self (n := s)).le.trans (Nat.pow_le_pow_right (by norm_num) h1)
  | add s t hs ht =>
    obtain ⟨ℓ₁, h₁⟩ := hs
    obtain ⟨ℓ₂, h₂⟩ := ht
    refine ⟨max ℓ₁ ℓ₂ + 1, fun A _ _ hn v => ?_⟩
    have e1 := (h₁ A hn v).trans (exp_mono hn (le_max_left ℓ₁ ℓ₂))
    have e2 := (h₂ A hn v).trans (exp_mono hn (le_max_right ℓ₁ ℓ₂))
    have hone : 1 ≤ Nat.card A ^ max ℓ₁ ℓ₂ := Nat.one_le_pow _ _ (by omega)
    calc (add s t).eval v = s.eval v + t.eval v := rfl
      _ ≤ 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂) + 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂) := Nat.add_le_add e1 e2
      _ = 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂ + 1) := by rw [pow_succ, mul_two]
      _ ≤ 2 ^ (Nat.card A ^ (max ℓ₁ ℓ₂ + 1)) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.add_le_add_left hone _).trans (pow_add_pow_le hn _))
  | mul s t hs ht =>
    obtain ⟨ℓ₁, h₁⟩ := hs
    obtain ⟨ℓ₂, h₂⟩ := ht
    refine ⟨max ℓ₁ ℓ₂ + 1, fun A _ _ hn v => ?_⟩
    have e1 := (h₁ A hn v).trans (exp_mono hn (le_max_left ℓ₁ ℓ₂))
    have e2 := (h₂ A hn v).trans (exp_mono hn (le_max_right ℓ₁ ℓ₂))
    calc (mul s t).eval v = s.eval v * t.eval v := rfl
      _ ≤ 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂) * 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂) := Nat.mul_le_mul e1 e2
      _ = 2 ^ (Nat.card A ^ max ℓ₁ ℓ₂ + Nat.card A ^ max ℓ₁ ℓ₂) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (Nat.card A ^ (max ℓ₁ ℓ₂ + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (pow_add_pow_le hn _)
  | sum k t ht =>
    obtain ⟨ℓ, h⟩ := ht
    refine ⟨max k ℓ + 1, fun A _ _ hn v => ?_⟩
    let := Fintype.ofFinite A
    have hcard : (Finset.univ : Finset (Fin k → A)).card = Nat.card A ^ k := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
    calc (sum k t).eval v = ∑ u : Fin k → A, t.eval (Sum.elim v u) :=
          finsum_eq_sum_of_fintype _
      _ ≤ (Finset.univ : Finset (Fin k → A)).card • 2 ^ (Nat.card A ^ ℓ) :=
          Finset.sum_le_card_nsmul _ _ _ fun u _ => h A hn _
      _ = Nat.card A ^ k * 2 ^ (Nat.card A ^ ℓ) := by rw [hcard, smul_eq_mul]
      _ ≤ 2 ^ (Nat.card A ^ max k ℓ) * 2 ^ (Nat.card A ^ max k ℓ) :=
          Nat.mul_le_mul ((Nat.lt_two_pow_self (n := Nat.card A ^ k)).le.trans
            (exp_mono hn (le_max_left k ℓ))) (exp_mono hn (le_max_right k ℓ))
      _ = 2 ^ (Nat.card A ^ max k ℓ + Nat.card A ^ max k ℓ) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (Nat.card A ^ (max k ℓ + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (pow_add_pow_le hn _)
  | prod k t ht =>
    obtain ⟨ℓ, h⟩ := ht
    refine ⟨ℓ + k, fun A _ _ hn v => ?_⟩
    let := Fintype.ofFinite A
    have hcard : (Finset.univ : Finset (Fin k → A)).card = Nat.card A ^ k := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
    calc (prod k t).eval v = ∏ u : Fin k → A, t.eval (Sum.elim v u) :=
          finprod_eq_prod_of_fintype _
      _ ≤ (2 ^ (Nat.card A ^ ℓ)) ^ (Finset.univ : Finset (Fin k → A)).card :=
          Finset.prod_le_pow_card _ _ _ fun u _ => h A hn _
      _ = 2 ^ (Nat.card A ^ (ℓ + k)) := by rw [hcard, ← pow_mul, ← pow_add]

/-- **The value of a term has polynomially many digits**: it is below
`2 ^ (n ^ ℓ)` on the structures with `n ≥ 2` elements. -/
theorem exists_bound {α : Type} (t : QTerm L α) :
    ∃ ℓ : ℕ, ∀ (A : Type) [L.Structure A] [Finite A], 2 ≤ Nat.card A →
      ∀ v : α → A, t.eval v < 2 ^ (Nat.card A ^ ℓ) := by
  obtain ⟨ℓ, h⟩ := t.exists_bound_le
  refine ⟨ℓ + 1, fun A _ _ hn v => lt_of_le_of_lt (h A hn v) ?_⟩
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self ℓ))

/-! ### One-element structures -/

/-- **On one-element structures a term takes finitely many values, each
recognized by a formula.** -/
theorem exists_formulas {α : Type} (t : QTerm L α) :
    ∃ (M : ℕ) (χ : ℕ → L.Formula α), ∀ (A : Type) [L.Structure A] [Subsingleton A]
      [Nonempty A] (v : α → A), t.eval v ≤ M ∧ ∀ N, (χ N).Realize v ↔ t.eval v = N := by
  classical
  induction t with
  | ind φ =>
    refine ⟨1, fun N => if N = 1 then φ else if N = 0 then ∼φ else ⊥, fun A _ _ _ v => ?_⟩
    simp only [eval]
    refine ⟨by split_ifs <;> simp, fun N => ?_⟩
    by_cases h : φ.Realize v <;> rcases N with _ | _ | N <;> simp [h]
  | const s =>
    refine ⟨s, fun N => if N = s then ⊤ else ⊥, fun A _ _ _ v => ⟨le_rfl, fun N => ?_⟩⟩
    simp only [eval]
    by_cases h : N = s
    · simp [h]
    · rw [ite_eq_right h]
      exact iff_of_false id fun h' => h h'.symm
  | add s t hs ht =>
    obtain ⟨Ms, χs, hs⟩ := hs
    obtain ⟨Mt, χt, ht⟩ := ht
    refine ⟨Ms + Mt, fun N => listSup ((List.range (N + 1)).map fun i => χs i ⊓ χt (N - i)),
      fun A _ _ _ v => ⟨Nat.add_le_add (hs A v).1 (ht A v).1, fun N => ?_⟩⟩
    rw [realize_listSup]
    change _ ↔ s.eval v + t.eval v = N
    constructor
    · rintro ⟨φ, hφ, hr⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ
      have h1 := ((hs A v).2 i).mp (Formula.realize_inf.mp hr).1
      have h2 := ((ht A v).2 (N - i)).mp (Formula.realize_inf.mp hr).2
      have := List.mem_range.mp hi
      omega
    · intro h
      refine ⟨_, List.mem_map.mpr ⟨s.eval v, List.mem_range.mpr (by omega), rfl⟩,
        Formula.realize_inf.mpr ⟨((hs A v).2 _).mpr rfl, ((ht A v).2 _).mpr (by omega)⟩⟩
  | mul s t hs ht =>
    obtain ⟨Ms, χs, hs⟩ := hs
    obtain ⟨Mt, χt, ht⟩ := ht
    refine ⟨Ms * Mt, fun N => listSup ((List.range (Ms + 1)).map fun i =>
        listSup ((List.range (Mt + 1)).map fun j => if i * j = N then χs i ⊓ χt j else ⊥)),
      fun A _ _ _ v => ⟨Nat.mul_le_mul (hs A v).1 (ht A v).1, fun N => ?_⟩⟩
    rw [realize_listSup]
    change _ ↔ s.eval v * t.eval v = N
    constructor
    · rintro ⟨φ, hφ, hr⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ
      obtain ⟨ψ, hψ, hr'⟩ := (realize_listSup _).mp hr
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
      split_ifs at hr' with hij
      · rw [((hs A v).2 i).mp (Formula.realize_inf.mp hr').1,
          ((ht A v).2 j).mp (Formula.realize_inf.mp hr').2]
        exact hij
      · exact hr'.elim
    · intro h
      refine ⟨_, List.mem_map.mpr ⟨s.eval v,
        List.mem_range.mpr (Nat.lt_succ_of_le (hs A v).1), rfl⟩, ?_⟩
      refine (realize_listSup _).mpr ⟨_, List.mem_map.mpr ⟨t.eval v,
        List.mem_range.mpr (Nat.lt_succ_of_le (ht A v).1), rfl⟩, ?_⟩
      rw [ite_eq_left h]
      exact Formula.realize_inf.mpr ⟨((hs A v).2 _).mpr rfl, ((ht A v).2 _).mpr rfl⟩
  | sum n t ht =>
    obtain ⟨M, χ, h⟩ := ht
    refine ⟨M, fun N => Formula.iExs (Fin n) (χ N), fun A _ _ _ v => ?_⟩
    let : Unique (Fin n → A) :=
      ⟨⟨fun _ => Classical.arbitrary A⟩, fun _ => Subsingleton.elim _ _⟩
    have he : (sum n t).eval v = t.eval (Sum.elim v default) := finsum_unique _
    rw [he]
    refine ⟨(h A _).1, fun N => ?_⟩
    rw [Formula.realize_iExs]
    exact ⟨fun ⟨u, hu⟩ => ((h A _).2 N).mp (Unique.eq_default u ▸ hu),
      fun hN => ⟨default, ((h A _).2 N).mpr hN⟩⟩
  | prod n t ht =>
    obtain ⟨M, χ, h⟩ := ht
    refine ⟨M, fun N => Formula.iExs (Fin n) (χ N), fun A _ _ _ v => ?_⟩
    let : Unique (Fin n → A) :=
      ⟨⟨fun _ => Classical.arbitrary A⟩, fun _ => Subsingleton.elim _ _⟩
    have he : (prod n t).eval v = t.eval (Sum.elim v default) := finprod_unique _
    rw [he]
    refine ⟨(h A _).1, fun N => ?_⟩
    rw [Formula.realize_iExs]
    exact ⟨fun ⟨u, hu⟩ => ((h A _).2 N).mp (Unique.eq_default u ▸ hu),
      fun hN => ⟨default, ((h A _).2 N).mpr hN⟩⟩

end QTerm

end DescriptiveComplexity
