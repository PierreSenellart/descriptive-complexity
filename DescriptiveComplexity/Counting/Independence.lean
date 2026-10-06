/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod

/-!
# Weighted counts of independent events

The computations with weighted counts
(`DescriptiveComplexity.weightedCount`) that make a query *safe*: its weighted
count, a sum over exponentially many valuations, is a product and a sum over
the variables.

* `DescriptiveComplexity.weightedCount_forall`: an event that constrains each
  variable separately has a product as weighted count.
* `DescriptiveComplexity.weightedCount_sum_type`: conditioning on the values of
  one group of variables.
* `DescriptiveComplexity.weightedCount_add_not`: an event and its complement
  share the total weight.
* `DescriptiveComplexity.prod_add_eq_prod_add_sum`: the *first success*
  identity. With `F i` the weight of a failure at `i` and `S i` that of a
  success, the total weight `∏ (F i + S i)` is the weight `∏ F i` of failing
  everywhere, plus, for each `i`, the weight of failing before `i`, succeeding
  at `i`, and doing anything after. It turns the difference
  `∏ (F i + S i) - ∏ F i`, the weight of succeeding somewhere, into a sum of
  products: no subtraction is left, which is what a quantitative term needs.
-/

namespace DescriptiveComplexity

section Independent

variable {X : Type} [Fintype X] [DecidableEq X] (a c : X → ℕ)

/-- **An event and its complement share the total weight.** -/
theorem weightedCount_add_not (f : (X → Bool) → Bool) :
    weightedCount a c f + weightedCount a c (fun v => !f v) = ∏ x, (a x + c x) := by
  rw [← weightedCount_true a c, weightedCount, weightedCount, weightedCount,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases f v <;> simp

/-- **An event constraining each variable separately**: its weighted count is
the product, over the variables, of the weights of the values it allows. -/
theorem weightedCount_forall (ok : X → Bool → Bool) :
    weightedCount a c (fun v => decide (∀ x, ok x (v x) = true)) =
      ∏ x, ((if ok x true then a x else 0) + (if ok x false then c x else 0)) := by
  have hps := Fintype.prod_sum fun (x : X) (b : Bool) =>
    if ok x b then (if b then a x else c x) else 0
  have hl : ∀ x : X, (∑ b : Bool, if ok x b then (if b then a x else c x) else 0) =
      (if ok x true then a x else 0) + (if ok x false then c x else 0) := fun x => by
    rw [Fintype.sum_bool]
    simp
  rw [← Finset.prod_congr rfl fun x _ => hl x, hps, weightedCount]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : ∀ x, ok x (v x) = true
  · rw [ite_eq_left (decide_eq_true hv), valWeight]
    exact Finset.prod_congr rfl fun x _ => (ite_eq_left (hv x)).symm
  · rw [ite_eq_right (by simpa using hv)]
    obtain ⟨x, hx⟩ := not_forall.mp hv
    exact (Finset.prod_eq_zero (Finset.mem_univ x) (ite_eq_right hx)).symm

/-- **Conditioning on a group of variables**: the weighted count over two
groups is the sum, over the valuations of the first, of their weight times the
weighted count over the second. -/
theorem weightedCount_sum_type {Y : Type} [Fintype Y] [DecidableEq Y] (a' c' : Y → ℕ)
    (f : (X ⊕ Y → Bool) → Bool) :
    weightedCount (Sum.elim a a') (Sum.elim c c') f =
      ∑ vX : X → Bool, valWeight a c vX *
        weightedCount a' c' (fun vY => f (Sum.elim vX vY)) := by
  rw [weightedCount, ← Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow X Y Bool).symm
    (fun p : (X → Bool) × (Y → Bool) =>
      if f (Sum.elim p.1 p.2) then valWeight a c p.1 * valWeight a' c' p.2 else 0) _
    (fun p => by
      have hw : valWeight (Sum.elim a a') (Sum.elim c c')
          ((Equiv.sumArrowEquivProdArrow X Y Bool).symm p) =
          valWeight a c p.1 * valWeight a' c' p.2 := by
        rw [valWeight, Fintype.prod_sum_type]
        rfl
      rw [hw]
      rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun vX _ => ?_
  rw [weightedCount, Finset.mul_sum]
  exact Finset.sum_congr rfl fun vY _ => by split_ifs <;> simp

/-- Weighted counts do not depend on how the variables are named. -/
theorem weightedCount_equiv {X' : Type} [Fintype X'] [DecidableEq X'] (e : X' ≃ X)
    (f : (X → Bool) → Bool) :
    weightedCount a c f =
      weightedCount (fun x => a (e x)) (fun x => c (e x)) (fun v => f fun x => v (e.symm x)) := by
  rw [weightedCount, weightedCount]
  refine (Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
    _ _ fun v => ?_).symm
  have hv : (fun x => v (e.symm x)) = Equiv.arrowCongr e (Equiv.refl Bool) v := rfl
  rw [hv, valWeight, valWeight]
  refine if_congr Iff.rfl (Fintype.prod_equiv e _ _ fun x => ?_) rfl
  simp [Equiv.arrowCongr]

end Independent

/-! ### First success -/

/-- **The first success identity**: the total weight is the weight of failing
everywhere, plus the weights of failing before an index, succeeding at it, and
doing anything after. -/
theorem prod_add_eq_prod_add_sum {I : Type} [Fintype I] [LinearOrder I] (F S : I → ℕ) :
    ∏ i, (F i + S i) = ∏ i, F i +
      ∑ i, (∏ j ∈ Finset.univ.filter (· < i), F j) * S i *
        ∏ j ∈ Finset.univ.filter (i < ·), (F j + S j) := by
  have key : ∀ s : Finset I, ∏ i ∈ s, (F i + S i) = ∏ i ∈ s, F i +
      ∑ i ∈ s, (∏ j ∈ s.filter (· < i), F j) * S i *
        ∏ j ∈ s.filter (i < ·), (F j + S j) := by
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert m s hm ih =>
      have hms : m ∉ s := fun h => lt_irrefl m (hm m h)
      have hlt : (insert m s).filter (· < m) = s := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        exact ⟨fun h => h.1.resolve_left (ne_of_lt h.2), fun h => ⟨Or.inr h, hm x h⟩⟩
      have hgt : (insert m s).filter (m < ·) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false,
          not_and, not_lt]
        rintro (rfl | h)
        · exact le_rfl
        · exact (hm x h).le
      have hi : ∀ i ∈ s, (∏ j ∈ (insert m s).filter (· < i), F j) * S i *
          ∏ j ∈ (insert m s).filter (i < ·), (F j + S j) =
          ((∏ j ∈ s.filter (· < i), F j) * S i * ∏ j ∈ s.filter (i < ·), (F j + S j)) *
            (F m + S m) := by
        intro i his
        have h1 : (insert m s).filter (· < i) = s.filter (· < i) := by
          rw [Finset.filter_insert, ite_eq_right (not_lt.mpr (hm i his).le)]
        have h2 : (insert m s).filter (i < ·) = insert m (s.filter (i < ·)) := by
          rw [Finset.filter_insert, ite_eq_left (hm i his)]
        rw [h1, h2, Finset.prod_insert (fun h => hms (Finset.mem_filter.mp h).1)]
        ring
      rw [Finset.prod_insert hms, Finset.prod_insert hms, Finset.sum_insert hms, hlt, hgt,
        Finset.prod_empty, Finset.sum_congr rfl hi, ← Finset.sum_mul, ih]
      ring
  simpa using key Finset.univ

end DescriptiveComplexity
