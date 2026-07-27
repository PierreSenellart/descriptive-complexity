/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Analysis.SpecificLimits.Normed
import DescriptiveComplexity.Encoding
import DescriptiveComplexity.Problems.Knapsack.Defs

/-!
# The size bounds have teeth: unary encodings are rejected

A criterion nobody can fail is worth nothing. This file proves that the
`card_le` bound of `DescriptiveComplexity.Encoding` genuinely rejects the one
mistake the library worries about most (`ROADMAP.md` §0): encoding a number in
*unary* – as the cardinality of a marked set – when the honest size of the
instance counts its *bit length*. Under a unary encoding a subset-sum instance
sits on a universe exponential in its own size, and the NP-hardness of the
weighted problems of the catalog (Knapsack, Partition, Job Sequencing, 0-1
Integer Programming) would silently evaporate.

* `DescriptiveComplexity.no_unary_encoding`: there is **no** encoding of
  subset-sum instances, sized by bit length, whose universe holds one element
  per unit of weight. The witness family is `([2 ^ k], 2 ^ k)`, of size
  `Θ(k)`: a unary universe on it is exponential in the declared size, so
  `card_le` cannot be discharged.
* `DescriptiveComplexity.binarySubsetSumEncoding`: the honest *binary*
  encoding of the same instance type (representation (C): items and bit
  positions, a `bit` relation) satisfies both bounds with room to spare.

Together they turn the prose lesson of `ROADMAP.md` §0 – unary versus binary
genuinely changes the problem – into a theorem.

This file is deliberately off the library's core import path: the negative
result needs a little asymptotics (`Mathlib.Analysis.SpecificLimits.Normed`),
which the core does not otherwise pull in.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- A concrete subset-sum instance: a list of weights and a target. -/
abbrev SubsetSumInstance : Type := List ℕ × ℕ

/-- The honest size of a subset-sum instance: the total *bit length* of its
weights and of its target, plus the number of items (so that zero weights
still take room). An encoding sized this way must represent weights in
binary or violate `card_le`. -/
def ssSize : SubsetSumInstance → ℕ := fun i =>
  (i.1.map Nat.size).sum + Nat.size i.2 + i.1.length

/-- Exponential beats polynomial, in the pointed form the negative example
needs: some `k` has `c * (2 * k + 4) ^ d < 2 ^ k`. -/
theorem exists_mul_pow_lt_two_pow (c d : ℕ) :
    ∃ k : ℕ, c * (2 * k + 4) ^ d < 2 ^ k := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d
      one_lt_two).def (c := 1 / ((c : ℝ) * 3 ^ d + 1)) (by positivity))
  refine ⟨max N 4, ?_⟩
  set k := max N 4 with hkdef
  have h4 : 4 ≤ k := le_max_right _ _
  have hreal := hN k (le_max_left _ _)
  simp only [norm_pow, Real.norm_natCast, Real.norm_ofNat] at hreal
  have hM : (0 : ℝ) ≤ (c : ℝ) * 3 ^ d := by positivity
  have hstep : ((c : ℝ) * 3 ^ d) * (k : ℝ) ^ d < 2 ^ k := by
    calc ((c : ℝ) * 3 ^ d) * (k : ℝ) ^ d
        ≤ ((c : ℝ) * 3 ^ d) * (1 / ((c : ℝ) * 3 ^ d + 1) * 2 ^ k) :=
          mul_le_mul_of_nonneg_left hreal hM
      _ = ((c : ℝ) * 3 ^ d) / ((c : ℝ) * 3 ^ d + 1) * 2 ^ k := by ring
      _ < 1 * 2 ^ k := by
          refine mul_lt_mul_of_pos_right ?_ (by positivity)
          rw [div_lt_one (by positivity)]
          linarith
      _ = 2 ^ k := one_mul _
  have hnat : c * (2 * k + 4) ^ d ≤ c * 3 ^ d * k ^ d := by
    have h3 : 2 * k + 4 ≤ 3 * k := by omega
    calc c * (2 * k + 4) ^ d
        ≤ c * (3 * k) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left h3 d)
      _ = c * 3 ^ d * k ^ d := by rw [mul_pow, mul_assoc]
  have hcast : (↑(c * (2 * k + 4) ^ d) : ℝ) < ↑(2 ^ k : ℕ) := by
    push_cast
    calc (c : ℝ) * (2 * (k : ℝ) + 4) ^ d
        ≤ (c : ℝ) * 3 ^ d * (k : ℝ) ^ d := by exact_mod_cast hnat
      _ < 2 ^ k := hstep
  exact_mod_cast hcast

/-- **No unary encoding**: no encoding of subset-sum instances, sized by bit
length, can have a universe holding one element per unit of weight – the
no-padding bound `card_le` fails on the family `([2 ^ k], 2 ^ k)`. This is
the theorem that gives the size discipline of `Encoding` its teeth: the
representation choice that unary-vs-binary prose warns about is now a proof
that does not close. -/
theorem no_unary_encoding :
    ¬ ∃ e : Encoding Language.binWeights SubsetSumInstance,
        e.size = ssSize ∧ ∀ i : SubsetSumInstance, i.1.sum ≤ Nat.card (e.Univ i) := by
  rintro ⟨e, hsize, huniv⟩
  obtain ⟨c, d, hcd⟩ := e.card_le
  obtain ⟨k, hk⟩ := exists_mul_pow_lt_two_pow c d
  have h1 := hcd ([2 ^ k], 2 ^ k)
  rw [hsize] at h1
  have hs : ssSize ([2 ^ k], 2 ^ k) = 2 * k + 3 := by
    simp only [ssSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, Nat.size_pow]
    omega
  rw [hs] at h1
  have h2 : 2 ^ k ≤ Nat.card (e.Univ ([2 ^ k], 2 ^ k)) := by
    simpa using huniv ([2 ^ k], 2 ^ k)
  have hcontr : 2 ^ k ≤ c * (2 * k + 4) ^ d := by
    have h4 : 2 * k + 3 + 1 = 2 * k + 4 := by omega
    rw [h4] at h1
    exact h2.trans h1
  exact absurd hcontr (not_le.mpr hk)

/-- The positive counterpart: the honest **binary** encoding of subset-sum
instances – one element per item, one element per bit position, `bit` and
`tgt` reading the binary digits, place values carried by the order – passes
both size bounds with room to spare. (Only the size discipline is at stake
here, so no semantic theorem accompanies this encoding; the catalog's
Knapsack development is where `Language.binWeights` structures get their
semantics.) -/
def binarySubsetSumEncoding : Encoding Language.binWeights SubsetSumInstance where
  size := ssSize
  Univ := fun i => Fin i.1.length ⊕ Fin (ssSize i + 1)
  deceq := fun _ => inferInstance
  fintype := fun _ => inferInstance
  relBool := fun i {n} R =>
    match n, R with
    | _, .item => fun x => (x 0).isLeft
    | _, .posn => fun x => (x 0).isRight
    | _, .bit => fun x =>
      match x 0, x 1 with
      | Sum.inl j, Sum.inr p => (i.1.get j).testBit p.1
      | _, _ => false
    | _, .tgt => fun x =>
      match x 0 with
      | Sum.inr p => i.2.testBit p.1
      | _ => false
    | _, .le => fun x =>
      match x 0, x 1 with
      | Sum.inl j, Sum.inl j' => decide (j ≤ j')
      | Sum.inl _, Sum.inr _ => true
      | Sum.inr _, Sum.inl _ => false
      | Sum.inr p, Sum.inr p' => decide (p ≤ p')
  card_le := Encoding.linear_bound (c := 2) fun i => by
    have hlen : i.1.length ≤ ssSize i := by
      simp only [ssSize]
      omega
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega
  le_card := Encoding.linear_bound (c := 1) fun i => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega

end DescriptiveComplexity
