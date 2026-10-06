/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Ladder
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# From an integer matrix to a 0-1 matrix, modulo `2 ^ L + 1`

The matrix a gadget argument produces has small integer entries, some of
them negative; a 0-1 matrix with the same permanent modulo `2 ^ L + 1` is
its ladder expansion (`DescriptiveComplexity.ladder`) with the **widths**
`DescriptiveComplexity.widths`: an entry `-1` becomes a ladder of `L` levels
of two rungs, i.e., `2 ^ L ≡ -1`, and an entry `k ≥ 0` a ladder whose least
level has `k` rungs and the others one
(`DescriptiveComplexity.bperm_ladder_widths_modEq`). When the permanent is
known to be `4 ^ t * N` with `4 ^ t * N ≤ 2 ^ L`, the count `N` is read off
the permanent of the 0-1 matrix by a remainder and a quotient
(`DescriptiveComplexity.bperm_ladder_widths_div`): the arithmetic the one-call
reduction to #Cycle Cover applies to the answer of its oracle.
-/

namespace DescriptiveComplexity

open Finset

section Widths

variable {V Λ : Type} [Fintype V] [DecidableEq V] [LinearOrder Λ] [Fintype Λ] [BoundedOrder Λ]

/-- **The widths of the ladders of an integer matrix**: two rungs at every
level for an entry `-1`; for an entry `k ≥ 0`, `k` rungs at the least level
and one at every other. -/
def widths (M : V → V → ℤ) (a b : V) (ℓ : Λ) : ℕ :=
  if M a b = -1 then 2 else if ℓ = ⊥ then (M a b).toNat else 1

omit [Fintype V] [DecidableEq V] in
omit [Fintype Λ] in
theorem widths_le (M : V → V → ℤ) (hM : ∀ a b, M a b ≤ 3) (a b : V) (ℓ : Λ) :
    widths M a b ℓ ≤ 3 := by
  unfold widths
  split_ifs
  · omega
  · exact Int.toNat_le.mpr (hM a b)
  · omega

omit [Fintype V] [DecidableEq V] in
/-- The product of the widths along a ladder: `2 ^ L` for an entry `-1`, the
entry otherwise. -/
theorem prod_widths (M : V → V → ℤ) (a b : V) :
    ∏ ℓ : Λ, widths M a b ℓ = if M a b = -1 then 2 ^ Fintype.card Λ else (M a b).toNat := by
  unfold widths
  split_ifs with h
  · rw [prod_const, card_univ]
  · rw [Fintype.prod_eq_single ⊥ fun ℓ hℓ => by rw [if_neg hℓ], if_pos rfl]

omit [Fintype V] [DecidableEq V] in
/-- The product of the widths is congruent to the entry modulo `2 ^ L + 1`,
for an entry at least `-1`. -/
theorem prod_widths_modEq (M : V → V → ℤ) (a b : V) (hM : -1 ≤ M a b) :
    ((∏ ℓ : Λ, widths M a b ℓ : ℕ) : ℤ) ≡ M a b [ZMOD 2 ^ Fintype.card Λ + 1] := by
  rw [prod_widths]
  split_ifs with h
  · rw [h]
    push_cast
    exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  · rw [Int.toNat_of_nonneg (by omega)]

/-- **The permanent of the 0-1 ladder expansion is congruent to the permanent
of the integer matrix** modulo `2 ^ L + 1`, for entries between `-1` and
`3`. -/
theorem bperm_ladder_widths_modEq (M : V → V → ℤ) (hM : ∀ a b, -1 ≤ M a b ∧ M a b ≤ 3) :
    ((bperm (ladder 3 (widths (Λ := Λ) M)) : ℕ) : ℤ) ≡ bperm M [ZMOD 2 ^ Fintype.card Λ + 1] := by
  rw [bperm_ladder (widths_le M fun a b => (hM a b).2), bperm_natCast]
  exact bperm_modEq _ _ _ fun a b => prod_widths_modEq M a b (hM a b).1

/-- **The count is read off the permanent of the 0-1 matrix**: when the
permanent of the integer matrix is `4 ^ t * N` with `4 ^ t * N ≤ 2 ^ L`, the
permanent of the ladder expansion, modulo `2 ^ L + 1` and divided by `4 ^ t`,
is `N`. -/
theorem bperm_ladder_widths_div (M : V → V → ℤ) (hM : ∀ a b, -1 ≤ M a b ∧ M a b ≤ 3) (t N : ℕ)
    (hperm : bperm M = 4 ^ t * (N : ℤ)) (hlt : 4 ^ t * N ≤ 2 ^ Fintype.card Λ) :
    bperm (ladder 3 (widths (Λ := Λ) M)) % (2 ^ Fintype.card Λ + 1) / 4 ^ t = N := by
  have h := bperm_ladder_widths_modEq (Λ := Λ) M hM
  rw [hperm] at h
  have hlt' : (4 : ℤ) ^ t * N < 2 ^ Fintype.card Λ + 1 := by
    have := Nat.lt_succ_of_le hlt
    exact_mod_cast this
  have h' : ((bperm (ladder 3 (widths (Λ := Λ) M)) : ℕ) : ℤ) % (2 ^ Fintype.card Λ + 1) =
      4 ^ t * N := by
    rw [show ((bperm (ladder 3 (widths (Λ := Λ) M)) : ℕ) : ℤ) % (2 ^ Fintype.card Λ + 1) =
      (4 ^ t * (N : ℤ)) % (2 ^ Fintype.card Λ + 1) from h]
    exact Int.emod_eq_of_lt (by positivity) hlt'
  have h'' : bperm (ladder 3 (widths (Λ := Λ) M)) % (2 ^ Fintype.card Λ + 1) = 4 ^ t * N := by
    exact_mod_cast h'
  rw [h'', Nat.mul_div_cancel_left _ (by positivity)]

end Widths

end DescriptiveComplexity
