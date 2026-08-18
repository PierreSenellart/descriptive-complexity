/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity

/-!
# Truncated distances, and the duplicator's answer on a line

The arithmetic core of the Ehrenfeucht–Fraïssé game on linear orders
([Ehrenfeucht 1961][ehrenfeucht1961application];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 2): no logic and no game
here, only integers.

The duplicator's invariant on a line is the classical one – corresponding
points are at equal distance, *or* at distance at least `2 ^ n` on both sides,
where `n` is the number of rounds still to play. Written with the truncation
`DescriptiveComplexity.truncAt n` – clamping to `[-2 ^ n, 2 ^ n]` – the two
alternatives, the order between the points and the case of equal points all
become the single equation `truncAt n (x - y) = truncAt n (x' - y')`
(`DescriptiveComplexity.truncAt_eq_iff`), which is what makes the invariant
manageable: one clause instead of four.

The theorem of the file is `DescriptiveComplexity.exists_answer`: from an
invariant with `n + 1` rounds to spare, any point the spoiler picks between
two existing points can be answered so that the invariant holds with `n`
rounds. Its proof is the textbook case analysis – copy the distance to the
left neighbour, or to the right one, or, when both are large, land in the
middle of a gap that the invariant guarantees is twice as large on the other
side – with the halving of the budget appearing exactly there.
-/

namespace DescriptiveComplexity

/-! ### Truncation -/

/-- The distance truncated at `2 ^ n`: an integer clamped to
`[-2 ^ n, 2 ^ n]`. Two truncated distances are equal exactly when the
distances are equal or both beyond the truncation, on the same side
(`DescriptiveComplexity.truncAt_eq_iff`). -/
def truncAt (n : ℕ) (x : ℤ) : ℤ :=
  max (-(2 ^ n)) (min (2 ^ n) x)

variable {n : ℕ} {x y : ℤ}

theorem two_pow_pos (n : ℕ) : (0 : ℤ) < 2 ^ n := by positivity

/-- Truncation is the identity within the bounds. -/
theorem truncAt_of_abs_le (h₁ : -(2 ^ n) ≤ x) (h₂ : x ≤ 2 ^ n) : truncAt n x = x := by
  simp only [truncAt, min_eq_right h₂, max_eq_right h₁]

/-- Truncation is `2 ^ n` above the bound. -/
theorem truncAt_of_le (h : 2 ^ n ≤ x) : truncAt n x = 2 ^ n := by
  have := two_pow_pos n
  simp only [truncAt, min_eq_left h]
  omega

/-- Truncation is `-2 ^ n` below the bound. -/
theorem truncAt_of_le_neg (h : x ≤ -(2 ^ n)) : truncAt n x = -(2 ^ n) := by
  have := two_pow_pos n
  simp only [truncAt, min_eq_right (by omega : (2 : ℤ) ^ n ≥ x)]
  omega

/-- **The characterization of equal truncated distances**: equal distances, or
both beyond the truncation on the same side. Every property of the
duplicator's invariant is read off this. -/
theorem truncAt_eq_iff : truncAt n x = truncAt n y ↔
    x = y ∨ (2 ^ n ≤ x ∧ 2 ^ n ≤ y) ∨ (x ≤ -(2 ^ n) ∧ y ≤ -(2 ^ n)) := by
  have hpos := two_pow_pos n
  constructor
  · intro h
    rcases le_or_gt (2 ^ n) x with hx | hx
    · rcases le_or_gt (2 ^ n) y with hy | hy
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
      · rw [truncAt_of_le hx] at h
        rcases le_or_gt y (-(2 ^ n)) with hy' | hy'
        · rw [truncAt_of_le_neg hy'] at h; omega
        · rw [truncAt_of_abs_le (by omega) (by omega)] at h; omega
    · rcases le_or_gt x (-(2 ^ n)) with hx' | hx'
      · rw [truncAt_of_le_neg hx'] at h
        rcases le_or_gt y (-(2 ^ n)) with hy' | hy'
        · exact Or.inr (Or.inr ⟨hx', hy'⟩)
        · rcases le_or_gt (2 ^ n) y with hy | hy
          · rw [truncAt_of_le hy] at h; omega
          · rw [truncAt_of_abs_le (by omega) (by omega)] at h; omega
      · rw [truncAt_of_abs_le (by omega) (by omega)] at h
        rcases le_or_gt (2 ^ n) y with hy | hy
        · rw [truncAt_of_le hy] at h; omega
        · rcases le_or_gt y (-(2 ^ n)) with hy' | hy'
          · rw [truncAt_of_le_neg hy'] at h; omega
          · rw [truncAt_of_abs_le (by omega) (by omega)] at h; omega
  · rintro (rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · rfl
    · rw [truncAt_of_le hx, truncAt_of_le hy]
    · rw [truncAt_of_le_neg hx, truncAt_of_le_neg hy]

/-! ### What an equation between truncated distances says -/

/-- Equal truncated distances have the same sign, weakly. -/
theorem le_zero_congr_of_truncAt (h : truncAt n x = truncAt n y) : x ≤ 0 ↔ y ≤ 0 := by
  have hpos := two_pow_pos n
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> constructor <;> intro <;> omega

/-- Equal truncated distances have the same strict sign. -/
theorem lt_zero_congr_of_truncAt (h : truncAt n x = truncAt n y) : x < 0 ↔ y < 0 := by
  have hpos := two_pow_pos n
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> constructor <;> intro <;> omega

/-- Truncation commutes with negation, as an equation between two
distances. -/
theorem neg_congr_of_truncAt (h : truncAt n x = truncAt n y) :
    truncAt n (-x) = truncAt n (-y) := by
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rfl
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩))

/-- Equal truncated distances are zero together. -/
theorem eq_zero_congr_of_truncAt (h : truncAt n x = truncAt n y) : x = 0 ↔ y = 0 := by
  have hpos := two_pow_pos n
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> constructor <;> intro <;> omega

/-- **Truncating further is coarser**: an equation between distances
truncated at `2 ^ n` survives truncation at any smaller bound. This is how a
round is spent – the budget halves, and the invariant still holds. -/
theorem truncAt_eq_of_le {m : ℕ} (hmn : m ≤ n) (h : truncAt n x = truncAt n y) :
    truncAt m x = truncAt m y := by
  have hmono : (2 : ℤ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hmn
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rfl
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inl ⟨le_trans hmono hx, le_trans hmono hy⟩))
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inr ⟨le_trans hx (by omega), le_trans hy (by omega)⟩))

/-- **Shifting both sides by a small amount costs one round**: two distances
equal up to truncation at `2 ^ (n + 1)` stay equal up to truncation at
`2 ^ n` after a common shift of at most `2 ^ n`. This single lemma answers
the spoiler in the two easy cases of
`DescriptiveComplexity.exists_answer` – the shift being the distance from the
new point to the neighbour the duplicator copies. -/
theorem truncAt_sub_shift {s : ℤ} (h : truncAt (n + 1) x = truncAt (n + 1) y)
    (hs₁ : -(2 ^ n) ≤ s) (hs₂ : s ≤ 2 ^ n) : truncAt n (x - s) = truncAt n (y - s) := by
  have hpow : (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
  rcases truncAt_eq_iff.mp h with rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rfl
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact truncAt_eq_iff.mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))

/-! ### The duplicator's answer -/

/-- **The duplicator answers on a line.** Two families of integers whose
mutual distances agree up to truncation at `2 ^ (n + 1)`, and a new point `c`
lying between two points of the first family: then there is a point `d`
answering it, whose distances to the second family agree, up to truncation at
`2 ^ n`, with those of `c` to the first.

The three cases are the classical ones: if `c` is one of the existing points,
copy the corresponding one; if `c` is closer than `2 ^ n` to its left or right
neighbour, copy that distance (`DescriptiveComplexity.truncAt_sub_shift`);
and if it is far from both, the gap it sits in is at least `2 ^ (n + 1)` wide,
hence so is the corresponding gap, and there is room to land at exactly
`2 ^ n` from the left neighbour. -/
theorem exists_answer {ι : Type} [Finite ι] {U V : ι → ℤ}
    (hinv : ∀ i i', truncAt (n + 1) (U i - U i') = truncAt (n + 1) (V i - V i'))
    {c : ℤ} {i₀ i₁ : ι} (h₀ : U i₀ ≤ c) (h₁ : c ≤ U i₁) :
    ∃ d : ℤ, ∀ i, truncAt n (U i - c) = truncAt n (V i - d) := by
  classical
  letI := Fintype.ofFinite ι
  have hpos := two_pow_pos n
  by_cases hmem : ∃ i, U i = c
  · obtain ⟨i₂, hi₂⟩ := hmem
    refine ⟨V i₂, fun i => ?_⟩
    rw [← hi₂]
    exact truncAt_eq_of_le (Nat.le_succ n) (hinv i i₂)
  -- `c` is inside a gap: take its two neighbours
  have hne : ∀ i, U i ≠ c := fun i hi => hmem ⟨i, hi⟩
  have hlo : (Finset.univ.filter fun i => U i < c).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne h₀ (hne i₀)⟩⟩
  have hhi : (Finset.univ.filter fun i => c < U i).Nonempty :=
    ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne h₁ (Ne.symm (hne i₁))⟩⟩
  obtain ⟨im, hmmem, hmax⟩ := Finset.exists_max_image _ U hlo
  obtain ⟨ip, hpmem, hmin⟩ := Finset.exists_min_image _ U hhi
  have hm : U im < c := (Finset.mem_filter.mp hmmem).2
  have hp : c < U ip := (Finset.mem_filter.mp hpmem).2
  -- every point of the family lies outside the gap
  have hgap : ∀ i, U i ≤ U im ∨ U ip ≤ U i := by
    intro i
    rcases lt_trichotomy (U i) c with hi | hi | hi
    · exact Or.inl (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    · exact absurd hi (hne i)
    · exact Or.inr (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
  rcases lt_or_ge (c - U im) (2 ^ n) with hleft | hleft
  · -- close to the left neighbour: copy the distance
    refine ⟨V im + (c - U im), fun i => ?_⟩
    have := truncAt_sub_shift (hinv i im) (s := c - U im) (by omega) (by omega)
    have heq₁ : U i - U im - (c - U im) = U i - c := by omega
    have heq₂ : V i - V im - (c - U im) = V i - (V im + (c - U im)) := by omega
    rwa [heq₁, heq₂] at this
  rcases lt_or_ge (U ip - c) (2 ^ n) with hright | hright
  · -- close to the right neighbour: copy the distance
    refine ⟨V ip - (U ip - c), fun i => ?_⟩
    have := truncAt_sub_shift (hinv i ip) (s := -(U ip - c)) (by omega) (by omega)
    have heq₁ : U i - U ip - -(U ip - c) = U i - c := by omega
    have heq₂ : V i - V ip - -(U ip - c) = V i - (V ip - (U ip - c)) := by omega
    rwa [heq₁, heq₂] at this
  · -- far from both: the gap is wide on both sides, so land in the middle
    have hwide : (2 : ℤ) ^ (n + 1) ≤ U ip - U im := by
      have : (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      omega
    have hwide' : (2 : ℤ) ^ (n + 1) ≤ V ip - V im := by
      rcases truncAt_eq_iff.mp (hinv ip im) with heq | ⟨_, hy⟩ | ⟨hx, _⟩
      · omega
      · exact hy
      · have : (0 : ℤ) < 2 ^ (n + 1) := two_pow_pos (n + 1)
        omega
    refine ⟨V im + 2 ^ n, fun i => ?_⟩
    have hpow : (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    rcases hgap i with hi | hi
    · -- to the left of the gap: both distances are beyond the truncation
      have hVi : V i - V im ≤ 0 :=
        (le_zero_congr_of_truncAt (hinv i im)).mp (by omega)
      rw [truncAt_of_le_neg (by omega), truncAt_of_le_neg (by omega)]
    · -- to the right of the gap
      have hVi : 0 ≤ V i - V ip := by
        have h' := (le_zero_congr_of_truncAt (hinv ip i)).mp (by omega)
        omega
      rw [truncAt_of_le (by omega), truncAt_of_le (by omega)]

end DescriptiveComplexity
