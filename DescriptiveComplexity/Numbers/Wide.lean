/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel

/-!
# Wide numbers: sums that no longer fit in the instance's own positions

A binary-weighted instance carries a set of bit positions, and each weight is
a number below `2 ^ n` for `n` the number of positions
(`DescriptiveComplexity.binNum_lt_two_pow`). A *sum* of such weights need not be:
`m` items of `n` bits reach `m · 2 ^ n`. For Knapsack that costs nothing – the
sum is required to equal the target, which is itself an `n`-bit number, so
every running total along the way is below `2 ^ n`. For Partition it is fatal:
each half is `total / 2`, which may well exceed every number the instance can
write, so a certificate carrying the running totals *on the positions* would
not exist even for yes-instances.

This file widens the representation. Bit positions become *pairs*, ordered
with the first coordinate major:

* `DescriptiveComplexity.WidePosn`: the pairs whose second coordinate is a position –
  `|A| · n` of them, enough room for any sum of the instance's weights
  (`DescriptiveComplexity.finsum_binNum_lt_wide`);
* `DescriptiveComplexity.wideLe`: the lexicographic order, first coordinate major,
  which makes the pairs `(⊥, p)` the *lowest* `n` positions, with the same
  ranks as the positions `p` themselves (`DescriptiveComplexity.bitRank_wide`), so
  that a weight is read unchanged in the wide representation
  (`DescriptiveComplexity.binNum_wide`).

Everything else – the ripple-carry lemmas of
`DescriptiveComplexity.Numbers.BinRel` – applies verbatim at the pair type, being
stated for an arbitrary relation on an arbitrary finite type. What the
first-order layer needs on top is the translation of the walk along the wide
positions into two coordinates, which is `DescriptiveComplexity.minPos_wide`,
`DescriptiveComplexity.maxPos_wide` and `DescriptiveComplexity.succPos_wide`.
-/

namespace DescriptiveComplexity

section Wide

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- The positions of the wide representation: pairs whose second coordinate is
a position of the instance. -/
def WidePosn (Posn : A → Prop) : A × A → Prop := fun u => Posn u.2

/-- The order of the wide representation: lexicographic, first coordinate
major. -/
def wideLe (Le : A → A → Prop) : A × A → A × A → Prop := fun u v =>
  (Le u.1 v.1 ∧ u.1 ≠ v.1) ∨ (u.1 = v.1 ∧ Le u.2 v.2)

omit [Finite A] in
/-- The wide order is a linear order. -/
theorem isLinOrd_wideLe (hlin : IsLinOrd Le) : IsLinOrd (wideLe Le) := by
  refine ⟨fun u => Or.inr ⟨rfl, hlin.1 _⟩, fun u v w h₁ h₂ => ?_, fun u v h₁ h₂ => ?_,
    fun u v => ?_⟩
  · rcases h₁ with ⟨h, hne⟩ | ⟨he, h⟩ <;> rcases h₂ with ⟨h', hne'⟩ | ⟨he', h'⟩
    · exact Or.inl ⟨hlin.2.1 _ _ _ h h', fun hcon => hne (hlin.2.2.1 _ _ h (hcon ▸ h'))⟩
    · exact Or.inl ⟨he' ▸ h, he' ▸ hne⟩
    · exact Or.inl ⟨he ▸ h', fun hcon => hne' (he ▸ hcon)⟩
    · exact Or.inr ⟨he.trans he', hlin.2.1 _ _ _ h h'⟩
  · rcases h₁ with ⟨h, hne⟩ | ⟨he, h⟩ <;> rcases h₂ with ⟨h', hne'⟩ | ⟨he', h'⟩
    · exact absurd (hlin.2.2.1 _ _ h h') hne
    · exact absurd he'.symm hne
    · exact absurd he.symm hne'
    · exact Prod.ext_iff.mpr ⟨he, hlin.2.2.1 _ _ h h'⟩
  · rcases eq_or_ne u.1 v.1 with he | hne
    · rcases hlin.2.2.2 u.2 v.2 with h | h
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr (Or.inr ⟨he.symm, h⟩)
    · rcases hlin.2.2.2 u.1 v.1 with h | h
      · exact Or.inl (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inl ⟨h, hne.symm⟩)

omit [Finite A] in
/-- **The instance's positions sit at the bottom of the wide ones**, with
unchanged ranks: a weight means the same number read either way. -/
theorem bitRank_wide (hlin : IsLinOrd Le) {a₀ : A} (h₀ : ∀ x, Le a₀ x) (p : A) :
    bitRank (wideLe Le) (WidePosn Posn) (a₀, p) = bitRank Le Posn p := by
  have hset : {u : A × A | WidePosn Posn u ∧ wideLe Le u (a₀, p) ∧ u ≠ (a₀, p)} =
      (fun q : A => ((a₀, q) : A × A)) '' {q : A | Posn q ∧ Le q p ∧ q ≠ p} := by
    ext ⟨z, y⟩
    constructor
    · rintro ⟨hu, hle, hne⟩
      have hz : z = a₀ := by
        rcases hle with ⟨h, hne'⟩ | ⟨he, -⟩
        · exact absurd (hlin.2.2.1 _ _ h (h₀ z)) hne'
        · exact he
      subst hz
      refine ⟨y, ⟨hu, ?_, ?_⟩, rfl⟩
      · rcases hle with ⟨-, hne'⟩ | ⟨-, h⟩
        · exact (hne' rfl).elim
        · exact h
      · intro hcon
        exact hne (by rw [hcon])
    · rintro ⟨q, ⟨hq, hqp, hne⟩, heq⟩
      obtain rfl : z = a₀ := (congrArg Prod.fst heq).symm
      obtain rfl : y = q := (congrArg Prod.snd heq).symm
      exact ⟨hq, Or.inr ⟨rfl, hqp⟩, fun hcon => hne (congrArg Prod.snd hcon)⟩
  rw [bitRank, hset, Set.InjOn.ncard_image (fun q _ q' _ h => congrArg Prod.snd h), bitRank]

omit [Finite A] in
/-- A weight is the same number in the wide representation. -/
theorem binNum_wide (hlin : IsLinOrd Le) {a₀ : A} (h₀ : ∀ x, Le a₀ x) (b : A → Prop) :
    binNum (wideLe Le) (WidePosn Posn) (fun u => u.1 = a₀ ∧ b u.2) =
      binNum Le Posn b := by
  have hset : {u : A × A | WidePosn Posn u ∧ (u.1 = a₀ ∧ b u.2)} =
      (fun q : A => ((a₀, q) : A × A)) '' {q : A | Posn q ∧ b q} := by
    ext ⟨z, y⟩
    constructor
    · rintro ⟨hu, h1, hb⟩
      have hz : z = a₀ := h1
      subst hz
      exact ⟨y, ⟨hu, hb⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hb⟩, heq⟩
      obtain rfl : z = a₀ := (congrArg Prod.fst heq).symm
      obtain rfl : y = q := (congrArg Prod.snd heq).symm
      exact ⟨hq, rfl, hb⟩
  rw [binNum, hset, finsum_mem_image (fun q _ q' _ h => congrArg Prod.snd h), binNum]
  exact finsum_mem_congr rfl fun q _ => by rw [bitRank_wide hlin h₀]

omit [Finite A] in
/-- There are `|A|` times as many wide positions as positions. -/
theorem ncard_widePosn :
    ({u : A × A | WidePosn Posn u} : Set (A × A)).ncard =
      Nat.card A * ({p : A | Posn p} : Set A).ncard := by
  have hset : {u : A × A | WidePosn Posn u} = (Set.univ : Set A) ×ˢ {p : A | Posn p} := by
    ext u
    simp [WidePosn]
  rw [hset, Set.ncard_prod, Set.ncard_univ]

/-! ### Walking the wide positions -/

omit [Finite A] in
/-- The lowest wide position is the lowest position of the lowest block. -/
theorem minPos_wide {x p : A} (hlin : IsLinOrd Le) :
    MinPos (wideLe Le) (WidePosn Posn) (x, p) ↔ (∀ y, Le x y) ∧ MinPos Le Posn p := by
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨fun y => ?_, hp, fun q hq => ?_⟩
    · rcases hmin (y, p) hp with ⟨h1, -⟩ | ⟨he, -⟩
      · exact h1
      · have he' : x = y := he
        exact he' ▸ hlin.1 x
    · rcases hmin (x, q) hq with ⟨-, hne⟩ | ⟨-, h2⟩
      · exact (hne rfl).elim
      · exact h2
  · rintro ⟨hx, hp, hmin⟩
    refine ⟨hp, ?_⟩
    rintro ⟨z, r⟩ hr
    rcases eq_or_ne x z with rfl | hne
    · exact Or.inr ⟨rfl, hmin r hr⟩
    · exact Or.inl ⟨hx z, hne⟩

omit [Finite A] in
/-- The highest wide position is the highest position of the highest block. -/
theorem maxPos_wide {x p : A} (hlin : IsLinOrd Le) :
    MaxPos (wideLe Le) (WidePosn Posn) (x, p) ↔ (∀ y, Le y x) ∧ MaxPos Le Posn p := by
  constructor
  · rintro ⟨hp, hmax⟩
    refine ⟨fun y => ?_, hp, fun q hq => ?_⟩
    · rcases hmax (y, p) hp with ⟨h1, -⟩ | ⟨he, -⟩
      · exact h1
      · have he' : y = x := he
        exact he' ▸ hlin.1 y
    · rcases hmax (x, q) hq with ⟨-, hne⟩ | ⟨-, h2⟩
      · exact (hne rfl).elim
      · exact h2
  · rintro ⟨hx, hp, hmax⟩
    refine ⟨hp, ?_⟩
    rintro ⟨z, r⟩ hr
    rcases eq_or_ne z x with rfl | hne
    · exact Or.inr ⟨rfl, hmax r hr⟩
    · exact Or.inl ⟨hx z, hne⟩

omit [Finite A] in
/-- Stepping along the wide positions: inside a block, or from the top of one
block to the bottom of the next. -/
theorem succPos_wide {x p y q : A} (hlin : IsLinOrd Le) :
    SuccPos (wideLe Le) (WidePosn Posn) (x, p) (y, q) ↔
      (x = y ∧ SuccPos Le Posn p q) ∨
        (SuccPos Le (fun _ => True) x y ∧ MaxPos Le Posn p ∧ MinPos Le Posn q) := by
  constructor
  · rintro ⟨hp, hq, hle, hne, hbet⟩
    rcases hle with ⟨hxy, hxne⟩ | ⟨hxe, hpq⟩
    · -- a step between two blocks
      have hxy' : Le x y := hxy
      have hxne' : x ≠ y := hxne
      have hmaxp : ∀ r, Posn r → Le r p := by
        intro r hr
        by_contra hcon
        have hpr : Le p r := (hlin.2.2.2 p r).resolve_right hcon
        have hne' : p ≠ r := fun h => hcon (h ▸ hlin.1 r)
        rcases hbet (x, r) hr (Or.inr ⟨rfl, hpr⟩) (Or.inl ⟨hxy, hxne⟩) with hc | hc
        · exact hne' (congrArg Prod.snd hc).symm
        · exact hxne' (congrArg Prod.fst hc)
      have hminq : ∀ r, Posn r → Le q r := by
        intro r hr
        by_contra hcon
        have hrq : Le r q := (hlin.2.2.2 q r).resolve_left hcon
        have hne' : r ≠ q := fun h => hcon (h ▸ hlin.1 r)
        rcases hbet (y, r) hr (Or.inl ⟨hxy, hxne⟩) (Or.inr ⟨rfl, hrq⟩) with hc | hc
        · exact hxne' (congrArg Prod.fst hc).symm
        · exact hne' (congrArg Prod.snd hc)
      refine Or.inr ⟨⟨trivial, trivial, hxy', hxne', fun r _ hxr hry => ?_⟩,
        ⟨hp, hmaxp⟩, hq, hminq⟩
      rcases eq_or_ne r x with rfl | hrx
      · exact Or.inl rfl
      rcases eq_or_ne r y with rfl | hry'
      · exact Or.inr rfl
      rcases hbet (r, p) hp (Or.inl ⟨hxr, fun hc => hrx hc.symm⟩)
        (Or.inl ⟨hry, hry'⟩) with hc | hc
      · exact absurd (congrArg Prod.fst hc) hrx
      · exact absurd (congrArg Prod.fst hc) hry'
    · -- a step inside a block
      have hxe' : x = y := hxe
      subst hxe'
      refine Or.inl ⟨rfl, hp, hq, hpq, fun hc => hne (by rw [hc]), fun r hr hpr hrq => ?_⟩
      rcases hbet (x, r) hr (Or.inr ⟨rfl, hpr⟩) (Or.inr ⟨rfl, hrq⟩) with hc | hc
      · exact Or.inl (congrArg Prod.snd hc)
      · exact Or.inr (congrArg Prod.snd hc)
  · rintro (⟨rfl, hp, hq, hpq, hne, hbet⟩ | ⟨⟨-, -, hxy, hxne, hxbet⟩, ⟨hp, hmax⟩, hq, hmin⟩)
    · refine ⟨hp, hq, Or.inr ⟨rfl, hpq⟩, fun hc => hne (congrArg Prod.snd hc), ?_⟩
      rintro ⟨z, r⟩ hr hle hle'
      have hzx : z = x := by
        rcases hle with ⟨h, hne'⟩ | ⟨he, -⟩
        · rcases hle' with ⟨h', -⟩ | ⟨he', -⟩
          · exact absurd (hlin.2.2.1 _ _ h h') hne'
          · exact he'
        · exact he.symm
      subst hzx
      rcases hle with ⟨-, hne'⟩ | ⟨-, h1⟩
      · exact (hne' rfl).elim
      rcases hle' with ⟨-, hne''⟩ | ⟨-, h2⟩
      · exact (hne'' rfl).elim
      rcases hbet r hr h1 h2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · refine ⟨hp, hq, Or.inl ⟨hxy, hxne⟩, fun hc => hxne (congrArg Prod.fst hc), ?_⟩
      rintro ⟨z, r⟩ hr hle hle'
      have hz : z = x ∨ z = y := by
        rcases hle with ⟨h, -⟩ | ⟨he, -⟩
        · rcases hle' with ⟨h', -⟩ | ⟨he', -⟩
          · exact hxbet z trivial h h'
          · exact Or.inr he'
        · exact Or.inl he.symm
      rcases hz with rfl | rfl
      · have hrp : r = p := by
          rcases hle with ⟨-, hne'⟩ | ⟨-, h'⟩
          · exact (hne' rfl).elim
          · exact hlin.2.2.1 _ _ (hmax r hr) h'
        exact Or.inl (by rw [hrp])
      · have hrq : r = q := by
          rcases hle' with ⟨-, hne'⟩ | ⟨-, h'⟩
          · exact (hne' rfl).elim
          · exact hlin.2.2.1 _ _ h' (hmin r hr)
        exact Or.inr (by rw [hrq])

/-! ### The room the wide positions buy -/

private theorem add_sub_le_mul {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) : m - 1 + k ≤ m * k := by
  cases m with
  | zero => omega
  | succ m' =>
    have h : m' ≤ m' * k := Nat.le_mul_of_pos_right m' hk
    calc m' + 1 - 1 + k = m' + k := by omega
      _ ≤ m' * k + k := by omega
      _ = (m' + 1) * k := by ring

/-- A sum of numbers below `2 ^ n`, over a universe of `m` elements, is below
`2 ^ (m * n)`. -/
theorem finsum_lt_two_pow_mul {n : ℕ} (w : A → ℕ) (S : Set A) (hw : ∀ i, w i < 2 ^ n) :
    (∑ᶠ i ∈ S, w i) < 2 ^ (Nat.card A * n) := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · rw [Set.eq_empty_of_isEmpty S, finsum_mem_empty]
    exact Nat.two_pow_pos _
  have hm : 0 < Nat.card A := Nat.card_pos
  have hsum : (∑ᶠ i ∈ S, w i) ≤ Nat.card A * (2 ^ n - 1) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite S)]
    have hcard : (Set.toFinite S).toFinset.card = S.ncard :=
      (Set.ncard_eq_toFinset_card S (Set.toFinite S)).symm
    calc ∑ i ∈ (Set.toFinite S).toFinset, w i
        ≤ (Set.toFinite S).toFinset.card • (2 ^ n - 1) :=
          Finset.sum_le_card_nsmul _ _ _ fun i _ => Nat.le_sub_one_of_lt (hw i)
      _ = S.ncard * (2 ^ n - 1) := by rw [hcard, smul_eq_mul]
      _ ≤ Nat.card A * (2 ^ n - 1) := Nat.mul_le_mul_right _ (Set.ncard_le_card S)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.mul_zero, pow_zero]
    simp only [pow_zero, Nat.sub_self, Nat.mul_zero] at hsum
    omega
  -- `m ≤ 2 ^ (m - 1)`, and `m - 1 + n ≤ m * n`, so `m * 2 ^ n` still fits
  have hmpow : Nat.card A ≤ 2 ^ (Nat.card A - 1) := by
    have := Nat.lt_two_pow_self (n := Nat.card A - 1)
    omega
  have hbig : Nat.card A * 2 ^ n ≤ 2 ^ (Nat.card A * n) :=
    calc Nat.card A * 2 ^ n ≤ 2 ^ (Nat.card A - 1) * 2 ^ n := Nat.mul_le_mul_right _ hmpow
      _ = 2 ^ (Nat.card A - 1 + n) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (Nat.card A * n) := Nat.pow_le_pow_right (by norm_num) (add_sub_le_mul hm hn)
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hmul : Nat.card A * (2 ^ n - 1) + Nat.card A = Nat.card A * 2 ^ n :=
    calc Nat.card A * (2 ^ n - 1) + Nat.card A = Nat.card A * (2 ^ n - 1 + 1) := by ring
      _ = Nat.card A * 2 ^ n := by rw [show 2 ^ n - 1 + 1 = 2 ^ n by omega]
  omega

/-- **The wide positions are wide enough**: any sum of the instance's weights
fits in them. -/
theorem finsum_binNum_lt_wide (hlin : IsLinOrd Le) (bits : A → A → Prop) (S : Set A) :
    (∑ᶠ i ∈ S, binNum Le Posn (bits i)) <
      2 ^ ({u : A × A | WidePosn Posn u} : Set (A × A)).ncard := by
  rw [ncard_widePosn]
  exact finsum_lt_two_pow_mul _ S fun i =>
    binNum_lt_two_pow hlin _ Posn rfl (bits i)

end Wide

end DescriptiveComplexity
