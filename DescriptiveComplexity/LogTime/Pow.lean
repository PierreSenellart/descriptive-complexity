/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Fields
import Mathlib.Data.Fintype.Lattice

/-!
# The doubling chain: `i ↦ 2 ^ i` is first-order in `≤`, `+` and `×`

`DescriptiveComplexity.powArithDef` – the graph of `i ↦ 2 ^ i` as a formula of
`FO(≤, +, ×)`, [Immerman 1999][immerman1999descriptive] Thm 1.17(2) – is the
lemma the AC⁰ reading of the machine model rested on, and this file proves it,
by exhibiting a *certificate* that a first-order formula can check.

## The certificate

The chain is the halving chain of the exponent: `a`, `a / 2`, `a / 4`, …, `0`,
of length `⌈log a⌉ ≤ log log n`. Its place values `2 ^ (a / 2 ^ t)` are
*positions*, so the chain is a **set of positions**, that is, one guessed element
`Y` – carrying the chain *below* its top, the top being the given `p`
(`DescriptiveComplexity.chainBelow`). Consecutive positions `q < q'` of the chain
are tied by

`q' = q * q` (the exponent doubles) or `q' = 2 * (q * q)` (it doubles and gains
one),

which is a product of elements – available – rather than an addition of
exponents, which is not. That is the whole reason the chain is guessed at all.

## Why the exponents have to be carried, and where

The chain conditions alone leave the *value* of the top exponent free: they force
`index q' = 2 * index q + ε` with `ε` read off which case fired, so they pin the
top index only relative to the bottom. What ties it to the given `i` is a second
guessed element `E` carrying, **in the field between `q` and the next chain
position** (`DescriptiveComplexity.FieldAt`), the number `index q`. No pairing
between the chain and the positions is then needed – the value sits at the place
it describes – and the recursion becomes a relation between *values*,
`val q' = 2 * val q + ε`, which is `DescriptiveComplexity.val_eq_of_chain`.

So the certificate is **two elements**, not three: the chain delimits its own
fields, and no marks have to be guessed. That the value fits in the field it is
given is `DescriptiveComplexity.half_add_size_le`, and it is exactly the right
statement – the field between the positions of index `k / 2` and `k` is
`k - k / 2` bits wide, and the value it must hold is `k / 2`.

Four consequences worth keeping:

* **Soundness needs no condition on the layout.** The formula never says where a
  field ends or that fields do not overlap: whatever the guess, each `q` reads
  *some* value, and the chain conditions force those values to be the indices.
  A garbage layout simply fails the conditions.
* **The top field must not be written.** Its value is `a` itself, needing
  `log log n` bits *above* position `a`, and there need be no room: `2 ^ a < n`
  says nothing about `2 ^ (a + log log n)`. The value at the top is the given
  element `i`, so the fields carry only the rest of the chain, whose largest
  entry is `a / 2` and which therefore fits below position `a`. The top position
  is also the one with no next chain position, so it is exactly the one with no
  field to read: the two facts are the same fact.
* **The top position is left out of `Y` for a second reason.** A set of
  positions is an element only if its value is a rank, and the chain *including*
  its top can exceed `2 ^ a`, hence the universe – there is no room for a bit at
  `p` itself when `n` is barely above `2 ^ a`. Leaving it out costs nothing, `p`
  being given, and the rest fits with room to spare:
  `DescriptiveComplexity.chainBelow_lt`.
* **The chain conditions are between consecutive positions only.** That is what
  `DescriptiveComplexity.chainSet_le_half_of_lt` buys – the predecessor of the
  entry `k` is `k / 2` and nothing lies between – so a formula quantifying “`q`
  and `q'` in `Y` with nothing of `Y` between” sees exactly the pairs the
  recursion talks about.

## What is here, in three layers

* **The arithmetic**, in `ℕ`: the chain as a set
  (`DescriptiveComplexity.ChainSet`), the fact that the predecessor of `k` in it
  is `k / 2` (`DescriptiveComplexity.chainSet_le_half_of_lt`), the induction that
  turns the chain conditions into `val k = k`
  (`DescriptiveComplexity.val_eq_of_chain`), and the two elements a certificate
  guesses – `DescriptiveComplexity.chainBelow`, read back by
  `DescriptiveComplexity.testBit_chainBelow`, and
  `DescriptiveComplexity.chainVals`, read back by
  `DescriptiveComplexity.chainVals_field`. Both are ranks because both are below
  `2 ^ a` (`DescriptiveComplexity.chainBelow_lt`,
  `DescriptiveComplexity.chainVals_lt`), the second by the capacity lemma
  `DescriptiveComplexity.half_add_size_le`.
* **The certificate**, as a property of four elements
  (`DescriptiveComplexity.PowCert`, over
  `DescriptiveComplexity.InChain`/`ConsChain`/`ValAt`), with both halves:
  `DescriptiveComplexity.powCert_sound` and
  `DescriptiveComplexity.powCert_complete`, conjoined in
  `DescriptiveComplexity.powCert_iff`.
* **The formula**, built with the `DescriptiveComplexity.ArithDef` API and the
  field reader `DescriptiveComplexity.arithDef_fieldAt`, giving
  `DescriptiveComplexity.powArithDef`.
-/

namespace DescriptiveComplexity

/-! ### The halving chain -/

/-- **The halving chain of `a`**: the exponents `a / 2 ^ t`, which are the
indices of the positions a `2 ^ a` certificate guesses. -/
def ChainSet (a k : ℕ) : Prop := ∃ t : ℕ, k = a / 2 ^ t

theorem chainSet_self (a : ℕ) : ChainSet a a := ⟨0, by simp⟩

theorem chainSet_zero (a : ℕ) : ChainSet a 0 :=
  ⟨a, (Nat.div_eq_of_lt (Nat.lt_two_pow_self)).symm⟩

theorem chainSet_half {a k : ℕ} (h : ChainSet a k) : ChainSet a (k / 2) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t + 1, by rw [pow_succ, Nat.div_div_eq_div_mul]⟩

theorem chainSet_le {a k : ℕ} (h : ChainSet a k) : k ≤ a := by
  obtain ⟨t, rfl⟩ := h
  exact Nat.div_le_self a (2 ^ t)

/-- Every entry but the top is an entry of the chain of the half. -/
theorem chainSet_half_of_ne {a k : ℕ} (h : ChainSet a k) (hne : k ≠ a) :
    ChainSet (a / 2) k := by
  obtain ⟨t, ht⟩ := h
  cases t with
  | zero => rw [pow_zero, Nat.div_one] at ht; exact absurd ht hne
  | succ s =>
    refine ⟨s, ?_⟩
    have h2 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by ring
    rw [ht, h2, ← Nat.div_div_eq_div_mul]

/-- …and conversely. -/
theorem chainSet_of_half {a k : ℕ} (h : ChainSet (a / 2) k) : ChainSet a k := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t + 1, ?_⟩
  have h2 : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
  rw [ht, h2, ← Nat.div_div_eq_div_mul]

/-- **The chain has no gaps**: an entry below `k` is at most `k / 2`, so the
predecessor of `k` in the chain is `k / 2` – which is what lets a formula state
the recursion for *consecutive* positions only. -/
theorem chainSet_le_half_of_lt {a k l : ℕ} (hk : ChainSet a k) (hl : ChainSet a l)
    (hlt : l < k) : l ≤ k / 2 := by
  obtain ⟨t, rfl⟩ := hk
  obtain ⟨s, rfl⟩ := hl
  have hts : t < s := by
    by_contra hcon
    have : a / 2 ^ t ≤ a / 2 ^ s :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.two_pow_pos _)
    omega
  have h1 : a / 2 ^ s ≤ a / 2 ^ (t + 1) :=
    Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.two_pow_pos _)
  have h2 : a / 2 ^ (t + 1) = a / 2 ^ t / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  omega

/-! ### Soundness: the chain conditions pin the exponents -/

/-- **The certificate is sound**: if a value is carried at every entry of a set
containing `0`, the value at `0` is `0`, and each entry's value is twice its
half's plus its own parity, then the value at every entry *is* that entry.

This is the whole of the soundness half of `DescriptiveComplexity.PowArithDef`,
with the formula stripped away: `val k` is the field a guessed element carries at
the position of index `k`, the parity is which of `q' = q * q` and
`q' = 2 * (q * q)` fired, and the conclusion says the guess describes the
exponents it claims to. -/
theorem val_eq_of_chain {S : ℕ → Prop} {val : ℕ → ℕ} (h0 : val 0 = 0)
    (hstep : ∀ k : ℕ, S k → 0 < k → S (k / 2) ∧ val k = 2 * val (k / 2) + k % 2) :
    ∀ k : ℕ, S k → val k = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact h0
    · obtain ⟨hhalf, hval⟩ := hstep k hk hpos
      rw [hval, ih (k / 2) (by omega) hhalf]
      omega

/-! ### The layout: why the fields fit -/

/-- **A value fits in its own number of bits**, and a field of that width at
position `k / 2` never reaches `k`: `Nat.size` is the width, `Nat.lt_size_self`
says the value fits, and this says the fields of a certificate are pairwise
disjoint – the completeness half's only capacity condition. -/
theorem half_add_size_le (k : ℕ) : k / 2 + Nat.size (k / 2) ≤ k := by
  have h : Nat.size (k / 2) ≤ k / 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-! ### The certificate's first element -/

/-- **The chain below its top, as a number**: one bit at the position of each
`a / 2 ^ t` for `t ≥ 1`. This is the element `Y` a certificate guesses. -/
def chainBelow (a : ℕ) : ℕ :=
  if a = 0 then 0 else 2 ^ (a / 2) + chainBelow (a / 2)
  decreasing_by omega

theorem chainBelow_zero : chainBelow 0 = 0 := by rw [chainBelow]; simp

theorem chainBelow_pos {a : ℕ} (ha : 0 < a) :
    chainBelow a = 2 ^ (a / 2) + chainBelow (a / 2) := by
  rw [chainBelow, if_neg (by omega)]

/-- **The chain below its top fits under its top**: `Y` is a rank whenever the
place value it certifies is one, which is what makes the certificate exist. The
chain *including* its top need not fit, which is why the top is left out. -/
theorem chainBelow_lt (a : ℕ) : chainBelow a < 2 ^ a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [chainBelow_zero]
      simp
    · rw [chainBelow_pos hpos]
      have hih : chainBelow (a / 2) < 2 ^ (a / 2) := ih (a / 2) (by omega)
      have hle : 2 ^ (a / 2) + 2 ^ (a / 2) ≤ 2 ^ a := by
        have h1 : (2 : ℕ) ^ (a / 2) + 2 ^ (a / 2) = 2 ^ (a / 2 + 1) := by
          rw [pow_succ]; ring
        rw [h1]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **A bit above a place value**: with a low part below `2 ^ m`, the bits of
`2 ^ m + y` are those of `y` below `m`, a one at `m`, and nothing above. This is
the only bit-level computation the chain's element needs. -/
theorem testBit_two_pow_add {m y : ℕ} (hy : y < 2 ^ m) (k : ℕ) :
    (2 ^ m + y).testBit k = if k < m then y.testBit k else decide (k = m) := by
  rcases lt_trichotomy k m with hk | rfl | hk
  · rw [if_pos hk, Nat.testBit_two_pow_add_gt hk]
  · rw [if_neg (lt_irrefl k), Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]
    simp
  · rw [if_neg (by omega), Nat.testBit_lt_two_pow, decide_eq_false (by omega)]
    calc 2 ^ m + y < 2 ^ m + 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The chain, read off its element**: the bits of
`DescriptiveComplexity.chainBelow` are exactly the entries of the chain other
than its top – the top being the given place value, which is why it is left
out. -/
theorem testBit_chainBelow : ∀ a k : ℕ,
    (chainBelow a).testBit k = true ↔ (ChainSet a k ∧ k ≠ a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro k
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [chainBelow_zero, Nat.zero_testBit]
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro ⟨hc, hne⟩
        have := chainSet_le hc
        omega
    · have hhalf : a / 2 < a := by omega
      rw [chainBelow_pos hpos, testBit_two_pow_add (chainBelow_lt (a / 2))]
      rcases lt_trichotomy k (a / 2) with hk | rfl | hk
      · rw [if_pos hk, ih (a / 2) hhalf k]
        exact ⟨fun h => ⟨chainSet_of_half h.1, by omega⟩,
          fun h => ⟨chainSet_half_of_ne h.1 (by omega), by omega⟩⟩
      · rw [if_neg (lt_irrefl _)]
        exact ⟨fun _ => ⟨⟨1, by norm_num⟩, by omega⟩, fun _ => by simp⟩
      · rw [if_neg (by omega)]
        simp only [decide_eq_true_eq]
        constructor
        · omega
        · rintro ⟨hc, hne⟩
          have hlt : k < a := lt_of_le_of_ne (chainSet_le hc) hne
          have := chainSet_le_half_of_lt (chainSet_self a) hc hlt
          omega

/-! ### The certificate's second element -/

/-- **The exponents of the chain, packed side by side**: each entry below the
top carries its own value in the field that starts at it and ends at the next
entry. This is the element `E` a certificate guesses. -/
def chainVals (a : ℕ) : ℕ :=
  if a = 0 then 0 else a / 2 * 2 ^ (a / 2) + chainVals (a / 2)
  decreasing_by omega

theorem chainVals_zero : chainVals 0 = 0 := by rw [chainVals]; simp

theorem chainVals_pos {a : ℕ} (ha : 0 < a) :
    chainVals a = a / 2 * 2 ^ (a / 2) + chainVals (a / 2) := by
  rw [chainVals, if_neg (by omega)]

/-- **An entry fits in the field it is given**: `k / 2` is written in the
`k - k / 2` bits between the positions of index `k / 2` and `k`, which is
`DescriptiveComplexity.half_add_size_le` read as a bound. -/
theorem half_lt_two_pow_sub (k : ℕ) : k / 2 < 2 ^ (k - k / 2) :=
  lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by norm_num) (by have := half_add_size_le k; omega))

/-- **The packed exponents fit under the top place value**: `E` is a rank
whenever `2 ^ a` is one, the top entry being the only one with no field. -/
theorem chainVals_lt (a : ℕ) : chainVals a < 2 ^ a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [chainVals_zero]
      simp
    · rw [chainVals_pos hpos]
      have hih : chainVals (a / 2) < 2 ^ (a / 2) := ih (a / 2) (by omega)
      have hfit : a / 2 + 1 ≤ 2 ^ (a - a / 2) := half_lt_two_pow_sub a
      have hle : (a / 2 + 1) * 2 ^ (a / 2) ≤ 2 ^ a := by
        calc (a / 2 + 1) * 2 ^ (a / 2) ≤ 2 ^ (a - a / 2) * 2 ^ (a / 2) :=
              Nat.mul_le_mul_right _ hfit
          _ = 2 ^ (a - a / 2 + a / 2) := (pow_add 2 _ _).symm
          _ = 2 ^ a := by congr 1; omega
      have hexp : (a / 2 + 1) * 2 ^ (a / 2) = a / 2 * 2 ^ (a / 2) + 2 ^ (a / 2) := by ring
      omega

/-- **The chain, one step below a given entry**: an entry other than the top has
a next entry, and it is that entry's half. -/
theorem exists_chainSucc {a k : ℕ} (hk : ChainSet a k) (hne : k ≠ a) :
    ∃ l : ℕ, ChainSet a l ∧ 0 < l ∧ l / 2 = k := by
  classical
  have hex : ∃ t : ℕ, a / 2 ^ t = k := by obtain ⟨t, ht⟩ := hk; exact ⟨t, ht.symm⟩
  have hfind : a / 2 ^ Nat.find hex = k := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h
    · rw [h0, pow_zero, Nat.div_one] at hfind
      exact absurd hfind.symm hne
    · exact h
  obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hhalf : a / 2 ^ s / 2 = k := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ, ← hs]
    exact hfind
  refine ⟨a / 2 ^ s, ⟨s, rfl⟩, ?_, hhalf⟩
  by_contra hzero
  have h0 : a / 2 ^ s = 0 := by omega
  have hk0 : k = 0 := by rw [← hhalf, h0]
  exact Nat.find_min hex (show s < Nat.find hex by omega) (by rw [h0, hk0])

/-- **The layout works**: between an entry and the next one, the packed element
carries that entry. This is the whole completeness half of the field reading –
the formula reads `DescriptiveComplexity.FieldAt`, and this says what it finds
in the element the certificate builds. -/
theorem chainVals_field : ∀ a : ℕ, ∀ l : ℕ, ChainSet a l → 0 < l →
    chainVals a / 2 ^ (l / 2) % 2 ^ (l - l / 2) = l / 2 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro l hl hlpos
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · have := chainSet_le hl
      omega
    rw [chainVals_pos hapos]
    by_cases hla : l = a
    · subst hla
      rw [Nat.add_comm (l / 2 * 2 ^ (l / 2)) (chainVals (l / 2)),
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos (l / 2)),
        Nat.div_eq_of_lt (chainVals_lt (l / 2)), Nat.zero_add,
        Nat.mod_eq_of_lt (half_lt_two_pow_sub l)]
    · -- `l` lies in the chain of `a / 2`, and the top block is a multiple of `2 ^ l`
      have hle : l ≤ a / 2 :=
        chainSet_le_half_of_lt (chainSet_self a) hl (lt_of_le_of_ne (chainSet_le hl) hla)
      have hsplit : a / 2 * 2 ^ (a / 2) =
          2 ^ (l / 2) * (2 ^ (l - l / 2) * (a / 2 * 2 ^ (a / 2 - l))) := by
        have h1 : (2 : ℕ) ^ (l / 2) * (2 ^ (l - l / 2) * (a / 2 * 2 ^ (a / 2 - l)))
            = a / 2 * (2 ^ (l / 2) * 2 ^ (l - l / 2) * 2 ^ (a / 2 - l)) := by ring
        have h2 : l / 2 + (l - l / 2) + (a / 2 - l) = a / 2 := by omega
        rw [h1, ← pow_add, ← pow_add, h2]
      rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_mod]
      exact ih (a / 2) (by omega) l (chainSet_half_of_ne hl hla) hlpos

/-! ### The certificate, as a property of four elements -/

section Certificate

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The chain**, as a set of elements: the given place value `p` – its top,
which is not written into the guess – together with the positions marked in the
guessed element `Y`. -/
def InChain (p Y q : A) : Prop := q = p ∨ (IsPos q ∧ BitAt q Y)

/-- **Two consecutive entries** of the chain: nothing of the chain lies between
them. `DescriptiveComplexity.chainSet_le_half_of_lt` is why speaking of
consecutive entries is enough – the entry below `k` is `k / 2`. -/
def ConsChain (p Y q q' : A) : Prop :=
  InChain p Y q ∧ InChain p Y q' ∧ q < q' ∧ ∀ r : A, ¬(InChain p Y r ∧ q < r ∧ r < q')

/-- **The exponent carried at a chain entry**: the given `i` at the top, and
otherwise the field of `E` running from the entry up to the next one. The top
carries no field – there is no room above it – which is the same fact as its
having no next entry. -/
def ValAt (i p Y E q v : A) : Prop :=
  (q = p ∧ v = i) ∨ (¬(q = p) ∧ ∃ q' : A, ConsChain p Y q q' ∧ FieldAt q q' E v)

/-- **The certificate for `orank p = 2 ^ orank i`**: `p` is a position and the
greatest entry of the chain it tops; the chain's least entry is the place value
`1`, carrying the exponent `0`; and consecutive entries square, or square and
double, with their exponents doubling, or doubling and gaining one. -/
def PowCert (i p Y E : A) : Prop :=
  IsPos p ∧
    (∀ q : A, InChain p Y q → q ≤ p) ∧
    (∃ q v : A, orank q = 1 ∧ InChain p Y q ∧ ValAt i p Y E q v ∧ orank v = 0) ∧
    (∀ q q' v v' : A, ConsChain p Y q q' → ValAt i p Y E q v → ValAt i p Y E q' v' →
      (orank q * orank q = orank q' ∧ orank v + orank v = orank v') ∨
      (∃ s u one : A, orank q * orank q = orank s ∧ orank s + orank s = orank q' ∧
        orank v + orank v = orank u ∧ orank one = 1 ∧ orank u + orank one = orank v'))

omit [Finite A] in
/-- Every entry of the chain is a position, the top because it is assumed to
be one. -/
theorem InChain.isPos {p Y q : A} (h : InChain p Y q) (hp : IsPos p) : IsPos q := by
  rcases h with rfl | ⟨h, -⟩
  · exact hp
  · exact h

/-- Positions are ordered by their exponents. -/
theorem posExp_lt_posExp {q q' : A} (hq : IsPos q) (hq' : IsPos q') (h : q < q') :
    posExp q < posExp q' := by
  have hlt := orank_lt_orank h
  rw [orank_eq_two_pow_posExp hq, orank_eq_two_pow_posExp hq'] at hlt
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt

omit [Finite A] in
/-- An entry has at most one next entry. -/
theorem consChain_unique {p Y q q₁ q₂ : A} (h₁ : ConsChain p Y q q₁)
    (h₂ : ConsChain p Y q q₂) : q₁ = q₂ := by
  rcases lt_trichotomy q₁ q₂ with h | h | h
  · exact absurd ⟨h₁.2.1, h₁.2.2.1, h⟩ (h₂.2.2.2 q₁)
  · exact h
  · exact absurd ⟨h₂.2.1, h₂.2.2.1, h⟩ (h₁.2.2.2 q₂)

/-- **An entry carries one exponent**: at the top it is the given `i`, and
elsewhere the field is a function of its two ends. -/
theorem valAt_unique {i p Y E q v v' : A} (hp : IsPos p)
    (h : ValAt i p Y E q v) (h' : ValAt i p Y E q v') : v = v' := by
  rcases h with ⟨hqp, rfl⟩ | ⟨hne, q₁, hc₁, hf₁⟩
  · rcases h' with ⟨-, rfl⟩ | ⟨hne', -⟩
    · rfl
    · exact absurd hqp hne'
  · rcases h' with ⟨hqp', rfl⟩ | ⟨-, q₂, hc₂, hf₂⟩
    · exact absurd hqp' hne
    · have hq : IsPos q := hc₁.1.isPos hp
      have hq₁ : IsPos q₁ := hc₁.2.1.isPos hp
      have hexp : posExp q < posExp q₁ := posExp_lt_posExp hq hq₁ hc₁.2.2.1
      rw [consChain_unique hc₂ hc₁] at hf₂
      exact fieldAt_unique (a := posExp q) (d := posExp q₁ - posExp q)
        (orank_eq_two_pow_posExp hq)
        (by rw [orank_eq_two_pow_posExp hq₁]; congr 1; omega) hf₁ hf₂

/-- **Below the top there is a next entry**: the least entry above the given
one. -/
theorem exists_consChain {p Y q : A} (hq : InChain p Y q) (hlt : q < p) :
    ∃ q' : A, ConsChain p Y q q' := by
  have : Nonempty {r : A // InChain p Y r ∧ q < r} := ⟨⟨p, Or.inl rfl, hlt⟩⟩
  obtain ⟨⟨q', hq'chain, hq'lt⟩, hmin⟩ :=
    Finite.exists_min fun r : {r : A // InChain p Y r ∧ q < r} => (r : A)
  refine ⟨q', hq, hq'chain, hq'lt, fun r hr => ?_⟩
  exact absurd (hmin ⟨r, hr.1, hr.2.1⟩) (not_le.mpr hr.2.2)

/-- **Above the least entry there is a previous one**: the greatest entry below
the given one. -/
theorem exists_consChain_lt {p Y q r : A} (hq : InChain p Y q) (hr : InChain p Y r)
    (hlt : r < q) : ∃ r' : A, ConsChain p Y r' q := by
  have : Nonempty {s : A // InChain p Y s ∧ s < q} := ⟨⟨r, hr, hlt⟩⟩
  obtain ⟨⟨r', hr'chain, hr'lt⟩, hmax⟩ :=
    Finite.exists_max fun s : {s : A // InChain p Y s ∧ s < q} => (s : A)
  refine ⟨r', hr'chain, hq, hr'lt, fun s hs => ?_⟩
  exact absurd (hmax ⟨s, hs.1, hs.2.2⟩) (not_le.mpr hs.2.1)

/-- **Every entry carries a value**: the top the given `i`, and any other the
field below its next entry, which is a rank because a field always is
(`DescriptiveComplexity.exists_fieldAt`). -/
theorem exists_valAt {i p Y E q : A} (hp : IsPos p) (hmax : ∀ r : A, InChain p Y r → r ≤ p)
    (hq : InChain p Y q) : ∃ v : A, ValAt i p Y E q v := by
  by_cases hqp : q = p
  · exact ⟨i, Or.inl ⟨hqp, rfl⟩⟩
  · obtain ⟨q', hc⟩ := exists_consChain hq (lt_of_le_of_ne (hmax q hq) hqp)
    have hqpos : IsPos q := hq.isPos hp
    have hq'pos : IsPos q' := hc.2.1.isPos hp
    have hexp : posExp q < posExp q' := posExp_lt_posExp hqpos hq'pos hc.2.2.1
    obtain ⟨v, hv⟩ := exists_fieldAt (p := q) (q := q') (x := E) (a := posExp q)
      (d := posExp q' - posExp q) (orank_eq_two_pow_posExp hqpos)
      (by rw [orank_eq_two_pow_posExp hq'pos]; congr 1; omega)
    exact ⟨v, Or.inr ⟨hqp, q', hc, hv⟩⟩

/-! ### Soundness: what a certificate forces -/

open Classical in
/-- **The exponent a certificate carries at the position of index `k`**: the
value read at the unique position of that place value, and `0` where there is
none. `DescriptiveComplexity.valAt_unique` is what makes this a function. -/
noncomputable def powVal (i p Y E : A) (k : ℕ) : ℕ :=
  if h : ∃ m : ℕ, ∃ q v : A, orank q = 2 ^ k ∧ ValAt i p Y E q v ∧ orank v = m then
    h.choose else 0

theorem powVal_eq {i p Y E q v : A} {k : ℕ} (hp : IsPos p) (hq : orank q = 2 ^ k)
    (hv : ValAt i p Y E q v) : powVal i p Y E k = orank v := by
  have hex : ∃ m : ℕ, ∃ q v : A, orank q = 2 ^ k ∧ ValAt i p Y E q v ∧ orank v = m :=
    ⟨orank v, q, v, hq, hv, rfl⟩
  rw [powVal, dif_pos hex]
  obtain ⟨q', v', hq', hv', hm⟩ := hex.choose_spec
  rw [orank_inj (hq'.trans hq.symm)] at hv'
  rw [← hm, valAt_unique hp hv' hv]

/-- **A certificate is sound**: whatever is guessed, the chain conditions force
the value at each entry to be that entry's exponent, and the value at the top is
the given `i`. Nothing is assumed about the layout of the fields – a garbage
guess simply fails the conditions. -/
theorem powCert_sound {i p Y E : A} (h : PowCert i p Y E) : orank p = 2 ^ orank i := by
  obtain ⟨hp, hmax, ⟨q₀, v₀, hq₀, hq₀chain, hq₀val, hv₀⟩, hstep⟩ := h
  have hval0 : powVal i p Y E 0 = 0 := by
    rw [powVal_eq hp (by rw [hq₀]; norm_num) hq₀val, hv₀]
  have hchain : ∀ k : ℕ, (∃ q : A, InChain p Y q ∧ orank q = 2 ^ k) → 0 < k →
      (∃ q : A, InChain p Y q ∧ orank q = 2 ^ (k / 2)) ∧
        powVal i p Y E k = 2 * powVal i p Y E (k / 2) + k % 2 := by
    intro k hk hkpos
    obtain ⟨q, hqchain, hqrank⟩ := hk
    have hq₀lt : q₀ < q := by
      refine lt_of_orank_lt ?_
      rw [hq₀, hqrank]
      exact Nat.one_lt_two_pow_iff.mpr (by omega)
    obtain ⟨r, hc⟩ := exists_consChain_lt hqchain hq₀chain hq₀lt
    obtain ⟨v, hv⟩ := exists_valAt (i := i) (E := E) hp hmax hc.1
    obtain ⟨v', hv'⟩ := exists_valAt (i := i) (E := E) hp hmax hqchain
    have hrrank : orank r = 2 ^ posExp r := orank_eq_two_pow_posExp (hc.1.isPos hp)
    have hvalr : powVal i p Y E (posExp r) = orank v := powVal_eq hp hrrank hv
    have hvalq : powVal i p Y E k = orank v' := powVal_eq hp hqrank hv'
    rcases hstep r q v v' hc hv hv' with ⟨hsq, hsv⟩ | ⟨s, u, one, hs1, hs2, hu1, hone, hu2⟩
    · have hexp : posExp r + posExp r = k := by
        refine Nat.pow_right_injective (le_refl 2) ?_
        change (2 : ℕ) ^ (posExp r + posExp r) = 2 ^ k
        rw [pow_add, ← hrrank, ← hqrank]
        exact hsq
      refine ⟨⟨r, hc.1, by rw [hrrank]; congr 1; omega⟩, ?_⟩
      have hhalf : k / 2 = posExp r := by omega
      rw [hvalq, hhalf, hvalr]
      omega
    · have hq2 : orank q = 2 ^ (posExp r + posExp r + 1) := by
        rw [pow_succ, pow_add, ← hrrank, hs1]
        omega
      have hexp : posExp r + posExp r + 1 = k :=
        Nat.pow_right_injective (le_refl 2) (hq2.symm.trans hqrank)
      refine ⟨⟨r, hc.1, by rw [hrrank]; congr 1; omega⟩, ?_⟩
      have hhalf : k / 2 = posExp r := by omega
      rw [hvalq, hhalf, hvalr]
      omega
  have hfin := val_eq_of_chain (S := fun k => ∃ q : A, InChain p Y q ∧ orank q = 2 ^ k)
    (val := powVal i p Y E) hval0 hchain (posExp p)
    ⟨p, Or.inl rfl, orank_eq_two_pow_posExp hp⟩
  have hpi : powVal i p Y E (posExp p) = orank i :=
    powVal_eq hp (orank_eq_two_pow_posExp hp) (Or.inl ⟨rfl, rfl⟩)
  rw [orank_eq_two_pow_posExp hp, ← hfin, hpi]

/-! ### Completeness: the certificate exists -/

/-- **A certificate exists**: the chain below the top is the element `Y`
(`DescriptiveComplexity.chainBelow`), the exponents packed in its fields are the
element `E` (`DescriptiveComplexity.chainVals`), and both are ranks because both
are below the place value `2 ^ orank i` that is assumed to be one. -/
theorem powCert_complete {i p : A} (h : orank p = 2 ^ orank i) :
    ∃ Y E : A, PowCert i p Y E := by
  have hnonempty : Nonempty A := ⟨i⟩
  set a := orank i with ha
  have hcard : 2 ^ a < Nat.card A := by rw [← h]; exact orank_lt_card p
  have hpow : ∀ k : ℕ, k ≤ a → ∃ q : A, orank q = 2 ^ k := fun k hk =>
    exists_orank_eq (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hk) hcard)
  obtain ⟨Y, hY⟩ : ∃ Y : A, orank Y = chainBelow a :=
    exists_orank_eq (lt_trans (chainBelow_lt a) hcard)
  obtain ⟨E, hE⟩ : ∃ E : A, orank E = chainVals a :=
    exists_orank_eq (lt_trans (chainVals_lt a) hcard)
  -- the chain is read off `Y`, its top being `p` itself
  have hInChain : ∀ q : A, InChain p Y q ↔ ∃ k : ℕ, ChainSet a k ∧ orank q = 2 ^ k := by
    intro q
    constructor
    · rintro (hqp | ⟨⟨b, hb⟩, hbit⟩)
      · exact ⟨a, chainSet_self a, by rw [hqp]; exact h⟩
      · rw [bitAt_iff hb, hY, testBit_chainBelow] at hbit
        exact ⟨b, hbit.1, hb⟩
    · rintro ⟨k, hk, hq⟩
      by_cases hka : k = a
      · exact Or.inl (orank_inj (by rw [hq, hka, h]))
      · exact Or.inr ⟨⟨k, hq⟩, by
          rw [bitAt_iff hq, hY]
          exact (testBit_chainBelow a k).mpr ⟨hk, hka⟩⟩
  -- consecutive entries are an entry and its half
  have hCons : ∀ q q' : A, ConsChain p Y q q' ↔
      ∃ l : ℕ, ChainSet a l ∧ 0 < l ∧ orank q = 2 ^ (l / 2) ∧ orank q' = 2 ^ l := by
    intro q q'
    constructor
    · rintro ⟨hq, hq', hlt, hbet⟩
      obtain ⟨k, hk, hqk⟩ := (hInChain q).mp hq
      obtain ⟨l, hl, hql⟩ := (hInChain q').mp hq'
      have hkl : k < l := by
        have hr := orank_lt_orank hlt
        rw [hqk, hql] at hr
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hr
      have hkhalf : k ≤ l / 2 := chainSet_le_half_of_lt hl hk hkl
      refine ⟨l, hl, by omega, ?_, hql⟩
      rcases Nat.eq_or_lt_of_le hkhalf with hc | hc
      · rw [hqk, hc]
      · obtain ⟨r, hr⟩ := hpow (l / 2) (le_trans (Nat.div_le_self l 2) (chainSet_le hl))
        refine absurd ⟨(hInChain r).mpr ⟨l / 2, chainSet_half hl, hr⟩, ?_, ?_⟩ (hbet r)
        · exact lt_of_orank_lt (by
            rw [hqk, hr]; exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hc)
        · exact lt_of_orank_lt (by
            rw [hr, hql]; exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega))
    · rintro ⟨l, hl, hlpos, hq, hq'⟩
      refine ⟨(hInChain q).mpr ⟨l / 2, chainSet_half hl, hq⟩,
        (hInChain q').mpr ⟨l, hl, hq'⟩, ?_, ?_⟩
      · exact lt_of_orank_lt (by
          rw [hq, hq']; exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega))
      · rintro r ⟨hr, hqr, hrq'⟩
        obtain ⟨m, hm, hrm⟩ := (hInChain r).mp hr
        have h1 : l / 2 < m := by
          have hx := orank_lt_orank hqr
          rw [hq, hrm] at hx
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hx
        have h2 : m < l := by
          have hx := orank_lt_orank hrq'
          rw [hrm, hq'] at hx
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hx
        have := chainSet_le_half_of_lt hl hm h2
        omega
  -- the value at an entry is its exponent
  have hValAt : ∀ (q v : A) (k : ℕ), ChainSet a k → orank q = 2 ^ k →
      (ValAt i p Y E q v ↔ orank v = k) := by
    intro q v k hk hq
    have hqp : q = p ↔ k = a := by
      constructor
      · intro hqp
        rw [hqp, h] at hq
        exact (Nat.pow_right_injective (le_refl 2) hq.symm)
      · intro hka
        exact orank_inj (by rw [hq, hka, h])
    constructor
    · rintro (⟨hp', rfl⟩ | ⟨hne, q', hc, hf⟩)
      · rw [← ha, ← hqp.mp hp']
      · obtain ⟨l, hl, hlpos, hql, hq'l⟩ := (hCons q q').mp hc
        have hkl : k = l / 2 := Nat.pow_right_injective (le_refl 2) (hq.symm.trans hql)
        rw [fieldAt_iff (a := k) (d := l - k) hq
          (by rw [hq'l]; congr 1; omega)] at hf
        rw [hf, hE, hkl, show l - l / 2 = l - l / 2 from rfl]
        exact chainVals_field a l hl hlpos
    · intro hv
      by_cases hqpe : q = p
      · exact Or.inl ⟨hqpe, orank_inj (by rw [hv, ← ha, hqp.mp hqpe])⟩
      · obtain ⟨l, hl, hlpos, hlk⟩ := exists_chainSucc hk (fun hka => hqpe (hqp.mpr hka))
        obtain ⟨q', hq'⟩ := hpow l (chainSet_le hl)
        refine Or.inr ⟨hqpe, q', (hCons q q').mpr ⟨l, hl, hlpos, by rw [hq, hlk], hq'⟩, ?_⟩
        rw [fieldAt_iff (a := k) (d := l - k) hq (by rw [hq']; congr 1; omega)]
        rw [hv, hE, ← hlk]
        exact (chainVals_field a l hl hlpos).symm
  refine ⟨Y, E, ⟨a, h⟩, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, hqk⟩ := (hInChain q).mp hq
    exact orank_le_iff.mp (by
      rw [hqk, h]; exact Nat.pow_le_pow_right (by norm_num) (chainSet_le hk))
  · obtain ⟨q₀, hq₀⟩ := hpow 0 (Nat.zero_le a)
    obtain ⟨v₀, hv₀⟩ := exists_orank_eq (A := A) Nat.card_pos
    exact ⟨q₀, v₀, by rw [hq₀]; norm_num, (hInChain q₀).mpr ⟨0, chainSet_zero a, hq₀⟩,
      (hValAt q₀ v₀ 0 (chainSet_zero a) hq₀).mpr hv₀, hv₀⟩
  · intro q q' v v' hc hv hv'
    obtain ⟨l, hl, hlpos, hql, hq'l⟩ := (hCons q q').mp hc
    have hvk : orank v = l / 2 := (hValAt q v (l / 2) (chainSet_half hl) hql).mp hv
    have hv'k : orank v' = l := (hValAt q' v' l hl hq'l).mp hv'
    have hla : l ≤ a := chainSet_le hl
    have hacard : a < Nat.card A := by rw [ha]; exact orank_lt_card i
    by_cases hpar : l % 2 = 0
    · refine Or.inl ⟨?_, by omega⟩
      rw [hql, hq'l, ← pow_add]
      congr 1
      omega
    · obtain ⟨s, hs⟩ := hpow (l / 2 + l / 2) (by omega)
      obtain ⟨u, hu⟩ := exists_orank_eq (A := A) (m := l / 2 + l / 2) (by omega)
      obtain ⟨one, hone⟩ := exists_orank_eq (A := A) (m := 1)
        (lt_of_le_of_lt Nat.one_le_two_pow hcard)
      refine Or.inr ⟨s, u, one, ?_, ?_, by omega, hone, by omega⟩
      · rw [hql, hs, ← pow_add]
      · rw [hs, hq'l]
        have : (2 : ℕ) ^ (l / 2 + l / 2) + 2 ^ (l / 2 + l / 2) = 2 ^ (l / 2 + l / 2 + 1) := by
          rw [pow_succ]; ring
        rw [this]
        congr 1
        omega

/-- **The certificate is exactly right**: `p` is the place value of `i` if and
only if the two elements can be guessed. This is the mathematics of
`DescriptiveComplexity.PowArithDef`; what remains is to write the conditions as
a formula. -/
theorem powCert_iff (i p : A) : (∃ Y E : A, PowCert i p Y E) ↔ orank p = 2 ^ orank i :=
  ⟨fun ⟨_, _, hc⟩ => powCert_sound hc, fun h => powCert_complete h⟩

end Certificate

/-! ### The formula -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- The chain is first-order: an equality, a position test and a bit. -/
theorem arithDef_inChain (p Y q : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => InChain (v p) (v Y) (v q)) :=
  ((arithDef_eq q p).or ((arithDef_isPos q).and (arithDef_bit q Y))).congr
    fun _ _ _ _ _ _ => Iff.rfl

/-- Consecutiveness is first-order: one universal quantifier says that nothing
of the chain lies between. -/
theorem arithDef_consChain (p Y q q' : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => ConsChain (v p) (v Y) (v q) (v q')) := by
  have hbet : ArithDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u => ¬ (InChain (u (Sum.inl p)) (u (Sum.inl Y)) (u (Sum.inr 0)) ∧
        (u (Sum.inl q) < u (Sum.inr 0) ∧ u (Sum.inr 0) < u (Sum.inl q')))) :=
    ((arithDef_inChain (Sum.inl p) (Sum.inl Y) (Sum.inr 0)).and
      ((arithDef_lt (Sum.inl q) (Sum.inr 0)).and (arithDef_lt (Sum.inr 0) (Sum.inl q')))).not
  refine ((arithDef_inChain p Y q).and ((arithDef_inChain p Y q').and
    ((arithDef_lt q q').and hbet.all))).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

/-- The value at an entry is first-order: the given `i` at the top, and
otherwise the field below the next entry
(`DescriptiveComplexity.arithDef_fieldAt`). -/
theorem arithDef_valAt (i p Y E q m : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => ValAt (v i) (v p) (v Y) (v E) (v q) (v m)) := by
  have hfield : ArithDef (L := L) (α := α ⊕ Fin 1)
      (fun _ _ _ _ _ u =>
        ConsChain (u (Sum.inl p)) (u (Sum.inl Y)) (u (Sum.inl q)) (u (Sum.inr 0)) ∧
          FieldAt (u (Sum.inl q)) (u (Sum.inr 0)) (u (Sum.inl E)) (u (Sum.inl m))) :=
    (arithDef_consChain (Sum.inl p) (Sum.inl Y) (Sum.inl q) (Sum.inr 0)).and
      (arithDef_fieldAt (Sum.inl q) (Sum.inr 0) (Sum.inl E) (Sum.inl m))
  refine (((arithDef_eq q p).and (arithDef_eq m i)).or
    ((arithDef_eq q p).not.and hfield.ex)).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Iff.rfl

/-- **The certificate is first-order**: four conditions, none of them about the
layout of the fields. -/
theorem arithDef_powCert (i p Y E : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => PowCert (v i) (v p) (v Y) (v E)) := by
  -- the top is the greatest entry
  have hc2 : ArithDef (L := L) (α := α)
      (fun _ _ _ _ _ v => ∀ q, InChain (v p) (v Y) q → q ≤ v p) :=
    ((arithDef_inChain (L := L) (α := α ⊕ Fin 1) (Sum.inl p) (Sum.inl Y) (Sum.inr 0)).imp
      (arithDef_le (Sum.inr 0) (Sum.inl p))).all
  -- the least entry is the place value `1`, and it carries `0`
  have hc3 : ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∃ q m : A,
      orank q = 1 ∧ InChain (v p) (v Y) q ∧ ValAt (v i) (v p) (v Y) (v E) q m ∧ orank m = 0) := by
    refine (((arithDef_isOne (L := L) (α := α ⊕ Fin 2) (Sum.inr 0)).and
      ((arithDef_inChain (Sum.inl p) (Sum.inl Y) (Sum.inr 0)).and
        ((arithDef_valAt (Sum.inl i) (Sum.inl p) (Sum.inl Y) (Sum.inl E)
          (Sum.inr 0) (Sum.inr 1)).and (arithDef_isZero (Sum.inr 1))))).exs).congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨q, m, hq⟩ => ⟨![q, m], hq⟩⟩
  -- consecutive entries square, or square and double
  have hodd : ArithDef (L := L) (α := (α ⊕ Fin 4) ⊕ Fin 3) (fun _ _ _ _ _ u =>
      orank (u (Sum.inl (Sum.inr 0))) * orank (u (Sum.inl (Sum.inr 0))) = orank (u (Sum.inr 0)) ∧
        (orank (u (Sum.inr 0)) + orank (u (Sum.inr 0)) = orank (u (Sum.inl (Sum.inr 1))) ∧
          (orank (u (Sum.inl (Sum.inr 2))) + orank (u (Sum.inl (Sum.inr 2))) =
              orank (u (Sum.inr 1)) ∧
            (orank (u (Sum.inr 2)) = 1 ∧
              orank (u (Sum.inr 1)) + orank (u (Sum.inr 2)) =
                orank (u (Sum.inl (Sum.inr 3))))))) :=
    (arithDef_times (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 0)) (Sum.inr 0)).and
      ((arithDef_plus (Sum.inr 0) (Sum.inr 0) (Sum.inl (Sum.inr 1))).and
        ((arithDef_plus (Sum.inl (Sum.inr 2)) (Sum.inl (Sum.inr 2)) (Sum.inr 1)).and
          ((arithDef_isOne (Sum.inr 2)).and
            (arithDef_plus (Sum.inr 1) (Sum.inr 2) (Sum.inl (Sum.inr 3))))))
  have hoddEx : ArithDef (L := L) (α := α ⊕ Fin 4) (fun A _ _ _ _ u => ∃ s v w : A,
      orank (u (Sum.inr 0)) * orank (u (Sum.inr 0)) = orank s ∧
        orank s + orank s = orank (u (Sum.inr 1)) ∧
          orank (u (Sum.inr 2)) + orank (u (Sum.inr 2)) = orank v ∧
            orank w = 1 ∧ orank v + orank w = orank (u (Sum.inr 3))) := by
    refine hodd.exs.congr fun A _ _ _ _ u => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun ⟨t, ht⟩ => ⟨t 0, t 1, t 2, ht⟩, fun ⟨s, v, w, hs⟩ => ⟨![s, v, w], hs⟩⟩
  have hc4 : ArithDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ q q' m m' : A,
      ConsChain (v p) (v Y) q q' → ValAt (v i) (v p) (v Y) (v E) q m →
        ValAt (v i) (v p) (v Y) (v E) q' m' →
          (orank q * orank q = orank q' ∧ orank m + orank m = orank m') ∨
            (∃ s u one : A, orank q * orank q = orank s ∧ orank s + orank s = orank q' ∧
              orank m + orank m = orank u ∧ orank one = 1 ∧
                orank u + orank one = orank m')) := by
    refine ((arithDef_consChain (L := L) (α := α ⊕ Fin 4) (Sum.inl p) (Sum.inl Y)
      (Sum.inr 0) (Sum.inr 1)).imp
      ((arithDef_valAt (Sum.inl i) (Sum.inl p) (Sum.inl Y) (Sum.inl E)
        (Sum.inr 0) (Sum.inr 2)).imp
        ((arithDef_valAt (Sum.inl i) (Sum.inl p) (Sum.inl Y) (Sum.inl E)
          (Sum.inr 1) (Sum.inr 3)).imp
          (((arithDef_times (Sum.inr 0) (Sum.inr 0) (Sum.inr 1)).and
            (arithDef_plus (Sum.inr 2) (Sum.inr 2) (Sum.inr 3))).or hoddEx)))).alls.congr
      fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h q q' m m' => h ![q, q', m, m'], fun h w => h (w 0) (w 1) (w 2) (w 3)⟩
  exact ((arithDef_isPos p).and (hc2.and (hc3.and hc4))).congr fun _ _ _ _ _ _ => Iff.rfl

/-- **The naming bridge, proved**: the graph of `i ↦ 2 ^ i` is a formula of
`FO(≤, +, ×)`, so the index naming of the bit positions costs the logic nothing
after all. This is [Immerman 1999][immerman1999descriptive] Thm 1.17(2), and it
is the half of Immerman's mutual definability that turns the machine model's
logic `FO(≤, BIT)` into a fragment of `FO(≤, +, ×)`.

The formula guesses two elements – the doubling chain below `p`, and its
exponents packed into the fields the chain delimits – and states three
conditions on them; `DescriptiveComplexity.powCert_iff` is that this is exactly
right. -/
theorem powArithDef (L : Language.{0, 0}) : PowArithDef L := by
  intro α i p
  refine (arithDef_powCert (L := L) (α := α ⊕ Fin 2) (Sum.inl i) (Sum.inl p)
    (Sum.inr 0) (Sum.inr 1)).exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  refine Iff.trans ?_ (powCert_iff (v i) (v p))
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨Y, E, h⟩ => ⟨![Y, E], h⟩⟩

end Definability

end DescriptiveComplexity
