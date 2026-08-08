/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Machine

/-!
# The arithmetic a sweep can do: comparison and addition, bit by bit

The base of a machine of `DescriptiveComplexity.LogTime.Machine` never evaluates
a numeric predicate; if it is to compare or to add, it has to *build* the
operation out of bits. This file does so, and the two constructions are the
bit-level analogues of `DescriptiveComplexity.HeadArith`'s `plusP` one resource
bound higher:

* `DescriptiveComplexity.leSweep` – the **comparison**, one state bit carrying
  the verdict on the positions read so far, overwritten whenever the two
  registers differ (`DescriptiveComplexity.leSweep_accepts`);
* `DescriptiveComplexity.plusSweep` – the **ripple-carry addition**, one state
  bit for the carry and one for “every output bit has matched so far”, accepting
  when the last carry is out and nothing mismatched
  (`DescriptiveComplexity.plusSweep_accepts`).

Both are single passes from the lowest position upwards, both use a constant
number of state bits, and neither reads the instance – so the machine model is
not vacuous: the order and the addition of the numeric predicates are *computed*
by it, from bits alone.

## Where the arithmetic stops

Multiplication is **not** here, and not for lack of effort: a sweep carries a
constant number of bits past each position, whereas the schoolbook product of
two `log n`-bit numbers accumulates a column count that grows with the number of
positions. That boundary is the honest limit of the model – and the reason the
converse of `DescriptiveComplexity.LTDecidable.ac0Definable` is out of reach
here; see the discussion in `DescriptiveComplexity.LogTime.Simulate`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### Peeling a bit off a remainder -/

/-- The remainder modulo the next power of two adds one bit. -/
theorem mod_two_pow_succ (x k : ℕ) :
    x % 2 ^ (k + 1) = x % 2 ^ k + (if x.testBit k then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ]
  cases hb : x.testBit k with
  | false =>
    have h : x / 2 ^ k % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb
      simp only [decide_eq_false_iff_not] at hb
      omega
    simp [h]
  | true =>
    have h : x / 2 ^ k % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb
      simpa using hb
    simp [h]

/-- A rank is its own remainder modulo the place value above the top
position. -/
theorem orank_mod_two_pow_posCount {A : Type} [LinearOrder A] [Finite A] (a : A) :
    orank a % 2 ^ posCount A = orank a :=
  Nat.mod_eq_of_lt (lt_of_lt_of_le (orank_lt_card a) (Nat.le_pow_clog (by norm_num) _))

/-! ### Comparison -/

/-- **The comparison sweep**: one state bit, holding the verdict on the
positions read so far. A position where the registers differ overwrites it; a
position where they agree keeps it. Read from the lowest position upwards, the
verdict left at the end is the comparison of the two registers. -/
@[reducible] def leSweep : Sweep 2 where
  σ := 1
  init := fun _ => true
  step := fun _ =>
    .or (.and (.not (.var (Sum.inr 0))) (.var (Sum.inr 1)))
      (.and (.var (Sum.inl 0))
        (.or (.and (.var (Sum.inr 0)) (.var (Sum.inr 1)))
          (.and (.not (.var (Sum.inr 0))) (.not (.var (Sum.inr 1))))))
  acc := .var 0

section Comparison

variable {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
/-- The invariant of the comparison sweep: after the positions below `i`, the
state bit compares the two registers modulo `2 ^ i`. -/
theorem leSweep_state (x : Fin 2 → A) :
    ∀ i : ℕ, (leSweep.state x i 0 = true ↔ orank (x 0) % 2 ^ i ≤ orank (x 1) % 2 ^ i) := by
  intro i
  induction i with
  | zero => simp [leSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (orank (x 0)) i
    have hy := mod_two_pow_succ (orank (x 1)) i
    have hxlt : orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    obtain ⟨st, hst⟩ : ∃ st, leSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ih
    rw [leSweep.state_succ x i 0, hst]
    simp only [leSweep, BitExpr.eval, Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true']
    rw [hx, hy]
    cases ha : (orank (x 0)).testBit i <;> cases hb : (orank (x 1)).testBit i <;>
      simp only [ih, reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
        or_false, false_or, true_iff, false_iff] <;> omega

/-- **The comparison sweep decides the order**: the machine model computes `≤`,
from bits alone. -/
theorem leSweep_accepts (x : Fin 2 → A) : leSweep.Accepts x ↔ x 0 ≤ x 1 := by
  rw [Sweep.Accepts]
  have h : leSweep.acc.eval (leSweep.state x (posCount A)) = leSweep.state x (posCount A) 0 := rfl
  rw [h, leSweep_state x (posCount A), orank_mod_two_pow_posCount,
    orank_mod_two_pow_posCount]
  exact orank_le_iff

end Comparison

/-! ### Addition -/

/-- **The ripple-carry addition sweep**: state bit `0` is the carry, state bit
`1` records that every output bit has matched the third register so far. The
sweep accepts when nothing has mismatched and the last carry is out – which is
the statement that the sum does not overflow the universe. -/
@[reducible] def plusSweep : Sweep 3 where
  σ := 2
  init := ![false, true]
  step := ![
    -- the carry: the majority of the two input bits and the incoming carry
    .or (.and (.var (Sum.inr 0)) (.var (Sum.inr 1)))
      (.or (.and (.var (Sum.inr 0)) (.var (Sum.inl 0)))
        (.and (.var (Sum.inr 1)) (.var (Sum.inl 0)))),
    -- the match: the previous matches, and this output bit is the sum bit
    .and (.var (Sum.inl 1))
      (.or
        (.and (.var (Sum.inr 2))
          (.or (.and (.var (Sum.inr 0)) (.and (.var (Sum.inr 1)) (.var (Sum.inl 0))))
            (.or (.and (.var (Sum.inr 0)) (.and (.not (.var (Sum.inr 1)))
                (.not (.var (Sum.inl 0)))))
              (.or (.and (.not (.var (Sum.inr 0))) (.and (.var (Sum.inr 1))
                  (.not (.var (Sum.inl 0)))))
                (.and (.not (.var (Sum.inr 0))) (.and (.not (.var (Sum.inr 1)))
                  (.var (Sum.inl 0))))))))
        (.and (.not (.var (Sum.inr 2)))
          (.or (.and (.var (Sum.inr 0)) (.and (.var (Sum.inr 1)) (.not (.var (Sum.inl 0)))))
            (.or (.and (.var (Sum.inr 0)) (.and (.not (.var (Sum.inr 1))) (.var (Sum.inl 0))))
              (.or (.and (.not (.var (Sum.inr 0))) (.and (.var (Sum.inr 1))
                  (.var (Sum.inl 0))))
                (.and (.not (.var (Sum.inr 0))) (.and (.not (.var (Sum.inr 1)))
                  (.not (.var (Sum.inl 0))))))))))]
  acc := .and (.var 1) (.not (.var 0))

section Addition

variable {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
/-- The carry of the addition sweep is the carry of the two remainders. -/
theorem plusSweep_carry (x : Fin 3 → A) :
    ∀ i : ℕ, (plusSweep.state x i 0 = true ↔
      2 ^ i ≤ orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i) := by
  intro i
  induction i with
  | zero => simp [plusSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (orank (x 0)) i
    have hy := mod_two_pow_succ (orank (x 1)) i
    have hxlt : orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hpow : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ih
    rw [plusSweep.state_succ x i 0, hst]
    simp only [plusSweep, Matrix.cons_val_zero, BitExpr.eval, Sum.elim_inl, Sum.elim_inr,
      Bool.or_eq_true, Bool.and_eq_true]
    rw [hx, hy, hpow]
    cases ha : (orank (x 0)).testBit i <;> cases hb : (orank (x 1)).testBit i <;>
      simp only [ih, reduceIte, Bool.false_eq_true, and_true, and_false, false_and, true_and,
        or_false, false_or, true_iff, false_iff, true_or] <;> omega

omit [Finite A] in
/-- The carry bit is set when the remainders overflow. -/
theorem plusSweep_carry_true (x : Fin 3 → A) (i : ℕ)
    (h : 2 ^ i ≤ orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i) :
    plusSweep.state x i 0 = true := (plusSweep_carry x i).mpr h

omit [Finite A] in
/-- The carry bit is clear when the remainders do not overflow. -/
theorem plusSweep_carry_false (x : Fin 3 → A) (i : ℕ)
    (h : ¬ 2 ^ i ≤ orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i) :
    plusSweep.state x i 0 = false := by
  cases hk : plusSweep.state x i 0 with
  | false => rfl
  | true => exact absurd ((plusSweep_carry x i).mp hk) h

omit [Finite A] in
/-- The match bit of the addition sweep records that the two remainders add up,
up to the carry it has produced. -/
theorem plusSweep_ok (x : Fin 3 → A) :
    ∀ i : ℕ, (plusSweep.state x i 1 = true ↔
      orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i =
        orank (x 2) % 2 ^ i +
          (if 2 ^ i ≤ orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i then 2 ^ i else 0)) := by
  intro i
  induction i with
  | zero => simp [plusSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (orank (x 0)) i
    have hy := mod_two_pow_succ (orank (x 1)) i
    have hz := mod_two_pow_succ (orank (x 2)) i
    have hxlt : orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hzlt : orank (x 2) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hpow : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    by_cases hcar : 2 ^ i ≤ orank (x 0) % 2 ^ i + orank (x 1) % 2 ^ i
    · have hk := plusSweep_carry_true x i hcar
      obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
      rw [hst] at ih hk
      rw [plusSweep.state_succ x i 1, hst]
      simp only [plusSweep, Matrix.cons_val_one, Matrix.cons_val_fin_one, BitExpr.eval,
        Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rw [hx, hy, hz, hpow, ih, hk, if_pos hcar]
      cases ha : (orank (x 0)).testBit i <;> cases hb : (orank (x 1)).testBit i <;>
        cases hc : (orank (x 2)).testBit i <;>
        simp only [reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, or_true, false_iff] <;> split_ifs <;> omega
    · have hk := plusSweep_carry_false x i hcar
      obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
      rw [hst] at ih hk
      rw [plusSweep.state_succ x i 1, hst]
      simp only [plusSweep, Matrix.cons_val_one, Matrix.cons_val_fin_one, BitExpr.eval,
        Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rw [hx, hy, hz, hpow, ih, hk, if_neg hcar]
      cases ha : (orank (x 0)).testBit i <;> cases hb : (orank (x 1)).testBit i <;>
        cases hc : (orank (x 2)).testBit i <;>
        simp only [reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, or_true, false_iff] <;> split_ifs <;> omega

/-- **The addition sweep decides addition**: the machine model computes the
numeric predicate `plus`, from bits alone – the bit-level analogue of the head
program `DescriptiveComplexity.plusP`. -/
theorem plusSweep_accepts (x : Fin 3 → A) :
    plusSweep.Accepts x ↔ orank (x 0) + orank (x 1) = orank (x 2) := by
  have hok := plusSweep_ok x (posCount A)
  have hcarry := plusSweep_carry x (posCount A)
  rw [orank_mod_two_pow_posCount, orank_mod_two_pow_posCount] at hok hcarry
  rw [orank_mod_two_pow_posCount] at hok
  have hzlt : orank (x 2) < 2 ^ posCount A :=
    lt_of_lt_of_le (orank_lt_card _) (Nat.le_pow_clog (by norm_num) _)
  rw [Sweep.Accepts]
  have hacc : plusSweep.acc.eval (plusSweep.state x (posCount A)) =
      (plusSweep.state x (posCount A) 1 && !(plusSweep.state x (posCount A) 0)) := rfl
  rw [hacc]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h0⟩
    have hcar : ¬ 2 ^ posCount A ≤ orank (x 0) + orank (x 1) := by
      intro hcon
      rw [hcarry.mpr hcon] at h0
      exact Bool.noConfusion h0
    rw [hok, if_neg hcar] at h1
    omega
  · intro heq
    have hcar : ¬ 2 ^ posCount A ≤ orank (x 0) + orank (x 1) := by
      rw [heq]
      omega
    refine ⟨hok.mpr (by rw [if_neg hcar]; omega), ?_⟩
    cases hk : plusSweep.state x (posCount A) 0 with
    | false => rfl
    | true => exact absurd (hcarry.mp hk) hcar

end Addition


/-! ### Positions and bits -/

/-- **The position test**: one state bit records that a bit of the register has
been seen, another that a second one has. The sweep accepts when exactly one bit
is set, which is what it is for a rank to be a place value. -/
@[reducible] def oneBitSweep : Sweep 1 where
  σ := 2
  init := ![false, false]
  step := ![
    -- seen: a bit has been read
    .or (.var (Sum.inl 0)) (.var (Sum.inr 0)),
    -- bad: a second bit has been read
    .or (.var (Sum.inl 1)) (.and (.var (Sum.inl 0)) (.var (Sum.inr 0)))]
  acc := .and (.var 0) (.not (.var 1))

/-- **The bit-implication sweep**: the second register carries a `1` wherever
the first does. -/
@[reducible] def impliesSweep : Sweep 2 where
  σ := 1
  init := fun _ => true
  step := fun _ =>
    .and (.var (Sum.inl 0)) (.or (.not (.var (Sum.inr 0))) (.var (Sum.inr 1)))
  acc := .var 0

section Positions

variable {A : Type} [LinearOrder A] [Finite A]

omit [Finite A] in
/-- The invariant of the position test: the two state bits track “some bit
below `i` is set” and “at most one is”. -/
theorem oneBitSweep_state (x : Fin 1 → A) :
    ∀ i : ℕ, (oneBitSweep.state x i 0 = true ↔ orank (x 0) % 2 ^ i ≠ 0) ∧
      (oneBitSweep.state x i 1 = true → oneBitSweep.state x i 0 = true) ∧
      ((oneBitSweep.state x i 0 = true ∧ oneBitSweep.state x i 1 = false) ↔
        ∃ j, orank (x 0) % 2 ^ i = 2 ^ j) := by
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [oneBitSweep, Nat.mod_one]
    · simp [oneBitSweep]
    · constructor
      · rintro ⟨h, -⟩
        exact absurd h (by simp [oneBitSweep])
      · rintro ⟨j, hj⟩
        rw [pow_zero, Nat.mod_one] at hj
        exact absurd hj.symm (Nat.two_pow_pos j).ne'
  | succ i ih =>
    obtain ⟨ihseen, ihmono, ihone⟩ := ih
    have hx := mod_two_pow_succ (orank (x 0)) i
    have hxlt : orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    obtain ⟨st, hst⟩ : ∃ st, oneBitSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ihseen ihmono ihone
    have hseen : oneBitSweep.state x (i + 1) 0 =
        (st 0 || (orank (x 0)).testBit i) := by
      rw [oneBitSweep.state_succ x i 0, hst]; rfl
    have hbad : oneBitSweep.state x (i + 1) 1 =
        (st 1 || (st 0 && (orank (x 0)).testBit i)) := by
      rw [oneBitSweep.state_succ x i 1, hst]; rfl
    rw [hseen, hbad]
    cases ha : (orank (x 0)).testBit i
    · have hval : orank (x 0) % 2 ^ (i + 1) = orank (x 0) % 2 ^ i := by
        rw [hx, ha]; simp
      rw [hval]
      simp only [Bool.or_false, Bool.and_false]
      exact ⟨ihseen, ihmono, ihone⟩
    · have hval : orank (x 0) % 2 ^ (i + 1) = orank (x 0) % 2 ^ i + 2 ^ i := by
        rw [hx, ha]; simp
      rw [hval]
      simp only [Bool.or_true, Bool.and_true]
      refine ⟨?_, fun _ => trivial, ?_⟩
      · have := Nat.two_pow_pos i
        simp only [true_iff]
        omega
      · simp only [true_and]
        constructor
        · intro hb
          have hst0 : st 0 = false := by
            cases hs : st 0 with
            | false => rfl
            | true => rw [hs] at hb; exact absurd hb (by simp)
          have hzero : orank (x 0) % 2 ^ i = 0 := by
            by_contra hne
            exact absurd (ihseen.mpr hne) (by rw [hst0]; simp)
          exact ⟨i, by omega⟩
        · rintro ⟨j, hj⟩
          have hle : 2 ^ i ≤ 2 ^ j := by omega
          have hlt : 2 ^ j < 2 ^ (i + 1) := by rw [pow_succ]; omega
          have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
          have hji : j < i + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
          have hje : j = i := by omega
          have hzero : orank (x 0) % 2 ^ i = 0 := by rw [hje] at hj; omega
          have hst0 : st 0 = false := by
            cases hs : st 0 with
            | false => rfl
            | true => exact absurd (ihseen.mp hs) (by omega)
          have hst1 : st 1 = false := by
            cases hs : st 1 with
            | false => rfl
            | true => rw [ihmono hs] at hst0; exact absurd hst0 (by simp)
          simp [hst0, hst1]

/-- **The position test decides `IsPos`**: a rank is a place value exactly when
exactly one of its bits is set. -/
theorem oneBitSweep_accepts (x : Fin 1 → A) : oneBitSweep.Accepts x ↔ IsPos (x 0) := by
  obtain ⟨-, -, hone⟩ := oneBitSweep_state x (posCount A)
  rw [orank_mod_two_pow_posCount] at hone
  have hacc : oneBitSweep.Accepts x ↔
      (oneBitSweep.state x (posCount A) 0 = true ∧
        oneBitSweep.state x (posCount A) 1 = false) := by
    have h : oneBitSweep.Accepts x ↔
        (oneBitSweep.state x (posCount A) 0 &&
          !(oneBitSweep.state x (posCount A) 1)) = true := Iff.rfl
    rw [h]
    simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [hacc, hone]
  exact Iff.rfl

omit [Finite A] in
/-- The invariant of the bit-implication sweep. -/
theorem impliesSweep_state (x : Fin 2 → A) :
    ∀ i : ℕ, (impliesSweep.state x i 0 = true ↔
      ∀ j < i, (orank (x 0)).testBit j = true → (orank (x 1)).testBit j = true) := by
  intro i
  induction i with
  | zero => simp [impliesSweep]
  | succ i ih =>
    obtain ⟨st, hst⟩ : ∃ st, impliesSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ih
    have hstep : impliesSweep.state x (i + 1) 0 =
        (st 0 && (!(orank (x 0)).testBit i || (orank (x 1)).testBit i)) := by
      rw [impliesSweep.state_succ x i 0, hst]; rfl
    rw [hstep]
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨hall, hhere⟩ j hj hbit
      rcases Nat.lt_or_ge j i with hlt | hge
      · exact hall j hlt hbit
      · have hji : j = i := by omega
        subst hji
        rcases hhere with h | h
        · exact absurd hbit (by rw [h]; simp)
        · exact h
    · intro hall
      refine ⟨fun j hj => hall j (by omega), ?_⟩
      cases hb : (orank (x 0)).testBit i with
      | false => exact Or.inl rfl
      | true => exact Or.inr (hall i (by omega) hb)

/-- **The bit-implication sweep decides bitwise implication**, over all
positions: above them every rank has a zero bit, so the bound is immaterial. -/
theorem impliesSweep_accepts (x : Fin 2 → A) :
    impliesSweep.Accepts x ↔
      ∀ j, (orank (x 0)).testBit j = true → (orank (x 1)).testBit j = true := by
  have h := impliesSweep_state x (posCount A)
  have hacc : impliesSweep.Accepts x ↔ impliesSweep.state x (posCount A) 0 = true := Iff.rfl
  rw [hacc, h]
  constructor
  · intro hall j hbit
    rcases Nat.lt_or_ge j (posCount A) with hlt | hge
    · exact hall j hlt hbit
    · exact absurd hbit (by rw [testBit_orank_eq_false hge]; simp)
  · exact fun hall j _ => hall j

/-- **A guarded bit is a bitwise implication**: when `p` is a position, the bit
of `y` at `p` is set exactly when every bit of `p` is a bit of `y` – `p` having
only one. This is the form a sweep can check. -/
theorem bitAt_iff_bits (p y : A) :
    (IsPos p ∧ BitAt p y) ↔
      (IsPos p ∧ ∀ j, (orank p).testBit j = true → (orank y).testBit j = true) := by
  refine and_congr_right fun hpos => ?_
  obtain ⟨i, hi⟩ := hpos
  rw [bitAt_iff hi]
  constructor
  · intro hbit j hj
    rw [hi, Nat.testBit_two_pow] at hj
    simp only [decide_eq_true_eq] at hj
    exact hj ▸ hbit
  · intro hall
    exact hall i (by rw [hi, Nat.testBit_two_pow]; simp)

/-- **The bit atom is two sweeps**: that `p` is a position, and that every bit
of `p` is a bit of `y`. This is `DescriptiveComplexity.BitAt` guarded by
`DescriptiveComplexity.IsPos`, decided from bits alone. -/
theorem bitAt_iff_sweeps (p y : A) :
    (IsPos p ∧ BitAt p y) ↔
      (oneBitSweep.Accepts ![p] ∧ impliesSweep.Accepts ![p, y]) := by
  rw [bitAt_iff_bits, oneBitSweep_accepts, impliesSweep_accepts]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

end Positions

end DescriptiveComplexity
