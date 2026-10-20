/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.Machine
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

namespace Lax895169.LogTimeMachines
end Lax895169.LogTimeMachines

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank posCount)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.LogTimeMachines (Sweep)
end Lax895169Proofs.DescriptiveComplexity

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
positions. That boundary is the honest limit of a *sweep*, and it is why the
model has a second primitive that is not one: `DescriptiveComplexity.BaseTest.bit`
reads a bit at an address instead of computing anything. Eliminating `×` in
favor of that read is the classical theorem the model waits on, not a widening
of this file; see `DescriptiveComplexity.LogTime`.
-/

namespace Lax895169Proofs.DescriptiveComplexity

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
    Lax895169.BitPredicate.orank a % 2 ^ Lax895169.BitPredicate.posCount A = Lax895169.BitPredicate.orank a :=
  Nat.mod_eq_of_lt (lt_of_lt_of_le (orank_lt_card a) (Nat.le_pow_clog (by norm_num) _))

/-! ### Comparison -/

/-- **The comparison sweep**: one state bit, holding the verdict on the
positions read so far. A position where the registers differ overwrites it; a
position where they agree keeps it. Read from the lowest position upwards, the
verdict left at the end is the comparison of the two registers. -/
@[reducible] def leSweep : Lax895169.LogTimeMachines.Sweep 2 where
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
    ∀ i : ℕ, (leSweep.state x i 0 = true ↔ Lax895169.BitPredicate.orank (x 0) % 2 ^ i ≤ Lax895169.BitPredicate.orank (x 1) % 2 ^ i) := by
  intro i
  induction i with
  | zero => simp [leSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 0)) i
    have hy := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 1)) i
    have hxlt : Lax895169.BitPredicate.orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : Lax895169.BitPredicate.orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    obtain ⟨st, hst⟩ : ∃ st, leSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ih
    rw [leSweep.state_succ x i 0, hst]
    simp only [leSweep, Lax895169.LogTimeMachines.BitExpr.eval, Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true']
    rw [hx, hy]
    cases ha : (Lax895169.BitPredicate.orank (x 0)).testBit i <;> cases hb : (Lax895169.BitPredicate.orank (x 1)).testBit i <;>
      simp only [ih, reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
        or_false, false_or, true_iff, false_iff] <;> omega

/-- **The comparison sweep decides the order**: the machine model computes `≤`,
from bits alone. -/
theorem leSweep_accepts (x : Fin 2 → A) : leSweep.Accepts x ↔ x 0 ≤ x 1 := by
  rw [Lax895169.LogTimeMachines.Sweep.Accepts]
  have h : leSweep.acc.eval (leSweep.state x (Lax895169.BitPredicate.posCount A)) = leSweep.state x (Lax895169.BitPredicate.posCount A) 0 := rfl
  rw [h, leSweep_state x (Lax895169.BitPredicate.posCount A), orank_mod_two_pow_posCount,
    orank_mod_two_pow_posCount]
  exact orank_le_iff

end Comparison

/-! ### Addition -/

/-- **The ripple-carry addition sweep**: state bit `0` is the carry, state bit
`1` records that every output bit has matched the third register so far. The
sweep accepts when nothing has mismatched and the last carry is out – which is
the statement that the sum does not overflow the universe. -/
@[reducible] def plusSweep : Lax895169.LogTimeMachines.Sweep 3 where
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
      2 ^ i ≤ Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i) := by
  intro i
  induction i with
  | zero => simp [plusSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 0)) i
    have hy := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 1)) i
    have hxlt : Lax895169.BitPredicate.orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : Lax895169.BitPredicate.orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hpow : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
    rw [hst] at ih
    rw [plusSweep.state_succ x i 0, hst]
    simp only [plusSweep, Matrix.cons_val_zero, Lax895169.LogTimeMachines.BitExpr.eval, Sum.elim_inl, Sum.elim_inr,
      Bool.or_eq_true, Bool.and_eq_true]
    rw [hx, hy, hpow]
    cases ha : (Lax895169.BitPredicate.orank (x 0)).testBit i <;> cases hb : (Lax895169.BitPredicate.orank (x 1)).testBit i <;>
      simp only [ih, reduceIte, Bool.false_eq_true, and_true, and_false, false_and, true_and,
        or_false, false_or, true_iff, false_iff, true_or] <;> omega

omit [Finite A] in
/-- The carry bit is set when the remainders overflow. -/
theorem plusSweep_carry_true (x : Fin 3 → A) (i : ℕ)
    (h : 2 ^ i ≤ Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i) :
    plusSweep.state x i 0 = true := (plusSweep_carry x i).mpr h

omit [Finite A] in
/-- The carry bit is clear when the remainders do not overflow. -/
theorem plusSweep_carry_false (x : Fin 3 → A) (i : ℕ)
    (h : ¬ 2 ^ i ≤ Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i) :
    plusSweep.state x i 0 = false := by
  cases hk : plusSweep.state x i 0 with
  | false => rfl
  | true => exact absurd ((plusSweep_carry x i).mp hk) h

omit [Finite A] in
/-- The match bit of the addition sweep records that the two remainders add up,
up to the carry it has produced. -/
theorem plusSweep_ok (x : Fin 3 → A) :
    ∀ i : ℕ, (plusSweep.state x i 1 = true ↔
      Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i =
        Lax895169.BitPredicate.orank (x 2) % 2 ^ i +
          (if 2 ^ i ≤ Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i then 2 ^ i else 0)) := by
  intro i
  induction i with
  | zero => simp [plusSweep, Nat.mod_one]
  | succ i ih =>
    have hx := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 0)) i
    have hy := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 1)) i
    have hz := mod_two_pow_succ (Lax895169.BitPredicate.orank (x 2)) i
    have hxlt : Lax895169.BitPredicate.orank (x 0) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hylt : Lax895169.BitPredicate.orank (x 1) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hzlt : Lax895169.BitPredicate.orank (x 2) % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
    have hpow : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    by_cases hcar : 2 ^ i ≤ Lax895169.BitPredicate.orank (x 0) % 2 ^ i + Lax895169.BitPredicate.orank (x 1) % 2 ^ i
    · have hk := plusSweep_carry_true x i hcar
      obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
      rw [hst] at ih hk
      rw [plusSweep.state_succ x i 1, hst]
      simp only [plusSweep, Matrix.cons_val_one, Matrix.cons_val_fin_one, Lax895169.LogTimeMachines.BitExpr.eval,
        Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rw [hx, hy, hz, hpow, ih, hk, if_pos hcar]
      cases ha : (Lax895169.BitPredicate.orank (x 0)).testBit i <;> cases hb : (Lax895169.BitPredicate.orank (x 1)).testBit i <;>
        cases hc : (Lax895169.BitPredicate.orank (x 2)).testBit i <;>
        simp only [reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, or_true, false_iff] <;> split_ifs <;> omega
    · have hk := plusSweep_carry_false x i hcar
      obtain ⟨st, hst⟩ : ∃ st, plusSweep.state x i = st := ⟨_, rfl⟩
      rw [hst] at ih hk
      rw [plusSweep.state_succ x i 1, hst]
      simp only [plusSweep, Matrix.cons_val_one, Matrix.cons_val_fin_one, Lax895169.LogTimeMachines.BitExpr.eval,
        Sum.elim_inl, Sum.elim_inr, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      rw [hx, hy, hz, hpow, ih, hk, if_neg hcar]
      cases ha : (Lax895169.BitPredicate.orank (x 0)).testBit i <;> cases hb : (Lax895169.BitPredicate.orank (x 1)).testBit i <;>
        cases hc : (Lax895169.BitPredicate.orank (x 2)).testBit i <;>
        simp only [reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
          or_false, or_true, false_iff] <;> split_ifs <;> omega

/-- **The addition sweep decides addition**: the machine model computes the
numeric predicate `plus`, from bits alone – the bit-level analogue of the head
program `DescriptiveComplexity.HeadProgram.plusP`. -/
theorem plusSweep_accepts (x : Fin 3 → A) :
    plusSweep.Accepts x ↔ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) = Lax895169.BitPredicate.orank (x 2) := by
  have hok := plusSweep_ok x (Lax895169.BitPredicate.posCount A)
  have hcarry := plusSweep_carry x (Lax895169.BitPredicate.posCount A)
  rw [orank_mod_two_pow_posCount, orank_mod_two_pow_posCount] at hok hcarry
  rw [orank_mod_two_pow_posCount] at hok
  have hzlt : Lax895169.BitPredicate.orank (x 2) < 2 ^ Lax895169.BitPredicate.posCount A :=
    lt_of_lt_of_le (orank_lt_card _) (Nat.le_pow_clog (by norm_num) _)
  rw [Lax895169.LogTimeMachines.Sweep.Accepts]
  have hacc : plusSweep.acc.eval (plusSweep.state x (Lax895169.BitPredicate.posCount A)) =
      (plusSweep.state x (Lax895169.BitPredicate.posCount A) 1 && !(plusSweep.state x (Lax895169.BitPredicate.posCount A) 0)) := rfl
  rw [hacc]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h0⟩
    have hcar : ¬ 2 ^ Lax895169.BitPredicate.posCount A ≤ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) := by
      intro hcon
      rw [hcarry.mpr hcon] at h0
      exact Bool.noConfusion h0
    rw [hok, if_neg hcar] at h1
    omega
  · intro heq
    have hcar : ¬ 2 ^ Lax895169.BitPredicate.posCount A ≤ Lax895169.BitPredicate.orank (x 0) + Lax895169.BitPredicate.orank (x 1) := by
      rw [heq]
      omega
    refine ⟨hok.mpr (by rw [if_neg hcar]; omega), ?_⟩
    cases hk : plusSweep.state x (Lax895169.BitPredicate.posCount A) 0 with
    | false => rfl
    | true => exact absurd (hcarry.mp hk) hcar

end Addition

/-! ### The trivial sweep -/

/-- **The trivial sweep**: no state, no register, always accepting. It is what a
constant of the bit-level logic compiles to, so that a trivially true kernel
needs no dummy variable. -/
@[reducible] def trueSweep : Lax895169.LogTimeMachines.Sweep 0 where
  σ := 0
  init := Fin.elim0
  step := Fin.elim0
  acc := .tt

end Lax895169Proofs.DescriptiveComplexity


