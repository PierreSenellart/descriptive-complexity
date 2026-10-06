/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.Bits
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

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Fields: reading a packed number out of one element

An element of a finite ordered universe carries `log n` bits, and both halves of
Immerman's mutual definability pack *several* numbers into one such element: the
packing argument for `DescriptiveComplexity.PowArithDef` writes the doubling
chain's exponents side by side, and the Bit Sum Lemma writes a running sum after
each segment. What both need first is a way to *read* one of those numbers back,
and that is what this file gives:

> `DescriptiveComplexity.FieldAt p q x m`: the bits of `x` from the place value
> `p` (included) up to the place value `q` (excluded), read as the number `m`.

The definition is a division with remainder written flat – `x = lo + m * p +
hi * q` with `lo < p` and `m * p < q` – so every witness is at most `x`, hence a
rank of the universe, and the whole thing is a formula of `FO(≤, +, ×)`
(`DescriptiveComplexity.arithDef_fieldAt`). That is the same trick that makes
`DescriptiveComplexity.BitAt` first-order, one field wide instead of one bit:
`DescriptiveComplexity.fieldAt_two_pow_succ` is the bit as a one-bit field.

## What to prove with it

`DescriptiveComplexity.fieldAt_iff` reads the field as `x / 2 ^ a % 2 ^ (b - a)`,
`DescriptiveComplexity.fieldAt_unique` makes it a function, and
`DescriptiveComplexity.exists_fieldAt` says the value is always there to be read.
A construction that lays numbers out in an element states its layout with
`FieldAt` and never touches a bit again.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-! ### Fields of a natural number -/

section NatFields

/-- **A field is a division with remainder, twice**: `m` is the block of bits of
`x` from position `a` to position `b` exactly when `x` splits as a low part below
`2 ^ a`, the block scaled by `2 ^ a`, and a high part scaled by `2 ^ b`. Every
witness of the left-hand side is at most `x`, which is what makes the statement
survive the truncation of a finite universe. -/
theorem field_iff (x m a d : ℕ) :
    (∃ lo hi : ℕ, lo + (m * 2 ^ a + hi * 2 ^ (a + d)) = x ∧ lo < 2 ^ a ∧
        m * 2 ^ a < 2 ^ (a + d)) ↔
      m = x / 2 ^ a % 2 ^ d := by
  have hpa : (0 : ℕ) < 2 ^ a := Nat.two_pow_pos a
  have hpd : (0 : ℕ) < 2 ^ d := Nat.two_pow_pos d
  constructor
  · rintro ⟨lo, hi, hsum, hlo, hblk⟩
    have hmd : m < 2 ^ d := by
      have h := hblk
      rw [pow_add, Nat.mul_comm (2 ^ a) (2 ^ d)] at h
      exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
    have hx : x = lo + 2 ^ a * (m + hi * 2 ^ d) := by
      rw [← hsum, pow_add]
      ring
    have hdiv : x / 2 ^ a = m + hi * 2 ^ d := by
      rw [hx, Nat.add_mul_div_left _ _ hpa, Nat.div_eq_of_lt hlo]
      omega
    rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmd]
  · intro hm
    refine ⟨x % 2 ^ a, x / 2 ^ a / 2 ^ d, ?_, Nat.mod_lt _ hpa, ?_⟩
    · rw [hm, pow_add]
      calc x % 2 ^ a + (x / 2 ^ a % 2 ^ d * 2 ^ a + x / 2 ^ a / 2 ^ d * (2 ^ a * 2 ^ d))
          = x % 2 ^ a + 2 ^ a * (x / 2 ^ a % 2 ^ d + 2 ^ d * (x / 2 ^ a / 2 ^ d)) := by ring
        _ = x % 2 ^ a + 2 ^ a * (x / 2 ^ a) := by rw [Nat.mod_add_div (x / 2 ^ a) (2 ^ d)]
        _ = x := Nat.mod_add_div x (2 ^ a)
    · rw [hm, pow_add]
      have : x / 2 ^ a % 2 ^ d < 2 ^ d := Nat.mod_lt _ hpd
      calc x / 2 ^ a % 2 ^ d * 2 ^ a < 2 ^ d * 2 ^ a :=
            (Nat.mul_lt_mul_right hpa).mpr this
        _ = 2 ^ a * 2 ^ d := by ring

end NatFields

/-! ### Fields of an element -/

section Fields

variable {A : Type} [LinearOrder A] [Finite A]

/-- The order of the elements is the order of their ranks. -/
theorem lt_of_orank_lt {x y : A} (h : Lax895169.BitPredicate.orank x < Lax895169.BitPredicate.orank y) : x < y :=
  lt_of_not_ge fun hc => absurd (orank_le_iff.mpr hc) (by omega)

/-- **The field of `x` between the place values `p` and `q`**, read as the number
`m`: the flat form of “the bits of `x` from `p` up to `q`”. All three witnesses
are at most `x`, hence ranks of the universe. -/
def FieldAt (p q x m : A) : Prop :=
  ∃ lo hi : A, Lax895169.BitPredicate.orank lo + (Lax895169.BitPredicate.orank m * Lax895169.BitPredicate.orank p + Lax895169.BitPredicate.orank hi * Lax895169.BitPredicate.orank q) = Lax895169.BitPredicate.orank x ∧
    Lax895169.BitPredicate.orank lo < Lax895169.BitPredicate.orank p ∧ Lax895169.BitPredicate.orank m * Lax895169.BitPredicate.orank p < Lax895169.BitPredicate.orank q

/-- **What a field reads**: at place values `2 ^ a` and `2 ^ (a + d)`, the field
of `x` is the `d` bits of `x` above position `a`. -/
theorem fieldAt_iff {p q x m : A} {a d : ℕ} (hp : Lax895169.BitPredicate.orank p = 2 ^ a)
    (hq : Lax895169.BitPredicate.orank q = 2 ^ (a + d)) :
    FieldAt p q x m ↔ Lax895169.BitPredicate.orank m = Lax895169.BitPredicate.orank x / 2 ^ a % 2 ^ d := by
  rw [FieldAt, hp, hq]
  constructor
  · rintro ⟨lo, hi, hsum, hlo, hblk⟩
    exact (field_iff (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank m) a d).mp ⟨Lax895169.BitPredicate.orank lo, Lax895169.BitPredicate.orank hi, hsum, hlo, hblk⟩
  · intro hm
    obtain ⟨lo, hi, hsum, hlo, hblk⟩ := (field_iff (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank m) a d).mpr hm
    have hlox : lo ≤ Lax895169.BitPredicate.orank x := by omega
    have hhix : hi ≤ Lax895169.BitPredicate.orank x := by
      rcases Nat.eq_zero_or_pos hi with rfl | hpos
      · omega
      · have : hi ≤ hi * 2 ^ (a + d) := Nat.le_mul_of_pos_right hi (Nat.two_pow_pos _)
        omega
    obtain ⟨loA, hloA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hlox (orank_lt_card x))
    obtain ⟨hiA, hhiA⟩ := exists_orank_eq (A := A) (lt_of_le_of_lt hhix (orank_lt_card x))
    exact ⟨loA, hiA, by rw [hloA, hhiA]; exact hsum, by rw [hloA]; exact hlo, hblk⟩

/-- **A field is a function of its two ends**: at most one element reads it. -/
theorem fieldAt_unique {p q x m m' : A} {a d : ℕ} (hp : Lax895169.BitPredicate.orank p = 2 ^ a)
    (hq : Lax895169.BitPredicate.orank q = 2 ^ (a + d)) (h : FieldAt p q x m) (h' : FieldAt p q x m') : m = m' :=
  orank_inj (((fieldAt_iff hp hq).mp h).trans ((fieldAt_iff hp hq).mp h').symm)

/-- **A field is always there to be read**: its value is below `2 ^ d ≤ q`, hence
a rank of the universe. -/
theorem exists_fieldAt {p q x : A} {a d : ℕ} (hp : Lax895169.BitPredicate.orank p = 2 ^ a)
    (hq : Lax895169.BitPredicate.orank q = 2 ^ (a + d)) : ∃ m : A, FieldAt p q x m := by
  have hlt : Lax895169.BitPredicate.orank x / 2 ^ a % 2 ^ d < Nat.card A := by
    have h1 : Lax895169.BitPredicate.orank x / 2 ^ a % 2 ^ d ≤ Lax895169.BitPredicate.orank x := le_trans (Nat.mod_le _ _)
      (Nat.div_le_self _ _)
    exact lt_of_le_of_lt h1 (orank_lt_card x)
  obtain ⟨m, hm⟩ := exists_orank_eq (A := A) hlt
  exact ⟨m, (fieldAt_iff hp hq).mpr hm⟩

end Fields

/-! ### Definability -/

section Definability

variable {L : Language.{0, 0}} {α : Type}

/-- **A field is first-order in `≤`, `+` and `×`**: two guessed witnesses, two
products and two sums, with no bit in sight. This is the reading primitive both
halves of Immerman's mutual definability write their layouts with. -/
theorem arithDef_fieldAt (p q x m : α) :
    ArithDef (L := L) (fun _ _ _ _ _ v => FieldAt (v p) (v q) (v x) (v m)) := by
  -- the five bound variables: `lo`, `hi`, `m * p`, `hi * q`, and their sum
  have hbody : ArithDef (L := L) (α := α ⊕ Fin 5)
      (fun _ _ _ _ _ u =>
        Lax895169.BitPredicate.orank (u (Sum.inr 0)) + Lax895169.BitPredicate.orank (u (Sum.inr 4)) = Lax895169.BitPredicate.orank (u (Sum.inl x)) ∧
          (Lax895169.BitPredicate.orank (u (Sum.inl m)) * Lax895169.BitPredicate.orank (u (Sum.inl p)) = Lax895169.BitPredicate.orank (u (Sum.inr 2)) ∧
            (Lax895169.BitPredicate.orank (u (Sum.inr 1)) * Lax895169.BitPredicate.orank (u (Sum.inl q)) = Lax895169.BitPredicate.orank (u (Sum.inr 3)) ∧
              (Lax895169.BitPredicate.orank (u (Sum.inr 2)) + Lax895169.BitPredicate.orank (u (Sum.inr 3)) = Lax895169.BitPredicate.orank (u (Sum.inr 4)) ∧
                (u (Sum.inr 0) < u (Sum.inl p) ∧ u (Sum.inr 2) < u (Sum.inl q)))))) :=
    (arithDef_plus (Sum.inr 0) (Sum.inr 4) (Sum.inl x)).and
      ((arithDef_times (Sum.inl m) (Sum.inl p) (Sum.inr 2)).and
        ((arithDef_times (Sum.inr 1) (Sum.inl q) (Sum.inr 3)).and
          ((arithDef_plus (Sum.inr 2) (Sum.inr 3) (Sum.inr 4)).and
            ((arithDef_lt (Sum.inr 0) (Sum.inl p)).and
              (arithDef_lt (Sum.inr 2) (Sum.inl q))))))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, FieldAt]
  constructor
  · rintro ⟨w, hsum, hmp, hhq, hadd, hlo, hblk⟩
    refine ⟨w 0, w 1, ?_, orank_lt_orank hlo, ?_⟩
    · rw [hmp, hhq, hadd]
      exact hsum
    · rw [hmp]
      exact orank_lt_orank hblk
  · rintro ⟨lo, hi, hsum, hlo, hblk⟩
    obtain ⟨u1, hu1⟩ := exists_orank_eq (A := A) (m := Lax895169.BitPredicate.orank (v m) * Lax895169.BitPredicate.orank (v p))
      (lt_trans hblk (orank_lt_card (v q)))
    obtain ⟨u2, hu2⟩ := exists_orank_eq (A := A) (m := Lax895169.BitPredicate.orank hi * Lax895169.BitPredicate.orank (v q))
      (lt_of_le_of_lt (by omega) (orank_lt_card (v x)))
    obtain ⟨u3, hu3⟩ := exists_orank_eq (A := A)
      (m := Lax895169.BitPredicate.orank (v m) * Lax895169.BitPredicate.orank (v p) + Lax895169.BitPredicate.orank hi * Lax895169.BitPredicate.orank (v q))
      (lt_of_le_of_lt (by omega) (orank_lt_card (v x)))
    refine ⟨![lo, hi, u1, u2, u3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Lax895169.BitPredicate.orank lo + Lax895169.BitPredicate.orank u3 = Lax895169.BitPredicate.orank (v x)
      rw [hu3]
      exact hsum
    · change Lax895169.BitPredicate.orank (v m) * Lax895169.BitPredicate.orank (v p) = Lax895169.BitPredicate.orank u1
      rw [hu1]
    · change Lax895169.BitPredicate.orank hi * Lax895169.BitPredicate.orank (v q) = Lax895169.BitPredicate.orank u2
      rw [hu2]
    · change Lax895169.BitPredicate.orank u1 + Lax895169.BitPredicate.orank u2 = Lax895169.BitPredicate.orank u3
      rw [hu1, hu2, hu3]
    · change lo < v p
      exact lt_of_orank_lt hlo
    · change u1 < v q
      exact lt_of_orank_lt (by rw [hu1]; exact hblk)

end Definability

end Lax895169Proofs.DescriptiveComplexity


