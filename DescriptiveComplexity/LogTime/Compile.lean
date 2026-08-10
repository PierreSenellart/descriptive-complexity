/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime.BitLogic
import DescriptiveComplexity.LogTime.Simulate

/-!
# The lower fence: a bit-level prenex logic, compiled into machines

`DescriptiveComplexity.LTDecidable.bitDefinable` puts the machine model inside
the bit-level logic. This file puts that logic back inside the machine model, so
that the fence is an **equality** and the picture is

prenex `FO(≤, +, BIT)`  =  alternating logarithmic time.

`DescriptiveComplexity.ltDecidable_iff_bitDefinable` is that equality: the
machine model of this development is exactly characterized by a logic, with no
normal form left to apply and no gap left to name on either side of it.

## The logic

`DescriptiveComplexity.BitSentence`: a quantifier prefix – a polarity per
variable, exactly the shape a machine's registers have – over a quantifier-free
kernel built from four atoms (`DescriptiveComplexity.BitAtom`): the order, the
addition of ranks, an input relation at a tuple of variables, and the bit
`BitIx i x` of `x` at the index `i`.

That last atom is where the model gets its power, and it is a *read* rather than
a computation: the machine has the index in a register and addresses the bit
there (`DescriptiveComplexity.BaseTest.bit`). No sweep can do it – locating the
position `orank i` means counting positions, and an automaton carrying a constant
number of bits cannot – which is exactly why it is a primitive and not a
construction.

## The addition is a derived predicate

`DescriptiveComplexity.bitDef_plus_free`: the atom
`DescriptiveComplexity.BitAtom.plus` is redundant. `orank x + orank y = orank z`
is bit-definable from the order and the bit atom alone, by carry-lookahead
(`DescriptiveComplexity.plus_iff_bits`), so the logic of this file is
`FO(≤, BIT)` under another name – its classical name, since `≤` is classically
definable from `BIT` too. The atom stays all the same:
`DescriptiveComplexity.plusSweep_accepts` is half of what shows the machine has
to *build* its arithmetic rather than read it, and deleting the atom would delete
that demonstration for no theorem.

The lookahead is also where the index naming shows: the carry into position `i`
is “some `j < i` generates one, and every `k` strictly between propagates it”,
with `j` and `k` ordinary elements compared by `≤`. Under the place-value naming
each of those quantifiers had to be relativized to the powers of two.

## The compilation

Atom by atom, with the sweeps already built: `≤` is `leSweep`, `+` is
`plusSweep`, the bit atom is the machine's read, and an input relation is a
query. `DescriptiveComplexity.Sweep.relabel` is what lets a sweep written once
for two or three registers be run on any registers of the machine. The Boolean
structure of the kernel becomes the Boolean structure of the base test, and the
quantifier prefix becomes the register list unchanged – there is nothing to
prenexify, because the source syntax is prenex by construction.

## What is closed, and what is not

The equality with the logic is closed on both sides. The identification of that
logic with `FO(≤, +, ×)`, that is, with `DescriptiveComplexity.AC0Definable`, is
[Immerman 1999][immerman1999descriptive] Thm 1.17, one named theorem per
direction:

* `FO(≤, +, BIT) ⊆ FO(≤, +, ×)` is `DescriptiveComplexity.powArithDef`, the
  definability of `i ↦ 2 ^ i`, which is **proved**
  (`DescriptiveComplexity.LogTime.Pow`), so
  `DescriptiveComplexity.BitDefinable.ac0Definable` is unconditional;
* `FO(≤, +, ×) ⊆ FO(≤, +, BIT)` is the Bit Sum Lemma, the counting argument that
  eliminates `×` in favour of the bit atom, and it is **not** built.

Neither is a defect of the machine: they are statements about two vocabularies,
and the machine is exactly the one of them that a machine can be.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitAtom

variable {L : Language.{0, 0}} {m : ℕ}

/-- The base test an atom compiles to. -/
def compile : BitAtom L (Fin m) → BaseTest L m
  | .le x y => .sweep (leSweep.relabel ![x, y])
  | .plus x y z => .sweep (plusSweep.relabel ![x, y, z])
  | .bit i x => .bit i x
  | .rel R arg => .query R arg

/-- **The compilation of an atom is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (a : BitAtom L (Fin m)) (v : Fin m → A) : a.compile.Holds v ↔ a.Holds v := by
  cases a with
  | le x y =>
    have h : (leSweep.relabel ![x, y]).Accepts v ↔ leSweep.Accepts fun k => v (![x, y] k) :=
      Sweep.accepts_relabel _ _ _
    rw [show ((BitAtom.le x y : BitAtom L (Fin m)).compile.Holds v) =
      (leSweep.relabel ![x, y]).Accepts v from rfl, h, leSweep_accepts]
    exact Iff.rfl
  | plus x y z =>
    have h : (plusSweep.relabel ![x, y, z]).Accepts v ↔
        plusSweep.Accepts fun k => v (![x, y, z] k) := Sweep.accepts_relabel _ _ _
    rw [show ((BitAtom.plus x y z : BitAtom L (Fin m)).compile.Holds v) =
      (plusSweep.relabel ![x, y, z]).Accepts v from rfl, h, plusSweep_accepts]
    exact Iff.rfl
  | bit i x => exact Iff.rfl
  | rel R arg => exact Iff.rfl

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {m : ℕ}

/-- The base test a kernel compiles to: the Boolean structure is carried over
unchanged. -/
def compile : BitKernel L (Fin m) → BaseTest L m
  | .atom a => a.compile
  | .tt => .sweep (trueSweep.relabel Fin.elim0)
  | .not k => .not k.compile
  | .and k k' => .and k.compile k'.compile
  | .or k k' => .or k.compile k'.compile

/-- **The compilation of a kernel is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (k : BitKernel L (Fin m)) (v : Fin m → A) : k.compile.Holds v ↔ k.Holds v := by
  induction k with
  | atom a => exact a.holds_compile v
  | tt => exact ⟨fun _ => trivial, fun _ => (Sweep.accepts_relabel _ _ _).mpr rfl⟩
  | not k ih => exact not_congr ih
  | and k k' ih ih' => exact and_congr ih ih'
  | or k k' ih ih' => exact or_congr ih ih'

end BitKernel

/-! ### The logic decided by the machines -/

namespace BitSentence

variable {L : Language.{0, 0}}

/-- The machine a sentence compiles to: the prefix *is* the register list. -/
def compile (φ : BitSentence L) : LTMachine L where
  regs := φ.vars
  pol := φ.pol
  base := φ.kernel.compile

/-- **The compilation of a sentence is correct**: the machine accepts exactly
the instances the sentence holds of. -/
theorem accepts_compile (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : φ.compile.Accepts A ↔ φ.Holds A :=
  prefixHolds_congr φ.vars φ.pol fun v => φ.kernel.holds_compile v

end BitSentence

/-! ### The addition is a derived predicate

`FO(≤, +, BIT) = FO(≤, BIT)`: the addition of ranks is expressed by the
carry-lookahead formula, a condition on the bits with no addition in it. The
atom is kept all the same – `plusSweep_accepts` is half of what shows the model
has to *build* its arithmetic rather than read it – so what this section settles
is a name, not an API. -/

section Carry

variable {A : Type} [LinearOrder A] [Finite A]

/-- The order of the elements is the order of their ranks. -/
theorem lt_iff_orank_lt {i i' : A} : i < i' ↔ orank i < orank i' := by
  refine ⟨orank_lt_orank, fun h => lt_of_not_ge fun hc => ?_⟩
  exact absurd (orank_le_iff.mpr hc) (by omega)

/-- **The carry into a position**, first-order in the bits: a lower position
*generates* a carry, and every position between propagates it. -/
def CarryAt (x y i : A) : Prop :=
  ∃ j : A, j < i ∧ BitIx j x ∧ BitIx j y ∧
    ∀ k : A, j < k → k < i → (BitIx k x ∨ BitIx k y)

/-- The carry into a position is the arithmetic carry at its index. -/
theorem carryAt_iff (x y i : A) :
    CarryAt x y i ↔ 2 ^ orank i ≤ orank x % 2 ^ orank i + orank y % 2 ^ orank i := by
  rw [carry_iff_lookahead]
  constructor
  · rintro ⟨j, hji, hjx, hjy, hprop⟩
    refine ⟨orank j, orank_lt_orank hji, hjx, hjy, fun d hd hd' => ?_⟩
    obtain ⟨k, hk⟩ := exists_orank_eq (A := A) (lt_trans hd' (orank_lt_card i))
    have h1 : j < k := lt_iff_orank_lt.mpr (by omega)
    have h2 : k < i := lt_iff_orank_lt.mpr (by omega)
    rcases hprop k h1 h2 with h | h
    · exact Or.inl (by rw [bitIx_iff, hk] at h; exact h)
    · exact Or.inr (by rw [bitIx_iff, hk] at h; exact h)
  · rintro ⟨d, hd, hdx, hdy, hprop⟩
    obtain ⟨j, hj⟩ := exists_orank_eq (A := A) (lt_trans hd (orank_lt_card i))
    refine ⟨j, lt_iff_orank_lt.mpr (by omega), by rw [bitIx_iff, hj]; exact hdx,
      by rw [bitIx_iff, hj]; exact hdy, fun k h1 h2 => ?_⟩
    have h3 : orank j < orank k := orank_lt_orank h1
    have h4 : orank k < orank i := orank_lt_orank h2
    rcases hprop (orank k) (by omega) h4 with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **The addition of ranks is the carry-lookahead formula.** `orank x + orank y
= orank z` says that at every index the output bit is the exclusive or of the two
input bits and the carry – written as an iff-chain, which for three propositions
is the parity of their truth values. Nothing on the right-hand side is an
addition: this is the sense in which `FO(≤, +, BIT)` is `FO(≤, BIT)`.

There is no separate clause for the carry out of the last position: the equation
at the index *above* the top one says exactly that, all three bits being clear
there, and that index is a rank of the universe
(`DescriptiveComplexity.posCount_lt_card`). -/
theorem plus_iff_bits [Nonempty A] (x y z : A) :
    orank x + orank y = orank z ↔
      ∀ i : A, (BitIx i z ↔ ((BitIx i x ↔ BitIx i y) ↔ CarryAt x y i)) := by
  have hK : ∀ w : A, orank w % 2 ^ posCount A = orank w := orank_mod_two_pow_posCount
  have hcap : ∀ w : A, orank w < 2 ^ posCount A := fun w =>
    lt_of_lt_of_le (orank_lt_card w) (Nat.le_pow_clog (by norm_num) _)
  have hbits := add_mod_iff_bits (orank x) (orank y) (orank z) (posCount A)
  simp only [hK] at hbits
  have hpt : ∀ i : A, (BitIx i z ↔ ((BitIx i x ↔ BitIx i y) ↔ CarryAt x y i)) ↔
      ((orank z).testBit (orank i) = true ↔
        (((orank x).testBit (orank i) = true ↔ (orank y).testBit (orank i) = true) ↔
          2 ^ orank i ≤ orank x % 2 ^ orank i + orank y % 2 ^ orank i)) := by
    intro i
    rw [bitIx_iff, bitIx_iff, bitIx_iff, carryAt_iff]
  constructor
  · intro heq i
    rw [hpt i]
    rcases Nat.lt_or_ge (orank i) (posCount A) with hlt | hge
    · have hnc : ¬ 2 ^ posCount A ≤ orank x + orank y := by
        have := hcap z
        omega
      exact hbits.mp (by rw [if_neg hnc]; omega) (orank i) hlt
    · have hpow : 2 ^ posCount A ≤ 2 ^ orank i := Nat.pow_le_pow_right (by norm_num) hge
      have hx := testBit_orank_eq_false (x := x) hge
      have hy := testBit_orank_eq_false (x := y) hge
      have hz := testBit_orank_eq_false (x := z) hge
      have hmx : orank x % 2 ^ orank i = orank x :=
        Nat.mod_eq_of_lt (lt_of_lt_of_le (hcap x) hpow)
      have hmy : orank y % 2 ^ orank i = orank y :=
        Nat.mod_eq_of_lt (lt_of_lt_of_le (hcap y) hpow)
      have hnc : ¬ 2 ^ orank i ≤ orank x + orank y := by
        have := hcap z
        omega
      rw [hx, hy, hz, hmx, hmy]
      simp [hnc]
  · intro hall
    have hd : ∀ d, d < posCount A → ((orank z).testBit d = true ↔
        (((orank x).testBit d = true ↔ (orank y).testBit d = true) ↔
          2 ^ d ≤ orank x % 2 ^ d + orank y % 2 ^ d)) := by
      intro d hdlt
      obtain ⟨w, hw⟩ := exists_orank_eq (A := A) (lt_card_of_lt_posCount (A := A) hdlt)
      have := (hpt w).mp (hall w)
      rwa [hw] at this
    have hsum := hbits.mpr hd
    obtain ⟨w, hw⟩ := exists_orank_eq (A := A) (posCount_lt_card (A := A))
    have htop := (hpt w).mp (hall w)
    rw [hw, testBit_orank_eq_false (x := x) (le_refl _),
      testBit_orank_eq_false (x := y) (le_refl _),
      testBit_orank_eq_false (x := z) (le_refl _), hK x, hK y] at htop
    have hnc : ¬ 2 ^ posCount A ≤ orank x + orank y := by simpa using htop
    rw [if_neg hnc] at hsum
    omega

end Carry

section PlusFree

variable {L : Language.{0, 0}} {α : Type}

/-- The carry into a bound index, bit-definably: three variables, `j` guessed
and `k` universal, and nothing but the order to bound them. -/
theorem bitDef_carryAt (x y : α) :
    BitDef (L := L) (α := α ⊕ Fin 1) fun _ _ _ _ _ u =>
      CarryAt (u (Sum.inl x)) (u (Sum.inl y)) (u (Sum.inr 0)) := by
  have hr : BitDef (L := L) (α := ((α ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1)
      fun _ _ _ _ _ w =>
        w (Sum.inl (Sum.inr 0)) < w (Sum.inr 0) →
        w (Sum.inr 0) < w (Sum.inl (Sum.inl (Sum.inr 0))) →
        (BitIx (w (Sum.inr 0)) (w (Sum.inl (Sum.inl (Sum.inl x)))) ∨
          BitIx (w (Sum.inr 0)) (w (Sum.inl (Sum.inl (Sum.inl y))))) :=
    (bitDef_lt (Sum.inl (Sum.inr 0)) (Sum.inr 0)).imp
      ((bitDef_lt (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0)))).imp
        ((bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl x)))).or
          (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl y))))))
  refine ((bitDef_lt (Sum.inr 0) (Sum.inl (Sum.inr 0))).and
    ((bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl x))).and
      ((bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inl y))).and hr.all))).ex.congr
    fun A _ _ _ _ u => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, CarryAt]

/-- **The addition atom is redundant**: `orank x + orank y = orank z` is
bit-definable with no `plus` atom in the construction – only the order and the
bit at an index – which is the sense in which the logic of this file is
`FO(≤, BIT)`. The atom stays: `plusSweep_accepts` is half of what shows the
machine has to *build* its arithmetic rather than read it. -/
theorem bitDef_plus_free (x y z : α) :
    BitDef (L := L) fun _ _ _ _ _ v =>
      orank (v x) + orank (v y) = orank (v z) := by
  have hp : BitDef (L := L) (α := α ⊕ Fin 1) fun _ _ _ _ _ u =>
      (BitIx (u (Sum.inr 0)) (u (Sum.inl z)) ↔
        ((BitIx (u (Sum.inr 0)) (u (Sum.inl x)) ↔ BitIx (u (Sum.inr 0)) (u (Sum.inl y))) ↔
          CarryAt (u (Sum.inl x)) (u (Sum.inl y)) (u (Sum.inr 0)))) :=
    (bitDef_bit (Sum.inr 0) (Sum.inl z)).iff
      (((bitDef_bit (Sum.inr 0) (Sum.inl x)).iff
        (bitDef_bit (Sum.inr 0) (Sum.inl y))).iff (bitDef_carryAt x y))
  refine (hp.all).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact (plus_iff_bits (v x) (v y) (v z)).symm

end PlusFree

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The lower fence**: every prenex `FO(≤, +, BIT)` sentence is decided by a
machine with a logarithmic clock and a bit-level base. The order and the addition
are the sweeps of `DescriptiveComplexity.LogTime.Arith`, the bit is a read, and
the quantifiers are the registers. -/
theorem BitDefinable.ltDecidable {P : DecisionProblem L} (h : BitDefinable P) :
    LTDecidable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.compile, fun A _ _ _ _ => ?_⟩
  rw [hφ A]
  exact (φ.accepts_compile A).symm

/-- **The machine model is exactly a logic.** Alternating logarithmic time – a
machine whose registers are guessed addresses and whose base sees nothing but
bits – decides exactly the problems defined by a prenex sentence over `≤`, `+`
and the bit at an index, that is, by `FO(≤, BIT)`. The forward direction guesses
each sweep's trace, one element per bit vector over the positions
(`DescriptiveComplexity.LTDecidable.bitDefinable`); the backward one compiles
atom by atom into the sweeps of `DescriptiveComplexity.LogTime.Arith` and the
machine's read. -/
theorem ltDecidable_iff_bitDefinable {P : DecisionProblem L} :
    LTDecidable P ↔ BitDefinable P :=
  ⟨LTDecidable.bitDefinable, BitDefinable.ltDecidable⟩

end DescriptiveComplexity
