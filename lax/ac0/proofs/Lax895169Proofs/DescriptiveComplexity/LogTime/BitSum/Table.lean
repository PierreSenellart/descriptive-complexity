/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.BitSum.Ones
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
export Lax895169.BitPredicate (BitIx orank posCount)
end Lax895169Proofs.DescriptiveComplexity

/-!
# Level 3: counting the ones of a short word, by a table indexed by its value

This is the base of the Bit Sum Lemma and the place where its circularity is
broken.
Levels 1 and 2 reduce “count the ones of a word” to “count the ones of a
*shorter* word”, and that cannot go on for ever: at the bottom something has to
count outright. Here it is, and the trick is that a **lookup is a bit read at an
index**, so a table indexed by the *value* of a short word costs nothing that a
product would cost:

> Guess a table `D` cut into sections of `2 ^ ℓ` bits, one per possible count.
> The bit of section `c` at offset `v` says “`v` has `c` ones”. Sections are the
> boundary set of `LogTime/BitSum/Blocks.lean`, so the walk over counts is a walk
> over boundaries, and the entry for `v` in section `c` is at the index
> `boundary + v` – an **addition**.

## Why this pins the table, and pins it locally

The table is not defined, it is *constrained*, by three conditions that mention
only neighboring sections (`DescriptiveComplexity.BitSum.TableOk`):

* section `0` is set exactly at `v = 0` – no ones means no word;
* no later section is set at `v = 0`;
* section `c + 1` is set at `v` exactly when section `c` is set at `v` with its
  lowest one cleared (`DescriptiveComplexity.BitSum.ClearLow`).

Every one of those is a recursion on the **value**, never on the count, so no
condition ever has to say “and now do this `c` times”. Soundness
(`DescriptiveComplexity.BitSum.table_sound`) is then an induction on the count,
and it needs nothing about the layout beyond the table fitting – the discipline
`LogTime/Pow.lean` established.

## Two things the conditions do *not* say

They do not say where the table stops: sections above `ℓ` are all zero and
satisfy the recursion, so the guess simply runs out of ones to describe. And the
step is **guarded** by `DescriptiveComplexity.IsLowIx`, for the reason the
counter's step is: above the top position an element has no bits, so a condition
demanded there would be unsatisfiable rather than merely idle.
-/

namespace Lax895169Proofs.DescriptiveComplexity

namespace BitSum

/-! ### The table -/

section Table

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The conditions on the table**: the bit of the section of count `c` at
offset `v` says “`v` has `c` ones”, pinned by a recursion on `v` alone. -/
def TableOk (g B D : A) : Prop :=
  (∀ v : A, v < g → (Lax895169.BitPredicate.BitIx v D ↔ Lax895169.BitPredicate.orank v = 0)) ∧
    (∀ b b' : A, Lax895169.BitPredicate.BitIx b B → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank b' → ¬ Lax895169.BitPredicate.BitIx b' D) ∧
      ∀ b b' v v' i i' : A, Lax895169.BitPredicate.BitIx b B → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank b' → v < g →
        ClearLow v v' → Lax895169.BitPredicate.orank b' + Lax895169.BitPredicate.orank v = Lax895169.BitPredicate.orank i → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank v' = Lax895169.BitPredicate.orank i' →
          IsLowIx i → (Lax895169.BitPredicate.BitIx i D ↔ Lax895169.BitPredicate.BitIx i' D)

/-- **The table says what it is meant to say**: the entry of the section of
count `j` at offset `v` holds exactly when `v` has `j` ones. The induction is on
the count; each step is one application of the recursion on the value. -/
theorem table_sound {g B D l : A} (hgpos : 0 < Lax895169.BitPredicate.orank g)
    (hB : IsBlockSet g B) (hT : TableOk g B D) (hbits : Lax895169.BitPredicate.orank g = 2 ^ Lax895169.BitPredicate.orank l) :
    ∀ j : ℕ, ∀ b v i : A, Lax895169.BitPredicate.orank b = Lax895169.BitPredicate.orank g * j → v < g → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank v = Lax895169.BitPredicate.orank i →
      IsLowIx i → (Lax895169.BitPredicate.BitIx i D ↔ onesBelow (Lax895169.BitPredicate.orank v) (Lax895169.BitPredicate.orank l) = j) := by
  obtain ⟨hzero, hstep0, hstep⟩ := hT
  have hvbits : ∀ v : A, v < g → ∀ i, Lax895169.BitPredicate.orank l ≤ i → (Lax895169.BitPredicate.orank v).testBit i = false := by
    intro v hv i hi
    refine Nat.testBit_lt_two_pow (lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hi))
    rw [← hbits]
    exact orank_lt_orank hv
  intro j
  induction j with
  | zero =>
    intro b v i hb hv hsum _
    have hiv : i = v := orank_inj (by omega)
    rw [hiv, hzero v hv, onesBelow_eq_zero_iff (hvbits v hv)]
  | succ j ih =>
    intro b v i hb hv hsum hlow
    -- the section below
    have hgj : Lax895169.BitPredicate.orank g * j < Nat.card A := by
      have hmono : Lax895169.BitPredicate.orank g * j ≤ Lax895169.BitPredicate.orank g * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      have := orank_lt_card b
      omega
    obtain ⟨b₀, hb₀⟩ := exists_orank_eq (A := A) hgj
    have hb₀sum : Lax895169.BitPredicate.orank b₀ + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank b := by
      rw [hb₀, hb, Nat.mul_succ]
    have hb₀low : IsLowIx b₀ := by
      rw [IsLowIx] at hlow ⊢
      omega
    have hb₀bit : Lax895169.BitPredicate.BitIx b₀ B :=
      (bitIx_iff_of_isBlockSet hgpos hB b₀).mpr ⟨⟨j, hb₀⟩, hb₀low⟩
    rcases Nat.eq_zero_or_pos (Lax895169.BitPredicate.orank v) with hv0 | hvpos
    · -- at the value `0`, no section but the first is set
      have hib : i = b := orank_inj (by omega)
      rw [hib]
      constructor
      · intro hc
        exact absurd hc (hstep0 b₀ b hb₀bit hb₀sum)
      · intro hc
        exfalso
        have : Lax895169.BitPredicate.orank v = 0 → onesBelow (Lax895169.BitPredicate.orank v) (Lax895169.BitPredicate.orank l) = 0 := fun h => by
          rw [h]
          simp [onesBelow]
        omega
    · -- otherwise the recursion on the value applies
      have : Nonempty A := ⟨b⟩
      obtain ⟨v', hv'⟩ := exists_clearLow (A := A) (x := v) (by omega)
      have hone := onesBelow_of_clearLow hv' (hvbits v hv)
      have hvv' : Lax895169.BitPredicate.orank v' < Lax895169.BitPredicate.orank v := orank_lt_of_clearLow hv'
      have hv'lt : v' < g := lt_trans (lt_of_orank_lt hvv') hv
      have hi'lt : Lax895169.BitPredicate.orank b₀ + Lax895169.BitPredicate.orank v' < Nat.card A := by
        have := orank_lt_card i
        omega
      obtain ⟨i', hi'⟩ := exists_orank_eq (A := A) hi'lt
      rw [hstep b₀ b v v' i i' hb₀bit hb₀sum hv hv' (by omega) (by omega) hlow,
        ih b₀ v' i' hb₀ hv'lt (by omega) (by rw [IsLowIx] at hlow ⊢; omega)]
      omega

/-- **The table exists**: its bit at the index `i` says that the value `i` names
has the count `i` names, which is a statement about `i` alone – so the guess is a
bit vector, and it fits by `DescriptiveComplexity.BitSum.table_lt`. -/
theorem exists_tableOk [Nonempty A] {g B l : A} (hgpos : 0 < Lax895169.BitPredicate.orank g)
    (hbits : Lax895169.BitPredicate.orank g = 2 ^ Lax895169.BitPredicate.orank l) (hB : IsBlockSet g B)
    (hfit : (Lax895169.BitPredicate.orank l + 1) * Lax895169.BitPredicate.orank g < Lax895169.BitPredicate.posCount A - 1) : ∃ D : A, TableOk g B D := by
  classical
  obtain ⟨D, hD, hD'⟩ := exists_orank_testBit' (A := A)
    fun i => decide (onesBelow (i % Lax895169.BitPredicate.orank g) (Lax895169.BitPredicate.orank l) = i / Lax895169.BitPredicate.orank g)
  -- the bits are what they say, above the top position as well as below
  have hbit : ∀ i : ℕ, (Lax895169.BitPredicate.orank D).testBit i
      = decide (onesBelow (i % Lax895169.BitPredicate.orank g) (Lax895169.BitPredicate.orank l) = i / Lax895169.BitPredicate.orank g) := by
    intro i
    by_cases hi : i + 1 < Lax895169.BitPredicate.posCount A
    · exact hD i hi
    · rw [hD' i (by omega)]
      refine (decide_eq_false ?_).symm
      have hdiv : Lax895169.BitPredicate.orank l + 1 ≤ i / Lax895169.BitPredicate.orank g := by
        refine (Nat.le_div_iff_mul_le hgpos).mpr ?_
        omega
      have := onesBelow_le (i % Lax895169.BitPredicate.orank g) (Lax895169.BitPredicate.orank l)
      omega
  -- reading the two coordinates of an index
  have hcoord : ∀ (j : ℕ) (v : A), Lax895169.BitPredicate.orank v < Lax895169.BitPredicate.orank g →
      (Lax895169.BitPredicate.orank g * j + Lax895169.BitPredicate.orank v) % Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank v ∧
        (Lax895169.BitPredicate.orank g * j + Lax895169.BitPredicate.orank v) / Lax895169.BitPredicate.orank g = j := fun j v hv =>
    ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv],
      by rw [Nat.mul_add_div hgpos, Nat.div_eq_of_lt hv, Nat.add_zero]⟩
  have hvbits : ∀ v : A, v < g → ∀ i, Lax895169.BitPredicate.orank l ≤ i → (Lax895169.BitPredicate.orank v).testBit i = false := by
    intro v hv i hi
    refine Nat.testBit_lt_two_pow (lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hi))
    rw [← hbits]
    exact orank_lt_orank hv
  refine ⟨D, fun v hv => ?_, fun b b' hb hsum => ?_,
    fun b b' v v' i i' hb hsum hv hcl hi hi' _ => ?_⟩
  · -- section `0` is set exactly at the value `0`
    obtain ⟨h1, h2⟩ := hcoord 0 v (orank_lt_orank hv)
    rw [Nat.mul_zero, Nat.zero_add] at h1 h2
    rw [bitIx_iff, hbit, h1, h2, decide_eq_true_eq, onesBelow_eq_zero_iff (hvbits v hv)]
  · -- no later section is set at the value `0`
    obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hgpos hB b).mp hb
    have hb' : Lax895169.BitPredicate.orank b' = Lax895169.BitPredicate.orank g * (j + 1) := by rw [Nat.mul_succ]; omega
    rw [bitIx_iff, hb', hbit, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hgpos,
      decide_eq_true_eq]
    simp [onesBelow]
  · -- the step, which is one clearing of a one
    obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hgpos hB b).mp hb
    have hvg : Lax895169.BitPredicate.orank v < Lax895169.BitPredicate.orank g := orank_lt_orank hv
    have hv'v : Lax895169.BitPredicate.orank v' < Lax895169.BitPredicate.orank v := orank_lt_of_clearLow hcl
    have hone := onesBelow_of_clearLow hcl (hvbits v hv)
    obtain ⟨h1, h2⟩ := hcoord (j + 1) v hvg
    obtain ⟨h3, h4⟩ := hcoord j v' (by omega)
    have hiv : Lax895169.BitPredicate.orank i = Lax895169.BitPredicate.orank g * (j + 1) + Lax895169.BitPredicate.orank v := by rw [Nat.mul_succ]; omega
    have hi'v : Lax895169.BitPredicate.orank i' = Lax895169.BitPredicate.orank g * j + Lax895169.BitPredicate.orank v' := by omega
    rw [bitIx_iff, bitIx_iff, hiv, hi'v, hbit, hbit, h1, h2, h3, h4,
      decide_eq_true_eq, decide_eq_true_eq]
    omega

/-! ### Counting the ones of a short word -/

/-- **`y` is the number of ones of the `l`-bit word `x`**: the level-3
certificate in one existential – the section width, the boundaries, the counter,
the table, and the section whose counter is `y`, whose entry at `x` is set. -/
def PopShort (l x y : A) : Prop :=
  ∃ g B C D b b' i : A, IsPowIx l g ∧ IsBlockSet g B ∧ IsCounter g B C ∧ TableOk g B D ∧
    x < g ∧ Lax895169.BitPredicate.BitIx b B ∧ Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank b' ∧ IsLowIx b' ∧ WindowAt b b' C y ∧
    Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank x = Lax895169.BitPredicate.orank i ∧ IsLowIx i ∧ Lax895169.BitPredicate.BitIx i D

/-- **The certificate is sound**: whatever is guessed, the section it points at
is the one holding the count of `x`. -/
theorem popShort_sound {l x y : A} (hl : Lax895169.BitPredicate.orank l < Lax895169.BitPredicate.posCount A) (h : PopShort l x y) :
    Lax895169.BitPredicate.orank y = onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank l) := by
  obtain ⟨g, B, C, D, b, b', i, hg, hB, hC, hT, hxg, hbB, hsum, hlow', hwin,
    hisum, hilow, hiD⟩ := h
  have hgval : Lax895169.BitPredicate.orank g = 2 ^ Lax895169.BitPredicate.orank l := orank_of_isPowIx hl hg
  have hgpos : 0 < Lax895169.BitPredicate.orank g := by rw [hgval]; positivity
  have hcount : Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y = Lax895169.BitPredicate.orank b := counter_eq hgpos hB hC b b' y hbB hsum hlow' hwin
  have := (table_sound hgpos hB hT hgval (Lax895169.BitPredicate.orank y) b x i (by omega) hxg hisum hilow).mp hiD
  omega

/-- **The certificate exists**, once the table fits and the counter's fields are
wide enough: this is the completeness half of level 3, and every element it
guesses has already been built. -/
theorem popShort_of_eq [Nonempty A] {l x y : A}
    (hfit : (Lax895169.BitPredicate.orank l + 1) * 2 ^ Lax895169.BitPredicate.orank l < Lax895169.BitPredicate.posCount A - 1)
    (hcap : Lax895169.BitPredicate.posCount A ≤ 2 ^ Lax895169.BitPredicate.orank l * 2 ^ 2 ^ Lax895169.BitPredicate.orank l)
    (hxl : Lax895169.BitPredicate.orank x < 2 ^ Lax895169.BitPredicate.orank l) (hy : Lax895169.BitPredicate.orank y = onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank l)) :
    PopShort l x y := by
  have hone : 1 ≤ 2 ^ Lax895169.BitPredicate.orank l := Nat.one_le_two_pow
  have hlP : Lax895169.BitPredicate.orank l < Lax895169.BitPredicate.posCount A := by
    have hmul : Lax895169.BitPredicate.orank l + 1 ≤ (Lax895169.BitPredicate.orank l + 1) * 2 ^ Lax895169.BitPredicate.orank l :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hP : 1 < Lax895169.BitPredicate.posCount A := by omega
  obtain ⟨g, hg⟩ := exists_isPowIx hlP
  have hgval : Lax895169.BitPredicate.orank g = 2 ^ Lax895169.BitPredicate.orank l := orank_of_isPowIx hlP hg
  have hgpos : 0 < Lax895169.BitPredicate.orank g := by rw [hgval]; positivity
  obtain ⟨B, hB⟩ := exists_isBlockSet (A := A) (g := g) hP
  obtain ⟨C, hC⟩ := exists_isCounter hgpos hB (by rw [hgval]; exact hcap)
  obtain ⟨D, hT⟩ := exists_tableOk hgpos hgval hB (by rw [hgval]; exact hfit)
  -- the section that stands for the count of `x`
  have hjl : onesBelow (Lax895169.BitPredicate.orank x) (Lax895169.BitPredicate.orank l) ≤ Lax895169.BitPredicate.orank l := onesBelow_le _ _
  have hPcard : Lax895169.BitPredicate.posCount A < Nat.card A := posCount_lt_card
  have htop : Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1) < Lax895169.BitPredicate.posCount A - 1 := by
    have hmul : Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1) ≤ Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank l + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hcomm : Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank l + 1) = (Lax895169.BitPredicate.orank l + 1) * 2 ^ Lax895169.BitPredicate.orank l := by
      rw [hgval]; ring
    omega
  obtain ⟨b, hbr⟩ := exists_orank_eq (A := A) (m := Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y) (by
    have hmul : Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y ≤ Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega)
  obtain ⟨b', hb'r⟩ := exists_orank_eq (A := A) (m := Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1)) (by omega)
  have hsum : Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank b' := by rw [hbr, hb'r, Nat.mul_succ]
  have hlow' : IsLowIx b' := by rw [IsLowIx, hb'r]; omega
  have hlowb : IsLowIx b := by
    rw [IsLowIx, hbr]
    have hmul : Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y ≤ Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hbB : Lax895169.BitPredicate.BitIx b B := (bitIx_iff_of_isBlockSet hgpos hB b).mpr ⟨⟨Lax895169.BitPredicate.orank y, hbr⟩, hlowb⟩
  have hxg : x < g := lt_of_orank_lt (by rw [hgval]; exact hxl)
  -- the counter of that section is `y`
  obtain ⟨c, hc⟩ := exists_windowAt (b := b) (e := b') (x := C) (w := Lax895169.BitPredicate.orank g) (by omega)
  have hcy : c = y := by
    have := counter_eq hgpos hB hC b b' c hbB hsum hlow' hc
    refine orank_inj ?_
    have hcancel : Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank c = Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y := by omega
    exact Nat.eq_of_mul_eq_mul_left hgpos hcancel
  -- the entry of that section at `x`
  obtain ⟨i, hir⟩ := exists_orank_eq (A := A) (m := Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank x) (by
    have : Lax895169.BitPredicate.orank x < Lax895169.BitPredicate.orank g := by rw [hgval]; exact hxl
    omega)
  have hilow : IsLowIx i := by
    rw [IsLowIx, hir, hbr]
    have : Lax895169.BitPredicate.orank x < Lax895169.BitPredicate.orank g := by rw [hgval]; exact hxl
    have hmul : Lax895169.BitPredicate.orank g * Lax895169.BitPredicate.orank y + Lax895169.BitPredicate.orank g = Lax895169.BitPredicate.orank g * (Lax895169.BitPredicate.orank y + 1) := by ring
    omega
  refine ⟨g, B, C, D, b, b', i, hg, hB, hC, hT, hxg, hbB, hsum, hlow', hcy ▸ hc,
    by omega, hilow, ?_⟩
  exact (table_sound hgpos hB hT hgval (Lax895169.BitPredicate.orank y) b x i hbr hxg (by omega) hilow).mpr hy.symm

end Table

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **The table's conditions are first-order in the bit logic.** -/
theorem bitDef_tableOk (g B D : α) :
    BitDef (L := L) fun _ _ _ _ _ v => TableOk (v g) (v B) (v D) := by
  have h1 : BitDef (L := L) (α := α)
      (fun A _ _ _ _ v => ∀ w : A, w < v g → (Lax895169.BitPredicate.BitIx w (v D) ↔ Lax895169.BitPredicate.orank w = 0)) :=
    ((bitDef_lt (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl g)).imp
      ((bitDef_bit (Sum.inr 0) (Sum.inl D)).iff (bitDef_isZero (Sum.inr 0)))).all
  have h2 : BitDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ b b' : A,
      Lax895169.BitPredicate.BitIx b (v B) → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank (v g) = Lax895169.BitPredicate.orank b' → ¬ Lax895169.BitPredicate.BitIx b' (v D)) := by
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 2) (Sum.inr 0) (Sum.inl B)).imp
      ((bitDef_plus (Sum.inr 0) (Sum.inl g) (Sum.inr 1)).imp
        (bitDef_bit (Sum.inr 1) (Sum.inl D)).not)).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h b b' => h ![b, b'], fun h w => h (w 0) (w 1)⟩
  have h3 : BitDef (L := L) (α := α) (fun A _ _ _ _ v => ∀ b b' w w' i i' : A,
      Lax895169.BitPredicate.BitIx b (v B) → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank (v g) = Lax895169.BitPredicate.orank b' → w < v g → ClearLow w w' →
        Lax895169.BitPredicate.orank b' + Lax895169.BitPredicate.orank w = Lax895169.BitPredicate.orank i → Lax895169.BitPredicate.orank b + Lax895169.BitPredicate.orank w' = Lax895169.BitPredicate.orank i' → IsLowIx i →
          (Lax895169.BitPredicate.BitIx i (v D) ↔ Lax895169.BitPredicate.BitIx i' (v D))) := by
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 6) (Sum.inr 0) (Sum.inl B)).imp <|
      (bitDef_plus (Sum.inr 0) (Sum.inl g) (Sum.inr 1)).imp <|
        (bitDef_lt (Sum.inr 2) (Sum.inl g)).imp <|
          (bitDef_clearLow (Sum.inr 2) (Sum.inr 3)).imp <|
            (bitDef_plus (Sum.inr 1) (Sum.inr 2) (Sum.inr 4)).imp <|
              (bitDef_plus (Sum.inr 0) (Sum.inr 3) (Sum.inr 5)).imp <|
                (bitDef_isLowIx (Sum.inr 4)).imp <|
                  (bitDef_bit (Sum.inr 4) (Sum.inl D)).iff
                    (bitDef_bit (Sum.inr 5) (Sum.inl D))).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h b b' w w' i i' => h ![b, b', w, w', i, i'],
      fun h u => h (u 0) (u 1) (u 2) (u 3) (u 4) (u 5)⟩
  exact (h1.and (h2.and h3)).congr fun _ _ _ _ _ _ => Iff.rfl

/-- **Level 3 is a formula**: the whole certificate, guessed in one block. -/
theorem bitDef_popShort (l x y : α) :
    BitDef (L := L) fun _ _ _ _ _ v => PopShort (v l) (v x) (v y) := by
  have hbody : BitDef (L := L) (α := α ⊕ Fin 7) (fun A _ _ _ _ u =>
      IsPowIx (u (Sum.inl l)) (u (Sum.inr 0)) ∧ IsBlockSet (u (Sum.inr 0)) (u (Sum.inr 1)) ∧
        IsCounter (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inr 2)) ∧
          TableOk (u (Sum.inr 0)) (u (Sum.inr 1)) (u (Sum.inr 3)) ∧
            u (Sum.inl x) < u (Sum.inr 0) ∧ Lax895169.BitPredicate.BitIx (u (Sum.inr 4)) (u (Sum.inr 1)) ∧
              Lax895169.BitPredicate.orank (u (Sum.inr 4)) + Lax895169.BitPredicate.orank (u (Sum.inr 0)) = Lax895169.BitPredicate.orank (u (Sum.inr 5)) ∧
                IsLowIx (u (Sum.inr 5)) ∧
                  WindowAt (u (Sum.inr 4)) (u (Sum.inr 5)) (u (Sum.inr 2)) (u (Sum.inl y)) ∧
                    Lax895169.BitPredicate.orank (u (Sum.inr 4)) + Lax895169.BitPredicate.orank (u (Sum.inl x)) = Lax895169.BitPredicate.orank (u (Sum.inr 6)) ∧
                      IsLowIx (u (Sum.inr 6)) ∧ Lax895169.BitPredicate.BitIx (u (Sum.inr 6)) (u (Sum.inr 3))) :=
    (bitDef_isPowIx (Sum.inl l) (Sum.inr 0)).and <|
      (bitDef_isBlockSet (Sum.inr 0) (Sum.inr 1)).and <|
        (bitDef_isCounter (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).and <|
          (bitDef_tableOk (Sum.inr 0) (Sum.inr 1) (Sum.inr 3)).and <|
            (bitDef_lt (Sum.inl x) (Sum.inr 0)).and <|
              (bitDef_bit (Sum.inr 4) (Sum.inr 1)).and <|
                (bitDef_plus (Sum.inr 4) (Sum.inr 0) (Sum.inr 5)).and <|
                  (bitDef_isLowIx (Sum.inr 5)).and <|
                    (bitDef_windowAt (Sum.inr 4) (Sum.inr 5) (Sum.inr 2) (Sum.inl y)).and <|
                      (bitDef_plus (Sum.inr 4) (Sum.inl x) (Sum.inr 6)).and <|
                        (bitDef_isLowIx (Sum.inr 6)).and (bitDef_bit (Sum.inr 6) (Sum.inr 3))
  refine hbody.exs.congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, hw⟩,
    fun ⟨g, B, C, D, b, b', i, h⟩ => ⟨![g, B, C, D, b, b', i], h⟩⟩

end Definability

end BitSum

end Lax895169Proofs.DescriptiveComplexity


