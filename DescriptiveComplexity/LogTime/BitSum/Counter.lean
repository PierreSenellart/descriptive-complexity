/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.BitSum.Blocks

/-!
# The counter field: telling a block which block it is

Co-location (`DescriptiveComplexity.LogTime.BitSum.Blocks`) says where a block's
field is, and that is enough to walk the blocks. It is not enough to *name* them:
a step of the walk that has to know “this is block `j`” cannot compute `j` from
the boundary `j · g`, that being a division. So the number is carried, in the
field the same boundaries delimit, by a second guessed element:

> `DescriptiveComplexity.BitSum.IsCounter g B C`: the window of `C` between two
> consecutive boundaries holds the index of the first – pinned by “the field at
> the least boundary is `0`” and “consecutive fields differ by one”, and by
> nothing else.

This is the second half of the device, and `LogTime/Pow.lean`'s `ValAt` is the
same idea with a doubling gap. It is what level 3 of `AC0.md` §2.3 needs: its
table's sections are indexed by a *count* of ones, and the section walk has to
know which count it is at.

## What the guard is for

The conditions are stated only where there is room: the step is required of a
pair of boundaries whose *second* window ends below the top position
(`DescriptiveComplexity.IsLowIx`). Without that guard the topmost field would
have to be written above the top position, where an element has no bits, and no
`C` would satisfy the conditions at all. With it,
`DescriptiveComplexity.BitSum.counter_eq` reads the counter wherever the layout
has room, which is everywhere a construction uses it, and
`DescriptiveComplexity.BitSum.exists_isCounter` builds one.

The capacity condition is the expected one: a field of `g` bits must hold every
index it names, so `posCount A ≤ orank g * 2 ^ orank g`. For the gaps of §2.3
that is true with room to spare.
-/

namespace DescriptiveComplexity

namespace BitSum

/-! ### The packed counters, in `ℕ` -/

/-- **The number whose `j`-th field holds `f j`**: fields of width `g`, one per
block, for the first `m` blocks. The counter is the case `f = id`, and the
running sum of `LogTime/BitSum/Sum.lean` is the general one. -/
def packVal (g : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => packVal g f m + f m * 2 ^ (m * g)

/-- **A packing fits below the block it stops at**, provided every value fits in
a field. -/
theorem packVal_lt {g : ℕ} {f : ℕ → ℕ} : ∀ {m : ℕ}, (∀ j, j < m → f j < 2 ^ g) →
    packVal g f m < 2 ^ (m * g) := by
  intro m
  induction m with
  | zero => intro _; simp [packVal]
  | succ m ih =>
    intro h
    have hih := ih fun j hj => h j (by omega)
    have hfm : f m + 1 ≤ 2 ^ g := h m (by omega)
    have hexp : (f m + 1) * 2 ^ (m * g) = f m * 2 ^ (m * g) + 2 ^ (m * g) := by ring
    have hle : (f m + 1) * 2 ^ (m * g) ≤ 2 ^ g * 2 ^ (m * g) :=
      Nat.mul_le_mul_right _ hfm
    have hpow : (2 : ℕ) ^ g * 2 ^ (m * g) = 2 ^ ((m + 1) * g) := by
      rw [← pow_add]
      congr 1
      ring
    have hval : packVal g f (m + 1) = packVal g f m + f m * 2 ^ (m * g) := rfl
    omega

/-- **What a field of a packing holds**: the `j`-th field is `f j`. -/
theorem packVal_window {g : ℕ} {f : ℕ → ℕ} : ∀ {m j : ℕ}, (∀ j, j < m → f j < 2 ^ g) →
    j < m → packVal g f m / 2 ^ (j * g) % 2 ^ g = f j := by
  intro m
  induction m with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro j hm hj
    rcases Nat.lt_or_ge j m with hlt | hge
    · -- the top field is a multiple of `2 ^ (j * g + g)`, so it is invisible here
      have hsplit : packVal g f (m + 1) =
          2 ^ (j * g) * (2 ^ g * (f m * 2 ^ (m * g - j * g - g))) + packVal g f m := by
        have hexp : (2 : ℕ) ^ (j * g) * (2 ^ g * (f m * 2 ^ (m * g - j * g - g)))
            = f m * (2 ^ (j * g) * 2 ^ g * 2 ^ (m * g - j * g - g)) := by ring
        have hsum : j * g + g + (m * g - j * g - g) = m * g := by
          have hmul : (j + 1) * g ≤ m * g := Nat.mul_le_mul_right _ (by omega)
          have hexp' : (j + 1) * g = j * g + g := by ring
          omega
        rw [packVal, hexp, ← pow_add, ← pow_add, hsum]
        ring
      rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_mod]
      exact ih (fun i hi => hm i (by omega)) hlt
    · -- the top field is the one being read
      have hjm : j = m := by omega
      subst hjm
      have hlow : packVal g f j < 2 ^ (j * g) := packVal_lt fun i hi => hm i (by omega)
      have hval : packVal g f (j + 1) = packVal g f j + f j * 2 ^ (j * g) := rfl
      rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (j * g)),
        Nat.div_eq_of_lt hlow, Nat.zero_add, Nat.mod_eq_of_lt (hm j (by omega))]

/-- **The packed counters**: the number whose `j`-th field holds `j`. -/
def counterVal (g m : ℕ) : ℕ := packVal g id m

/-- **The counters fit below the block they stop at**, provided each index fits
in a field – which is what `m ≤ 2 ^ g` says. -/
theorem counterVal_lt {g m : ℕ} (h : m ≤ 2 ^ g) : counterVal g m < 2 ^ (m * g) :=
  packVal_lt fun j hj => by simpa using by omega

/-- **What a counter field holds**: the `j`-th field of the packed counters is
`j`. -/
theorem counterVal_window {g m j : ℕ} (h : m ≤ 2 ^ g) (hj : j < m) :
    counterVal g m / 2 ^ (j * g) % 2 ^ g = j :=
  packVal_window (fun i hi => by simpa using by omega) hj

/-! ### The counter of a boundary set -/

section Counter

variable {A : Type} [LinearOrder A] [Finite A]

/-- **The counter element of a boundary set**: between consecutive boundaries,
`C` holds the number of the first – `0` at the least boundary, one more at each
step. The step is asked only where the second window has room
(`DescriptiveComplexity.IsLowIx`), since above the top position an element has
no bits to write in. -/
def IsCounter (g B C : A) : Prop :=
  (∀ z b' c : A, orank z = 0 → orank z + orank g = orank b' → WindowAt z b' C c →
      orank c = 0) ∧
    ∀ b b' b'' c c' : A, BitIx b B → orank b + orank g = orank b' →
      orank b' + orank g = orank b'' → IsLowIx b'' →
        WindowAt b b' C c → WindowAt b' b'' C c' → orank c + 1 = orank c'

/-- **What the counter says**: at a boundary, the field holds the number of the
boundary. The induction is on that number, and it is the whole soundness half of
the device. -/
theorem counter_eq {g B C : A} (hg : 0 < orank g) (hB : IsBlockSet g B)
    (hC : IsCounter g B C) :
    ∀ b b' c : A, BitIx b B → orank b + orank g = orank b' → IsLowIx b' →
      WindowAt b b' C c → orank g * (orank c) = orank b := by
  have key : ∀ j : ℕ, ∀ b b' c : A, orank b = orank g * j → BitIx b B →
      orank b + orank g = orank b' → IsLowIx b' → WindowAt b b' C c → orank c = j := by
    intro j
    induction j with
    | zero =>
      intro b b' c hb _ hsum _ hwin
      exact hC.1 b b' c (by omega) hsum hwin
    | succ j ih =>
      intro b b' c hb hbit hsum hlow hwin
      -- the boundary below `b`
      have hprev : orank g * j < Nat.card A := by
        have hmono : orank g * j ≤ orank g * (j + 1) := Nat.mul_le_mul_left _ (by omega)
        have := orank_lt_card b
        omega
      obtain ⟨b₀, hb₀⟩ := exists_orank_eq (A := A) hprev
      have hb₀sum : orank b₀ + orank g = orank b := by
        rw [hb₀, hb, Nat.mul_succ]
      have hb₀low : IsLowIx b := by
        rw [IsLowIx] at hlow ⊢
        omega
      have hb₀bit : BitIx b₀ B :=
        (bitIx_iff_of_isBlockSet hg hB b₀).mpr ⟨⟨j, hb₀⟩, by
          rw [IsLowIx] at hb₀low ⊢
          omega⟩
      obtain ⟨c₀, hc₀⟩ := exists_windowAt (b := b₀) (e := b) (x := C) (w := orank g)
        (by omega)
      have hstep := hC.2 b₀ b b' c₀ c hb₀bit hb₀sum hsum hlow hc₀ hwin
      have := ih b₀ b c₀ hb₀ hb₀bit hb₀sum hb₀low hc₀
      omega
  intro b b' c hbit hsum hlow hwin
  obtain ⟨j, hj⟩ := ((bitIx_iff_of_isBlockSet hg hB b).mp hbit).1
  rw [key j b b' c hj hbit hsum hlow hwin]
  exact hj.symm

/-- **A counter exists**, once a field is wide enough to hold every index it
names: the packed counters of `DescriptiveComplexity.BitSum.counterVal`, cut off
where the tape runs out. -/
theorem exists_isCounter [Nonempty A] {g B : A} (hg : 0 < orank g)
    (hB : IsBlockSet g B) (hcap : posCount A ≤ orank g * 2 ^ orank g) :
    ∃ C : A, IsCounter g B C := by
  set m := (posCount A - 1) / orank g with hm
  have hPpos : 0 < posCount A := by
    rw [← two_pow_lt_card_iff_lt_posCount]
    have := orank_lt_card g
    simpa using by omega
  have hmg : m * orank g ≤ posCount A - 1 := by
    rw [hm]
    exact Nat.div_mul_le_self _ _
  have hmle : m ≤ 2 ^ orank g := by
    have h1 : posCount A - 1 ≤ orank g * 2 ^ orank g := by omega
    calc m = (posCount A - 1) / orank g := hm
      _ ≤ orank g * 2 ^ orank g / orank g := Nat.div_le_div_right h1
      _ = 2 ^ orank g := Nat.mul_div_cancel_left _ hg
  have hcard : 2 ^ (posCount A - 1) < Nat.card A :=
    (two_pow_lt_card_iff_lt_posCount _).mpr (by omega)
  have hlt : counterVal (orank g) m < Nat.card A :=
    lt_of_lt_of_le (counterVal_lt hmle)
      (le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hmg) hcard))
  obtain ⟨C, hCval⟩ := exists_orank_eq (A := A) hlt
  -- every window of `C` at a block below `m` reads that block's number
  have hread : ∀ b b' c : A, ∀ j : ℕ, orank b = orank g * j → j < m →
      orank b + orank g = orank b' → WindowAt b b' C c → orank c = j := by
    intro b b' c j hb hj hsum hwin
    rw [(windowAt_iff (w := orank g) (by omega)).mp hwin, hCval, hb, Nat.mul_comm]
    exact counterVal_window hmle hj
  refine ⟨C, fun z b' c hz hsum hwin => ?_, fun b b' b'' c c' hbit hs1 hs2 hlow hw1 hw2 => ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [(windowAt_iff (w := orank g) (by omega)).mp hwin, hCval, hm0]
      simp [counterVal, packVal]
    · exact hread z b' c 0 (by omega) hmpos hsum hwin
  · obtain ⟨⟨j, hj⟩, -⟩ := (bitIx_iff_of_isBlockSet hg hB b).mp hbit
    have hb'' : orank b'' = orank g * (j + 2) := by
      have : orank g * (j + 2) = orank g * j + orank g + orank g := by ring
      omega
    have hjm : j + 2 ≤ m := by
      rw [IsLowIx] at hlow
      rw [hm]
      refine Nat.le_div_iff_mul_le hg |>.mpr ?_
      have hcomm : (j + 2) * orank g = orank g * (j + 2) := Nat.mul_comm _ _
      omega
    rw [hread b b' c j hj (by omega) hs1 hw1,
      hread b' b'' c' (j + 1) (by rw [Nat.mul_succ]; omega) (by omega) hs2 hw2]

end Counter

/-! ### Definability -/

section Definability

open FirstOrder

open Language

variable {L : Language.{0, 0}} {α : Type}

/-- **The counter is first-order in the bit logic**: two conditions, each a
block of quantified indices over windows. -/
theorem bitDef_isCounter (g B C : α) :
    BitDef (L := L) fun _ _ _ _ _ v => IsCounter (v g) (v B) (v C) := by
  have hbase : BitDef (L := L) (α := α) (fun _ _ _ _ _ v => ∀ z b' c : _,
      orank z = 0 → orank z + orank (v g) = orank b' → WindowAt z b' (v C) c →
        orank c = 0) := by
    refine (((bitDef_isZero (L := L) (α := α ⊕ Fin 3) (Sum.inr 0)).imp
      ((bitDef_plus (Sum.inr 0) (Sum.inl g) (Sum.inr 1)).imp
        ((bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl C) (Sum.inr 2)).imp
          (bitDef_isZero (Sum.inr 2))))).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h z b' c => h ![z, b', c], fun h w => h (w 0) (w 1) (w 2)⟩
  have hstep : BitDef (L := L) (α := α) (fun _ _ _ _ _ v => ∀ b b' b'' c c' : _,
      BitIx b (v B) → orank b + orank (v g) = orank b' →
        orank b' + orank (v g) = orank b'' → IsLowIx b'' →
          WindowAt b b' (v C) c → WindowAt b' b'' (v C) c' → orank c + 1 = orank c') := by
    have hsucc : BitDef (L := L) (α := α ⊕ Fin 5)
        (fun _ _ _ _ _ u => orank (u (Sum.inr 3)) + 1 = orank (u (Sum.inr 4))) := by
      refine (((bitDef_isOne (L := L) (α := (α ⊕ Fin 5) ⊕ Fin 1) (Sum.inr 0)).and
        (bitDef_plus (Sum.inl (Sum.inr 3)) (Sum.inr 0)
          (Sum.inl (Sum.inr 4)))).ex).congr fun A _ _ _ _ u => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      constructor
      · rintro ⟨o, ho, hsum⟩
        omega
      · intro h
        have hone : (1 : ℕ) < Nat.card A :=
          lt_of_le_of_lt (by omega) (orank_lt_card (u (Sum.inr 4)))
        obtain ⟨o, ho⟩ := exists_orank_eq (A := A) hone
        exact ⟨o, ho, by omega⟩
    refine (((bitDef_bit (L := L) (α := α ⊕ Fin 5) (Sum.inr 0) (Sum.inl B)).imp
      ((bitDef_plus (Sum.inr 0) (Sum.inl g) (Sum.inr 1)).imp
        ((bitDef_plus (Sum.inr 1) (Sum.inl g) (Sum.inr 2)).imp
          ((bitDef_isLowIx (Sum.inr 2)).imp
            ((bitDef_windowAt (Sum.inr 0) (Sum.inr 1) (Sum.inl C) (Sum.inr 3)).imp
              ((bitDef_windowAt (Sum.inr 1) (Sum.inr 2) (Sum.inl C)
                (Sum.inr 4)).imp hsucc)))))).alls).congr fun A _ _ _ _ v => ?_
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h b b' b'' c c' => h ![b, b', b'', c, c'],
      fun h w => h (w 0) (w 1) (w 2) (w 3) (w 4)⟩
  exact (hbase.and hstep).congr fun _ _ _ _ _ _ => Iff.rfl

end Definability

end BitSum

end DescriptiveComplexity
