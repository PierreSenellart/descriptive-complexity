/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.BinRel
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the binary numbers below a bound

A number written in binary on the positions of a linear order is a set of
positions (`DescriptiveComplexity.binNum`). This file counts those sets: over
`n` positions the decoding is a bijection onto the numbers below `2 ^ n`
(`DescriptiveComplexity.binCode_bijective`), so the sets of bits whose value is
below that of a given set `w` are exactly as many as the value of `w`
(`DescriptiveComplexity.card_binNum_lt`).

That is what lets a number in the instance act as a *weight* in a count: a
witness that carries, beside a solution, a number below the weight of that
solution is counted once per unit of weight, and “below” is first-order
(`DescriptiveComplexity.binNum_lt_iff`).
-/

namespace DescriptiveComplexity

variable {A : Type} [Finite A] {Le : A → A → Prop}

/-- The decoding of a set of bits, over all the elements as positions, as a
number below `2 ^ n`. -/
noncomputable def binCode (hlin : IsLinOrd Le) (b : A → Prop) : Fin (2 ^ Nat.card A) :=
  ⟨binNum Le (fun _ => True) b,
    binNum_lt_two_pow hlin (Nat.card A) (fun _ => True)
      (by
        rw [← Nat.card_coe_set_eq]
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial))
      b⟩

/-- **Binary decoding is a bijection** from the sets of positions onto the
numbers below `2 ^ n`. -/
theorem binCode_bijective (hlin : IsLinOrd Le) : Function.Bijective (binCode (A := A) hlin) := by
  classical
  let := Fintype.ofFinite (A → Prop)
  have hcard : ({p : A | True} : Set A).ncard = Nat.card A := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun b b' h => ?_, ?_⟩
  · exact funext fun p => propext
      (binNum_inj_on hlin (Nat.card A) (fun _ => True) hcard b b' (congrArg Fin.val h) p trivial)
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card,
      Fintype.card_prop]

/-- **The sets of bits below a weight are as many as the weight.** -/
theorem card_binNum_lt (hlin : IsLinOrd Le) (w : A → Prop) :
    Nat.card {b : A → Prop // binNum Le (fun _ => True) b < binNum Le (fun _ => True) w} =
      binNum Le (fun _ => True) w := by
  have hw := (binCode hlin w).2
  have e1 : {b : A → Prop // binNum Le (fun _ => True) b < binNum Le (fun _ => True) w} ≃
      {k : Fin (2 ^ Nat.card A) // k.1 < binNum Le (fun _ => True) w} :=
    Equiv.subtypeEquiv (Equiv.ofBijective _ (binCode_bijective hlin)) fun _ => Iff.rfl
  have e2 : {k : Fin (2 ^ Nat.card A) // k.1 < binNum Le (fun _ => True) w} ≃
      Fin (binNum Le (fun _ => True) w) :=
    { toFun := fun k => ⟨k.1.1, k.2⟩
      invFun := fun i => ⟨⟨i.1, lt_trans i.2 hw⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card, Fintype.card_fin]

end DescriptiveComplexity
