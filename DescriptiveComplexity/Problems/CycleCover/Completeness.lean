/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CycleCover.Drawing
import DescriptiveComplexity.Problems.OneInSat.CountingFromSat
import DescriptiveComplexity.Counting.Reduction

/-!
# #Cycle Cover is one-call `#P`-complete

**Valiant's theorem** ([Valiant 1979][valiant1979complexity]): the permanent
of a 0-1 matrix, i.e., the number of cycle covers of a digraph or of perfect
matchings of a bipartite graph, is `#P`-complete. The reduction here is from
#1-in-SAT, and it is a **one-call** reduction: the number of exactly-one
models is read off the one permanent asked for, by a remainder and a
quotient (`DescriptiveComplexity.sharpOneInSat_oneCall_sharpCycleCover`).

The route, file by file:

* `DescriptiveComplexity.Problems.CycleCover.Base`: the base graph of the
  formula, and the evaluation of each term of the XOR sum;
* `DescriptiveComplexity.Problems.CycleCover.Models`: the consistent choices
  are the exactly-one models, so that the base graph with Valiant's gadgets
  attached has permanent `4 ^ t * N`, `t` the number of occurrences and `N`
  the number of models;
* `DescriptiveComplexity.Permanent.Widths`: the 0-1 ladder expansion of that
  integer matrix has permanent congruent to it modulo `2 ^ L + 1`, `L` the
  number of levels, with `4 ^ t * N ≤ 2 ^ L`;
* `DescriptiveComplexity.Problems.CycleCover.Formulas` and
  `DescriptiveComplexity.Problems.CycleCover.Drawing`: the ladder expansion
  is first-order definable over the ordered expansion of the formula.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc Finset

namespace SatCover

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Fintype A]

/-- The permanent of the attached matrix is `4 ^ t` times the number of
exactly-one models. -/
theorem bperm_attachedM :
    bperm (attachedM (A := A)) = 4 ^ Nat.card (Occ A) * (SharpOneInSAT A : ℤ) := by
  rw [attachedM, Site.bperm_flatAttach, Nat.card_eq_fintype_card]
  exact bperm_attachAll_sites_eq

omit [LinearOrder A] [Fintype A] in
/-- The number of variables is at most the number of occurrences. -/
theorem card_satOccurs_le [Finite A] : Nat.card {x : A // SatOccurs A x} ≤ Nat.card (Occ A) :=
  Nat.card_le_card_of_injective (fun x => Occ.dummy x.1 x.2 true) fun _ _ h =>
    Subtype.ext (congrArg Occ.x h)

omit [LinearOrder A] [Fintype A] in
/-- The number of exactly-one models is at most `2 ^ t`. -/
theorem sharpOneInSat_le [Finite A] : SharpOneInSAT A ≤ 2 ^ Nat.card (Occ A) := by
  rw [sharpOneInSat_apply]
  refine le_trans (Nat.card_le_card_of_injective
    (fun ν : {ν : A → Prop // OneInModel A ν} => (⟨ν.1, ν.2.2⟩ :
      {ν : A → Prop // ∀ x, ν x → SatOccurs A x})) fun ν ν' h => Subtype.ext (by
        have := congrArg Subtype.val h
        exact this)) ?_
  rw [card_subsets_eq_two_pow]
  exact Nat.pow_le_pow_right (by norm_num) card_satOccurs_le

variable [Nonempty A]

/-- **The number of cycle covers of the drawing** is the permanent of the
ladder expansion of the attached matrix. -/
theorem sharpCycleCover_drawInterp :
    SharpCycleCover (drawInterp.MapRel A) =
      bperm (ladder 3 (widths (Λ := Level A) (attachedM (A := A)))) := by
  classical
  have : Finite (drawInterp.MapRel A) := drawInterp.mapRel_finite A
  let : Fintype (drawInterp.MapRel A) := Fintype.ofFinite _
  have h1 := sharpCycleCover_eq_bperm (drawInterp.MapRel A)
  have h2 := bperm_reindex drawEquiv drawEquiv
    (fun x y : drawInterp.MapRel A => if DGArc x y then (1 : ℕ) else 0)
  have h3 : (fun y y' : (V A ⊕ RungA A) ⊕ Unit =>
      (fun x y : drawInterp.MapRel A => if DGArc x y then (1 : ℕ) else 0)
        (drawEquiv.symm y) (drawEquiv.symm y')) =
      fun y y' => if DrawEdge y y' then 1 else 0 :=
    funext fun y => funext fun y' => if_congr (drawArc_iff y y') rfl rfl
  have h4 := bperm_extend_loop (ladder 3 (widths (Λ := Level A) (attachedM (A := A))))
    (fun y y' : (V A ⊕ RungA A) ⊕ Unit => if DrawEdge y y' then 1 else 0)
    (fun a b => rfl) (by simp [DrawEdge]) (fun b => by simp [DrawEdge])
  rw [h1, ← h2, h3]
  convert h4 using 2

end SatCover

/-- **#1-in-SAT reduces to #Cycle Cover with one call**: the number of
exactly-one models is the permanent of the drawn digraph, modulo `2 ^ L + 1`
for `L` the number of levels, divided by `4 ^ t` for `t` the number of
occurrences. -/
noncomputable def sharpOneInSat_oneCall_sharpCycleCover : SharpOneInSAT ≤ᶜ[≤] SharpCycleCover where
  Tag := SatCover.FullTag
  dim := 6
  toRelInterpretation := SatCover.drawInterp
  dom_nonempty := fun A _ _ _ _ => by
    let := Fintype.ofFinite A
    exact ⟨Sum.inr (), fun _ => SatCover.least, SatCover.realize_drawDomF_extra.mpr
      ⟨fun y => Finset.min'_le _ _ (Finset.mem_univ y), rfl, rfl, rfl, rfl, rfl⟩⟩
  post := .div (.mod .oracle (.add (.pow2 (.card SatCover.levelsInterp)) (.poly (.num 1))))
    (.pow2 (.mul (.num 2) (.card SatCover.occInterp)))
  correct := fun A _ _ _ _ => by
    let := Fintype.ofFinite A
    change SharpOneInSAT A = (SharpCycleCover (SatCover.drawInterp.MapRel A) %
      (2 ^ Nat.card (SatCover.levelsInterp.MapRel A) + 1)) /
      2 ^ (2 * Nat.card (SatCover.occInterp.MapRel A))
    rw [SatCover.sharpCycleCover_drawInterp, SatCover.card_occInterp, pow_mul,
      show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.card_eq_fintype_card (α := SatCover.Level A)]
    refine (bperm_ladder_widths_div (Λ := SatCover.Level A) SatCover.attachedM
      SatCover.attachedM_bounds (Nat.card (SatCover.Occ A)) (SharpOneInSAT A)
      SatCover.bperm_attachedM ?_).symm
    rw [← Nat.card_eq_fintype_card]
    calc 4 ^ Nat.card (SatCover.Occ A) * SharpOneInSAT A
        ≤ 4 ^ Nat.card (SatCover.Occ A) * 2 ^ Nat.card (SatCover.Occ A) :=
          Nat.mul_le_mul_left _ SatCover.sharpOneInSat_le
      _ = 2 ^ (3 * Nat.card (SatCover.Occ A)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          ring_nf
      _ ≤ 2 ^ Nat.card (SatCover.Level A) :=
          Nat.pow_le_pow_right (by norm_num) SatCover.three_mul_card_occ_le

/-- **#Cycle Cover is one-call `#P`-hard.** -/
theorem sharpCycleCover_sharpP_oneCallHard : SharpP.OneCallHard SharpCycleCover :=
  CountingClass.OneCallHard.of_oneCall sharpOneInSat_oneCall_sharpCycleCover
    (oneCallHard_sharpP_of_parsimoniousHard sharpOneInSat_sharpP_parsimoniousHard)

/-- **Valiant's theorem: #Cycle Cover, the permanent of a 0-1 matrix, is
one-call `#P`-complete** ([Valiant 1979][valiant1979complexity]). -/
theorem sharpCycleCover_sharpP_oneCallComplete : SharpP.OneCallComplete SharpCycleCover :=
  .of_mem sharpCycleCover_mem_sharpP sharpCycleCover_sharpP_oneCallHard

end DescriptiveComplexity
