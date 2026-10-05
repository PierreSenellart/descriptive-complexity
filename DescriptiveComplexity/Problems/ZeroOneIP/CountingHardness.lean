/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ZeroOneIP.Counting
import DescriptiveComplexity.Problems.ZeroOneIP.Hardness
import DescriptiveComplexity.Problems.Knapsack.CountingHardness

/-!
# #0-1 integer programming is parsimoniously `#P`-complete

The reduction of Knapsack to 0-1 integer programming
(`DescriptiveComplexity.Problems.ZeroOneIP.Hardness`) reads a subset-sum instance as a
program with one equation: the items become the columns, and the interpreted
universe is a copy of the input. A set of items is a `0-1` vector, and it sums
to the target exactly when the equation holds, so the solutions correspond
bijectively (`DescriptiveComplexity.IPRed.solEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

namespace IPRed

open Language Structure

variable (A : Type) [Language.binWeights.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The solutions of the one-equation program are the solutions of the
subset-sum instance**, bijectively. -/
def solEquiv {a₀ : A} (ha₀ : IsBot a₀) :
    {S : A → Prop // KnapsackSol A S} ≃
      {x : ipInterp.Map A → Prop // ZeroOneSol (ipInterp.Map A) x} where
  toFun S := ⟨colsOf S.1, ipInterp.map_finite A, isLinOrd_ipLe S.2.2.1,
    (zeroOneSol_colsOf S.2.2.2.1 S.2.2.2.2).1, (zeroOneSol_colsOf S.2.2.2.1 S.2.2.2.2).2⟩
  invFun x := ⟨itemsOfCols x.1, ‹Finite A›, isLinOrd_bwLe_of_ipLe x.2.2.1,
    (subsetSum_itemsOfCols ha₀ x.2.2.2.1 x.2.2.2.2).1,
    (subsetSum_itemsOfCols ha₀ x.2.2.2.1 x.2.2.2.2).2⟩
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨x, hx⟩
    refine Subtype.ext (funext fun q => ?_)
    change x (ipPt (q.2 0)) = x q
    rw [← ipPt_surj q]

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpZeroOneIP_map : SharpZeroOneIP (ipInterp.Map A) = SharpKnapsack A := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpZeroOneIP_apply, sharpKnapsack_apply]
  exact (Nat.card_congr (solEquiv A ha₀)).symm

end IPRed

open IPRed in
/-- **#Knapsack reduces parsimoniously to #0-1 integer programming.** -/
noncomputable def sharpKnapsack_ordered_parsimonious_sharpZeroOneIP :
    SharpKnapsack ≤ᵖ[≤] SharpZeroOneIP where
  Tag := Unit
  dim := 1
  toInterpretation := ipInterp
  correct A _ _ _ _ := (sharpZeroOneIP_map A).symm

/-- #0-1 integer programming is parsimoniously `#P`-hard. -/
theorem sharpZeroOneIP_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpZeroOneIP :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpKnapsack_ordered_parsimonious_sharpZeroOneIP sharpKnapsack_sharpP_parsimoniousHard

/-- **#0-1 integer programming is parsimoniously `#P`-complete**, its entries
being written in binary. -/
theorem sharpZeroOneIP_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpZeroOneIP :=
  ⟨sharpZeroOneIP_mem_sharpP, sharpZeroOneIP_sharpP_parsimoniousHard⟩

end DescriptiveComplexity
