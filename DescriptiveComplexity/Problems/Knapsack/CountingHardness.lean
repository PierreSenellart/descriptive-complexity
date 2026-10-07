/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Counting
import DescriptiveComplexity.Problems.Knapsack.Hardness
import DescriptiveComplexity.Problems.ExactCoverCounting
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Knapsack is parsimoniously `#P`-complete

Karp's reduction of Exact Cover to Knapsack
(`DescriptiveComplexity.Problems.Knapsack.Hardness`) is parsimonious as it stands. Its
items are the sets of the family, one each, so a set of items *is* a subfamily;
and the weights of a set of items sum to the target exactly when the subfamily
is an exact cover, the digit of the block of a ground element counting the
chosen sets that contain it. Hence the solutions of the interpreted instance
are the exact covers of the set system, bijectively
(`DescriptiveComplexity.KnapRed.solEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

namespace KnapRed

open Language Structure

variable (A : Type) [Language.setSystem.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The solutions of the interpreted subset-sum instance are the exact covers
of the set system**, bijectively. -/
def solEquiv {a₀ : A} (ha₀ : IsBot a₀) :
    {G : A → Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G} ≃
      {S : kInterp.Map A → Prop // KnapsackSol (kInterp.Map A) S} where
  toFun G := ⟨itemsOf a₀ G.1, kInterp.map_finite A, isLinOrd_bwLe,
    (subsetSum_itemsOf ha₀ G.2).1, (subsetSum_itemsOf ha₀ G.2).2⟩
  invFun S := ⟨coverOfItems a₀ S.1, exactCoverBy_coverOfItems ha₀ S.2.2.2.1 S.2.2.2.2⟩
  left_inv := by
    rintro ⟨G, hG⟩
    refine Subtype.ext (funext fun s => propext ⟨?_, fun h => ⟨s, h, rfl⟩⟩)
    rintro ⟨s', hs', heq⟩
    rw [kItem_injective a₀ heq]
    exact hs'
  right_inv := by
    rintro ⟨S, hS⟩
    refine Subtype.ext (funext fun i => propext ⟨?_, fun h => ?_⟩)
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · have hi := (eq_kItem ha₀ (hS.2.2.1 i h)).1
      exact ⟨i.2 0, show S (kItem a₀ (i.2 0)) by rw [← hi]; exact h, hi⟩

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpKnapsack_map : SharpKnapsack (kInterp.Map A) = SharpExactCover A := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpKnapsack_apply, sharpExactCover_apply]
  exact (Nat.card_congr (solEquiv A ha₀)).symm

end KnapRed

open KnapRed in
/-- **#ExactCover reduces parsimoniously to #Knapsack.** -/
noncomputable def sharpExactCover_ordered_parsimonious_sharpKnapsack :
    SharpExactCover ≤ᵖ[≤] SharpKnapsack where
  Tag := KTag
  dim := 2
  toInterpretation := kInterp
  correct A _ _ _ _ := (sharpKnapsack_map A).symm

/-- #Knapsack is parsimoniously `#P`-hard. -/
theorem sharpKnapsack_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpKnapsack :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpExactCover_ordered_parsimonious_sharpKnapsack sharpExactCover_sharpP_parsimoniousHard

/-- **#Knapsack is parsimoniously `#P`-complete**, its weights being written in
binary.
Registered in the Lax archive as
[`Lax280166.KnapsackComplete.sharpKnapsack_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.KnapsackComplete.html#s-Lax280166.KnapsackComplete.sharpKnapsack_sharpP_parsimoniousComplete). -/
theorem sharpKnapsack_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpKnapsack :=
  ⟨sharpKnapsack_mem_sharpP, sharpKnapsack_sharpP_parsimoniousHard⟩

/-- `SharpKnapsack` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpKnapsack_sharpP_complete : SharpP.Complete SharpKnapsack :=
  complete_sharpP_of_parsimoniousComplete sharpKnapsack_sharpP_parsimoniousComplete

end DescriptiveComplexity
