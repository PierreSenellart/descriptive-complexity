/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ExactCover
import DescriptiveComplexity.Problems.SetFamily.Counting
import DescriptiveComplexity.Problems.OneInSat.CountingFromSat
import DescriptiveComplexity.Counting.Subtractive

/-!
# #ExactCover is parsimoniously `#P`-complete

The reduction of 1-in-SAT to Exact Cover in
`DescriptiveComplexity.Problems.ExactCover` is parsimonious as it stands: covering the
element of a variable exactly once *is* choosing one of its two literals, so
the exact covers of the literal set system are the exactly-one models of the
formula, bijectively (`DescriptiveComplexity.ExactCoverRed.modelEquiv`). No order, no
gadget, dimension 1.

The one thing counting asks of that reduction is that only the *variables* of
the formula be ground elements: an element occurring in no clause would
otherwise be covered by either of two singleton sets.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace ExactCoverRed

open Language Structure SatOcc

/-- **The exact covers of the literal set system are the exactly-one models of
the formula**, bijectively. -/
def modelEquiv (A : Type) [Language.sat.Structure A] :
    {ν : A → Prop // OneInModel A ν} ≃
      {G : ecInterp.Map A → Prop //
        ExactCoverBy (SSElem (A := ecInterp.Map A)) SSFam SSMem G} where
  toFun ν := ⟨coverOf ν.1, exactCoverBy_coverOf ν.2.1⟩
  invFun G := ⟨assignOf G.1, oneInProper_assignOf G.2,
    fun x hx => (ssFam_lset true x).mp (G.2.1 _ hx)⟩
  left_inv := by
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun x => propext ⟨?_, fun h => ⟨true, x, rfl, h, hν.2 x h⟩⟩)
    rintro ⟨s, y, heq, hT, -⟩
    obtain ⟨hs, rfl⟩ := ecPt_eq_iff.mp heq
    obtain rfl : true = s := by simpa using hs
    exact hT
  right_inv := by
    rintro ⟨G, hG⟩
    refine Subtype.ext (funext fun S => propext ⟨?_, fun h => ?_⟩)
    · rintro ⟨s, x, rfl, hT, hocc⟩
      exact (exactCoverBy_lit hG hocc s).mpr hT
    · obtain ⟨s, x, hocc, rfl⟩ := ssFam_cases (hG.1 S h)
      exact ⟨s, x, rfl, (exactCoverBy_lit hG hocc s).mp h, hocc⟩

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpExactCover_map (A : Type) [Language.sat.Structure A] :
    SharpExactCover (ecInterp.Map A) = SharpOneInSAT A := by
  rw [sharpExactCover_apply, sharpOneInSat_apply]
  exact (Nat.card_congr (modelEquiv A)).symm

end ExactCoverRed

open ExactCoverRed in
/-- **#1-in-SAT reduces parsimoniously to #ExactCover**, without an order. -/
noncomputable def sharpOneInSat_parsimonious_sharpExactCover :
    SharpOneInSAT ≤ᵖ SharpExactCover where
  Tag := ECTag
  dim := 1
  toInterpretation := ecInterp
  correct A _ _ _ := (sharpExactCover_map A).symm

/-- #ExactCover is parsimoniously `#P`-hard. -/
theorem sharpExactCover_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpExactCover :=
  SharpP.parsimoniousHard_of_parsimonious sharpOneInSat_parsimonious_sharpExactCover
    sharpOneInSat_sharpP_parsimoniousHard

/-- **#ExactCover is parsimoniously `#P`-complete.** -/
theorem sharpExactCover_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpExactCover :=
  ⟨sharpExactCover_mem_sharpP, sharpExactCover_sharpP_parsimoniousHard⟩

/-- `SharpExactCover` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpExactCover_sharpP_complete : SharpP.Complete SharpExactCover :=
  complete_sharpP_of_parsimoniousComplete sharpExactCover_sharpP_parsimoniousComplete

end DescriptiveComplexity
