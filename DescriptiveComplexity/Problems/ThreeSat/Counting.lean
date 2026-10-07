/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeSat.ToSat
import DescriptiveComplexity.Problems.Sat.Counting

/-!
# #3SAT: counting the models of a 3-CNF formula

The counting version of `DescriptiveComplexity.ThreeSAT`: the number of models of a CNF
formula whose clauses have at most three literals. As for the decision
problem, the width bound is folded in: an instance violating it has no model
to count. Models are those of `DescriptiveComplexity.SharpSAT` – sets of variables of
the formula (`DescriptiveComplexity.SatModel`).

`DescriptiveComplexity.SharpThreeSAT` is in `#P`
(`DescriptiveComplexity.sharpThreeSat_mem_sharpP`), the kernel of #SAT being conjoined
with the first-order sentence stating the width bound. Its parsimonious
hardness is in `DescriptiveComplexity.Problems.ThreeSat.CountingFromSat`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The first-order kernel of #3SAT: no clause is wide, and the truth
assignment is a model. -/
noncomputable def sharpThreeSatKernel : satSOLang.Sentence :=
  ∼(LHom.sumInl.onSentence ThreeSatToSat.wideS) ⊓ sharpSatKernel

/-- Realization of the kernel of #3SAT. -/
theorem realize_sharpThreeSatKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpThreeSatKernel) ↔
      WidthAtMostThree A ∧ SatModel A ((satAssignEquiv A).symm ρ) := by
  have h2 := realize_sharpSatKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpThreeSatKernel, Sentence.Realize, Formula.realize_inf, Formula.realize_not]
  refine and_congr ?_ h2
  have h1 : (A ⊨ (LHom.sumInl.onSentence ThreeSatToSat.wideS : satSOLang.Sentence)) ↔
      ThreeSatToSat.Wide A :=
    (LHom.realize_onSentence A LHom.sumInl ThreeSatToSat.wideS).trans
      (ThreeSatToSat.realize_wideS (A := A))
  exact (not_congr (h1.trans (ThreeSatToSat.wide_iff_not_widthAtMostThree (A := A)))).trans
    not_not

/-- The number of models of a 3-CNF formula is the number of witnesses of the
kernel of #3SAT. -/
theorem card_threeSatModel_eq_witnessCount (A : Type) [Language.sat.Structure A] :
    Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν} =
      witnessCount satAssignBlock sharpThreeSatKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpThreeSatKernel, Equiv.symm_apply_apply])

/-- **#3SAT**: the number of models of a CNF formula with at most three
literals per clause; zero when some clause is wider. -/
noncomputable def SharpThreeSAT : CountingProblem Language.sat where
  Count := fun A inst =>
    Nat.card {ν : A → Prop // @WidthAtMostThree A inst ∧ @SatModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_threeSatModel_eq_witnessCount A, card_threeSatModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpThreeSatKernel e

theorem sharpThreeSat_apply (A : Type) [Language.sat.Structure A] :
    SharpThreeSAT A = Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν} :=
  rfl

/-- On an instance within the width bound, #3SAT is #SAT. -/
theorem sharpThreeSat_eq_sharpSat {A : Type} [Language.sat.Structure A]
    (h : WidthAtMostThree A) : SharpThreeSAT A = SharpSAT A :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right h)

/-- **The support of #3SAT is 3SAT.**
Registered in the Lax archive as
[`Lax280166.ThreeSATComplete.sharpThreeSat_support_iff`](https://laxarchive.org/lax-280166/Lax280166.ThreeSATComplete.html#s-Lax280166.ThreeSATComplete.sharpThreeSat_support_iff). -/
theorem sharpThreeSat_support_iff (A : Type) [Language.sat.Structure A] [Finite A] :
    SharpThreeSAT.support A ↔ ThreeSAT A := by
  by_cases h : WidthAtMostThree A
  · rw [CountingProblem.support_iff, sharpThreeSat_eq_sharpSat h]
    exact (sharpSat_support_iff A).trans (and_iff_right h).symm
  · refine iff_of_false ?_ fun hT => h hT.1
    rw [CountingProblem.support_iff, sharpThreeSat_apply, Nat.card_pos_iff]
    rintro ⟨⟨_, hw, -⟩, -⟩
    exact h hw

/-- **#3SAT is in `#P`.** -/
theorem sharpThreeSat_mem_sharpP : SharpThreeSAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_threeSatModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpThreeSatKernel)

end DescriptiveComplexity
