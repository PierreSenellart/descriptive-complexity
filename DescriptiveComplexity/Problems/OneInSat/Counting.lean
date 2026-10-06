/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Defs
import DescriptiveComplexity.Problems.Sat.Counting

/-!
# #1-in-SAT: counting exactly-one models

The counting version of `DescriptiveComplexity.OneInSAT`: the number of assignments
giving every clause *exactly one* true literal. As for #SAT, an assignment is
a set of variables of the formula – of elements occurring in a clause
(`DescriptiveComplexity.OneInModel`).

`DescriptiveComplexity.SharpOneInSAT` is in `#P`
(`DescriptiveComplexity.sharpOneInSat_mem_sharpP`); its parsimonious hardness is in
`DescriptiveComplexity.Problems.OneInSat.CountingFromSat`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-- The set `ν` of true variables is an exactly-one model of the CNF formula:
every clause has exactly one true literal, and `ν` consists of variables of
the formula. -/
def OneInModel (A : Type) [Language.sat.Structure A] (ν : A → Prop) : Prop :=
  OneInProper ν ∧ ∀ x : A, ν x → SatOccurs A x

/-- The first-order kernel of #1-in-SAT. -/
noncomputable def sharpOneInKernel : satSOLang.Sentence :=
  oneInKernel ⊓ satVarKernel

/-- Realization of the kernel of #1-in-SAT. -/
theorem realize_sharpOneInKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpOneInKernel) ↔
      OneInModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_oneInKernel_iff_oneInProper ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpOneInKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

/-- The number of exactly-one models is the number of witnesses of the
kernel. -/
theorem card_oneInModel_eq_witnessCount (A : Type) [Language.sat.Structure A] :
    Nat.card {ν : A → Prop // OneInModel A ν} =
      witnessCount satAssignBlock sharpOneInKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpOneInKernel, Equiv.symm_apply_apply])

/-- **#1-in-SAT**: the number of assignments of the variables of a CNF formula
giving every clause exactly one true literal. -/
noncomputable def SharpOneInSAT : CountingProblem Language.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @OneInModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_oneInModel_eq_witnessCount A, card_oneInModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpOneInKernel e

theorem sharpOneInSat_apply (A : Type) [Language.sat.Structure A] :
    SharpOneInSAT A = Nat.card {ν : A → Prop // OneInModel A ν} :=
  rfl

/-- An exactly-one proper assignment restricts to an exactly-one model: only
its values at the variables of the formula matter. -/
theorem oneInModel_restrict {A : Type} [Language.sat.Structure A] {ν : A → Prop}
    (h : OneInProper ν) : OneInModel A fun x => ν x ∧ SatOccurs A x := by
  have hlit : ∀ c y t, OccIn c y t →
      (LitTrue (fun x => ν x ∧ SatOccurs A x) y t ↔ LitTrue ν y t) := by
    intro c y t hy
    have hocc : SatOccurs A y := by
      cases t
      · exact ⟨c, hy.1, Or.inr hy.2⟩
      · exact ⟨c, hy.1, Or.inl hy.2⟩
    cases t
    · exact not_congr (and_iff_left hocc)
    · exact and_iff_left hocc
  refine ⟨fun c hc => ?_, fun x hx => hx.2⟩
  obtain ⟨x, s, hx, hT, huniq⟩ := h c hc
  exact ⟨x, s, hx, (hlit c x s hx).mpr hT,
    fun y t hy hTy => huniq y t hy ((hlit c y t hy).mp hTy)⟩

/-- **The support of #1-in-SAT is 1-in-SAT.** -/
theorem sharpOneInSat_support_iff (A : Type) [Language.sat.Structure A] [Finite A] :
    SharpOneInSAT.support A ↔ OneInSAT A := by
  rw [CountingProblem.support_iff, sharpOneInSat_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨ν, hν⟩, -⟩
    exact ⟨ν, hν.1⟩
  · rintro ⟨ν, hν⟩
    exact ⟨⟨⟨_, oneInModel_restrict hν⟩⟩, inferInstance⟩

/-- **#1-in-SAT is in `#P`.** -/
theorem sharpOneInSat_mem_sharpP : SharpOneInSAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_oneInModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpOneInKernel)

end DescriptiveComplexity
