/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.Membership
import DescriptiveComplexity.Counting.Class

/-!
# #ExactCover: counting exact covers

The counting version of `DescriptiveComplexity.ExactCover`: the number of subfamilies
of a set system covering every ground element exactly once
(`DescriptiveComplexity.ExactCoverBy`). A cover is a set of members of the family, so
nothing has to be said about the other elements of the instance.

`DescriptiveComplexity.SharpExactCover` is in `#P`
(`DescriptiveComplexity.sharpExactCover_mem_sharpP`); its parsimonious hardness is in
`DescriptiveComplexity.Problems.ExactCoverCounting`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- Subfamilies, as assignments of the guess block with an empty binary
relation. -/
def familyGuessOf {A : Type} (G : A → Prop) : familyGuessBlock.Assignment A :=
  fun i => match i with
    | .guess => fun w : Fin 1 → A => G (w 0)
    | .inj => fun _ : Fin 2 → A => False

/-- **The exact covers of a set system are the witnesses of the counting
kernel**, bijectively. -/
def exactCoverEquiv (A : Type) [Language.setSystem.Structure A] :
    {ρ : familyGuessBlock.Assignment A //
        @Sentence.Realize setFamilySOLang A
          (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) sharpExactCoverKernel} ≃
      {G : A → Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G} where
  toFun ρ := ⟨fun s => ρ.1 .guess ![s], ((realize_sharpExactCoverKernel ρ.1).mp ρ.2).1⟩
  invFun G := ⟨familyGuessOf G.1,
    (realize_sharpExactCoverKernel _).mpr ⟨G.2, fun _ _ h => h⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hinj := ((realize_sharpExactCoverKernel ρ).mp hρ).2
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | guess =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .guess) (funext fun k => by fin_cases k; rfl)
    | inj =>
      refine funext fun (w : Fin 2 → A) => propext ⟨fun h => h.elim, fun h => ?_⟩
      refine hinj (w 0) (w 1) ?_
      exact (congrArg (ρ .inj) (funext fun k => by fin_cases k <;> rfl)).mpr h
  right_inv := fun _ => rfl

/-- **#ExactCover**: the number of exact covers of a set system. -/
noncomputable def SharpExactCover : CountingProblem Language.setSystem where
  Count := fun A inst =>
    Nat.card {G : A → Prop //
      ExactCoverBy (@SSElem A inst) (@SSFam A inst) (@SSMem A inst) G}
  iso_invariant := fun {A B} _ _ e => by
    rw [← Nat.card_congr (exactCoverEquiv A), ← Nat.card_congr (exactCoverEquiv B)]
    exact witnessCount_iso familyGuessBlock sharpExactCoverKernel e

theorem sharpExactCover_apply (A : Type) [Language.setSystem.Structure A] :
    SharpExactCover A =
      Nat.card {G : A → Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G} :=
  rfl

/-- **The support of #ExactCover is Exact Cover.**
Registered in the Lax archive as
[`Lax280166.ExactCoverComplete.sharpExactCover_support_iff`](https://laxarchive.org/lax-280166/Lax280166.ExactCoverComplete.html#s-Lax280166.ExactCoverComplete.sharpExactCover_support_iff). -/
theorem sharpExactCover_support_iff (A : Type) [Language.setSystem.Structure A] [Finite A] :
    SharpExactCover.support A ↔ ExactCover A := by
  rw [CountingProblem.support_iff, sharpExactCover_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨G, hG⟩, _⟩ => ⟨G, hG⟩, fun ⟨G, hG⟩ => ⟨⟨⟨G, hG⟩⟩, inferInstance⟩⟩

/-- **#ExactCover is in `#P`.** -/
theorem sharpExactCover_mem_sharpP : SharpExactCover ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (exactCoverEquiv A))
    (sharpPDefinable_ofKernel familyGuessBlock sharpExactCoverKernel)

end DescriptiveComplexity
