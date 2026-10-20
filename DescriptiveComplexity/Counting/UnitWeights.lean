/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.WeightedWorlds

/-!
# Possible worlds are weighted worlds of weight one

The unweighted problem of `DescriptiveComplexity.Counting.PossibleWorlds`,
where every uncertain fact is present with probability `1/2`, is the case of
`DescriptiveComplexity.Counting.WeightedWorlds` in which every fact has the
weights `1` and `1`.

* `DescriptiveComplexity.unitWeightStructure`: the weighted instance of an
  ordered instance, the weight `1` being the single bit of the least position
  (`DescriptiveComplexity.binNum_isBot`);
* `DescriptiveComplexity.weightedWorlds_unitWeight`: its weighted worlds are
  counted like the worlds of the instance, every product of weights being `1`;
* `DescriptiveComplexity.possibleWorlds_ordered_parsimonious_weightedWorlds`:
  the instance is first-order definable
  (`DescriptiveComplexity.unitWeightInterp`), so counting worlds reduces
  parsimoniously to counting weighted worlds. The reduction is an *ordered*
  one: writing the number `1` means naming the least position.

So a hardness result for the unweighted problem is a hardness result for the
weighted one, at uniform probability `1/2`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

/-- The weighted instance of an instance with certain and uncertain facts,
over a linear order: every weight is `1`, written as the single bit of the
least position. -/
@[instance_reducible]
def unitWeightStructure (A : Type) [(L.sum L).Structure A] [LinearOrder A] :
    (weightedLang L).Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {n} R x =>
    match n, R, x with
    | _, .cert R, x => RelMap (L := L.sum L) (M := A) (Sum.inl R) x
    | _, .unc R, x => RelMap (L := L.sum L) (M := A) (Sum.inr R) x
    | _, .pres _, y => IsBot (y (Fin.last _))
    | _, .abs _, y => IsBot (y (Fin.last _))
    | _, .le, y => y 0 ≤ y 1

section Unit

variable {A : Type} [(L.sum L).Structure A] [LinearOrder A]

/-- The number whose only bit is at the least position is `1`. -/
theorem binNum_isBot [Finite A] [Nonempty A] :
    binNum (fun a b : A => a ≤ b) (fun _ => True) (fun i => IsBot i) = 1 := by
  obtain ⟨b, hb⟩ : ∃ b : A, IsBot b := by
    obtain ⟨b, hb⟩ := Finite.exists_min (id : A → A)
    exact ⟨b, hb⟩
  have hset : {p : A | True ∧ IsBot p} = {b} := by
    ext p
    simp only [Set.mem_ofPred_eq, true_and, Set.mem_singleton_iff]
    exact ⟨fun hp => le_antisymm (hp b) (hb p), fun h => h ▸ hb⟩
  have hrank : bitRank (fun a b : A => a ≤ b) (fun _ => True) b = 0 := by
    rw [bitRank, Set.ncard_eq_zero]
    ext q
    simp only [Set.mem_ofPred_eq, true_and, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact fun hq => le_antisymm hq (hb q)
  rw [binNum, hset, finsum_mem_singleton, hrank, pow_zero]

/-- **With every weight equal to one, counting weighted worlds is counting
worlds.** -/
theorem weightedWorlds_unitWeight [L.IsRelational] [Finite A] [Nonempty A] (φ : L.Sentence) :
    (letI := unitWeightStructure (L := L) A; WeightedWorlds φ A) = PossibleWorlds φ A := by
  let := unitWeightStructure (L := L) A
  have hle : WLe L A = fun a b : A => a ≤ b := rfl
  have hlin : IsLinOrd (WLe L A) := by
    rw [hle]
    exact ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩
  have hpres : ∀ q : Fact L A, binNum (WLe L A) (fun _ => True)
      (bitsOf (WeightedRel.pres q.1.2) q.2) = 1 := fun q => by
    have h1 : bitsOf (WeightedRel.pres q.1.2) q.2 = fun i : A => IsBot i := funext fun i => by
      change IsBot (Fin.snoc (α := fun _ => A) q.2 i (Fin.last _)) = IsBot i
      rw [Fin.snoc_last]
    rw [h1, hle]
    exact binNum_isBot
  have habs : ∀ q : Fact L A, binNum (WLe L A) (fun _ => True)
      (bitsOf (WeightedRel.abs q.1.2) q.2) = 1 := fun q => by
    have h1 : bitsOf (WeightedRel.abs q.1.2) q.2 = fun i : A => IsBot i := funext fun i => by
      change IsBot (Fin.snoc (α := fun _ => A) q.2 i (Fin.last _)) = IsBot i
      rw [Fin.snoc_last]
    rw [h1, hle]
    exact binNum_isBot
  have hw : ∀ (ρ : (worldBlock L).Assignment A) (q : Fact L A), factWeight ρ q = 1 := by
    intro ρ q
    by_cases ho : IsOpen q <;> by_cases hρ : ρ q.1 q.2 <;>
      simp only [factWeight, ho, hρ, ↓reduceIte, hpres, habs]
  let := Fintype.ofFinite {ρ : (worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ}
  have hsum : (∑ᶠ ρ : {ρ : (worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ},
      ∏ᶠ q : Fact L A, factWeight ρ.1 q) =
      ∑ᶠ _ : {ρ : (worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ}, 1 :=
    finsum_congr fun ρ => (finprod_congr fun q => hw ρ.1 q).trans finprod_one
  rw [weightedWorlds_eq_weightSum hlin, possibleWorlds_apply, hsum,
    finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun ρ =>
    and_congr_left' ⟨fun h p x => h ⟨p, x⟩, fun h q => h q.1 q.2⟩)

end Unit

/-! ### The interpretation -/

/-- The certain facts of a symbol, over the ordered expansion. -/
abbrev uwCert {n : ℕ} (R : L.Relations n) : ((L.sum L).sum Language.order).Relations n :=
  Sum.inl (Sum.inl R)

/-- The uncertain facts of a symbol, over the ordered expansion. -/
abbrev uwUnc {n : ℕ} (R : L.Relations n) : ((L.sum L).sum Language.order).Relations n :=
  Sum.inl (Sum.inr R)

/-- The order symbol of the ordered expansion. -/
abbrev uwLe (L : Language.{0, 0}) : ((L.sum L).sum Language.order).Relations 2 :=
  Sum.inr leSymb

/-- The weighted instance of weight one, drawn first-order from an ordered
instance: the facts are kept, the order of the positions is the order of the
instance, and the only bit of every weight is at the least element. -/
noncomputable def unitWeightInterp (L : Language.{0, 0}) :
    FOInterpretation ((L.sum L).sum Language.order) (weightedLang L) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .cert R => fun _ => Relations.formula (uwCert R) fun m => Term.var (m, 0)
    | _, .unc R => fun _ => Relations.formula (uwUnc R) fun m => Term.var (m, 0)
    | _, .pres _ => fun _ => Formula.iAlls Unit
        (Relations.formula₂ (uwLe L) (Term.var (Sum.inl (Fin.last _, 0))) (Term.var (Sum.inr ())))
    | _, .abs _ => fun _ => Formula.iAlls Unit
        (Relations.formula₂ (uwLe L) (Term.var (Sum.inl (Fin.last _, 0))) (Term.var (Sum.inr ())))
    | _, .le => fun _ => Relations.formula₂ (uwLe L) (Term.var (0, 0)) (Term.var (1, 0))

/-- The interpreted structure is the weighted instance of weight one. -/
noncomputable def unitWeightLEquiv (A : Type) [(L.sum L).Structure A] [LinearOrder A] :
    @Language.Equiv (weightedLang L) ((unitWeightInterp L).Map A) A
      (FOInterpretation.mapStructure (unitWeightInterp L) A) (unitWeightStructure A) :=
  letI := unitWeightStructure (L := L) A
  { toEquiv := (unitWeightInterp L).mapEquivSelf A
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      rw [FOInterpretation.relMap_map]
      cases R with
      | cert R =>
        exact (Formula.realize_rel (M := A) (R := uwCert R)
          (ts := fun m => Term.var (m, (0 : Fin 1)))
          (v := fun p : Fin _ × Fin 1 => (x p.1).2 p.2)).symm
      | unc R =>
        exact (Formula.realize_rel (M := A) (R := uwUnc R)
          (ts := fun m => Term.var (m, (0 : Fin 1)))
          (v := fun p : Fin _ × Fin 1 => (x p.1).2 p.2)).symm
      | pres R =>
        refine Iff.trans ?_ Formula.realize_iAlls.symm
        simp only [Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
        exact ⟨fun h f => h (f ()), fun h a => h fun _ => a⟩
      | abs R =>
        refine Iff.trans ?_ Formula.realize_iAlls.symm
        simp only [Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
        exact ⟨fun h f => h (f ()), fun h a => h fun _ => a⟩
      | le =>
        exact (Formula.realize_rel₂ (M := A) (R := uwLe L)
          (t₁ := Term.var ((0 : Fin 2), (0 : Fin 1))) (t₂ := Term.var ((1 : Fin 2), (0 : Fin 1)))
          (v := fun p : Fin 2 × Fin 1 => (x p.1).2 p.2)).symm }

/-- **Counting possible worlds reduces parsimoniously to counting weighted
worlds**, by giving every fact the weights `1` and `1`. The reduction is
ordered: it names the least position. -/
noncomputable def possibleWorlds_ordered_parsimonious_weightedWorlds [L.IsRelational]
    (φ : L.Sentence) : PossibleWorlds φ ≤ᵖ[≤] WeightedWorlds φ where
  Tag := Unit
  dim := 1
  toInterpretation := unitWeightInterp L
  correct := fun A _ _ _ _ =>
    (weightedWorlds_unitWeight φ).symm.trans
      (@CountingProblem.iso_invariant _ _ (WeightedWorlds φ) ((unitWeightInterp L).Map A) A
        (FOInterpretation.mapStructure (unitWeightInterp L) A) (unitWeightStructure A)
        (unitWeightLEquiv A)).symm

end DescriptiveComplexity
