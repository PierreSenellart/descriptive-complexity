/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.WeightedWorlds
import DescriptiveComplexity.Counting.Independence

/-!
# Weighted worlds, with every fact as a variable

`DescriptiveComplexity.weightedWorlds_eq_weightedCount` reads the count of the
weighted worlds as a weighted count over the valuations of the *open* facts.
For computing it, a more uniform reading is convenient: **every** fact of the
schema over the universe is a Boolean variable, with two weights that say
everything about its status
(`DescriptiveComplexity.fullPresWeight`, `DescriptiveComplexity.fullAbsWeight`):

| the fact is | weight of presence | weight of absence |
| --- | --- | --- |
| certain | `1` | `0` |
| open | its weight of presence | its weight of absence |
| neither | `0` | `1` |

A valuation that is not a possible world then has weight `0`, and the count is
a weighted count over all the valuations
(`DescriptiveComplexity.weightedWorlds_eq_weightedCount_facts`), with no
side condition on the worlds: the independence lemmas of
`DescriptiveComplexity.Counting.Independence` apply to it as they stand.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] {A : Type}
  [(weightedLang L).Structure A]

open Classical in
/-- The weight of presence of a fact, whatever its status. -/
noncomputable def fullPresWeight (q : Fact L A) : ℕ :=
  if RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2 then 1
  else if RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 then
    binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.pres q.1.2) q.2)
  else 0

open Classical in
/-- The weight of absence of a fact, whatever its status. -/
noncomputable def fullAbsWeight (q : Fact L A) : ℕ :=
  if RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2 then 0
  else if RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 then
    binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.abs q.1.2) q.2)
  else 1

/-- The family of relations of a valuation of all the facts. -/
def factWorld (v : Fact L A → Bool) : (worldBlock L).Assignment A :=
  fun p x => v ⟨p, x⟩ = true

/-- The facts over a finite universe, as a finite type. -/
noncomputable instance factFintype [Finite A] : Fintype (Fact L A) :=
  Fintype.ofFinite _

open Classical in
/-- Families of relations are valuations of the facts. -/
noncomputable def factWorldEquiv (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)]
    (A : Type) :
    (Fact L A → Bool) ≃ (worldBlock L).Assignment A where
  toFun := factWorld
  invFun ρ := fun q => decide (ρ q.1 q.2)
  left_inv v := funext fun ⟨p, x⟩ => by
    cases h : v ⟨p, x⟩ <;> simp [factWorld, h]
  right_inv ρ := funext fun p => funext fun x => propext decide_eq_true_iff

open Classical in
omit [L.IsRelational] in
/-- **The weight of a valuation of all the facts**: the product of the weights
of the facts if it is a possible world, and `0` otherwise. -/
theorem prod_fullWeight [Finite A] [Fintype (Fact L A)] (ρ : (worldBlock L).Assignment A) :
    (∏ q : Fact L A, if ρ q.1 q.2 then fullPresWeight q else fullAbsWeight q) =
      if IsWeightedWorld ρ then ∏ᶠ q : Fact L A, factWeight ρ q else 0 := by
  by_cases hw : IsWeightedWorld ρ
  · rw [if_pos hw, finprod_eq_prod_of_fintype]
    refine Finset.prod_congr rfl fun q _ => ?_
    by_cases hc : RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2
    · have ho : ¬IsOpen q := fun h => h.2 hc
      simp only [fullPresWeight, factWeight, hc, (hw q).1 hc, ho, ↓reduceIte]
    · by_cases hu : RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2
      · have ho : IsOpen q := ⟨hu, hc⟩
        by_cases hρ : ρ q.1 q.2 <;>
          simp only [fullPresWeight, fullAbsWeight, factWeight, hc, hu, ho, hρ, ↓reduceIte]
      · have ho : ¬IsOpen q := fun h => hu h.1
        have hρ : ¬ρ q.1 q.2 := fun h => ((hw q).2 h).elim hc hu
        simp only [fullAbsWeight, factWeight, hc, hu, ho, hρ, ↓reduceIte]
  · rw [if_neg hw]
    obtain ⟨q, hq⟩ := not_forall.mp hw
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    by_cases hc : RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2
    · have hρ : ¬ρ q.1 q.2 := fun h => hq ⟨fun _ => h, fun _ => Or.inl hc⟩
      simp only [fullAbsWeight, hc, hρ, ↓reduceIte]
    · by_cases hρ : ρ q.1 q.2
      · have hu : ¬RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 :=
          fun h => hq ⟨fun h' => absurd h' hc, fun _ => Or.inr h⟩
        simp only [fullPresWeight, hc, hu, hρ, ↓reduceIte]
      · exact absurd ⟨fun h => absurd h hc, fun h => absurd h hρ⟩ hq

open Classical in
/-- **The count is a weighted count over the valuations of all the facts**: on
an instance whose positions are linearly ordered, counting the weighted worlds
of a sentence is the weighted count of the event that the sentence holds, every
fact being a variable. -/
theorem weightedWorlds_eq_weightedCount_facts [Finite A] [Fintype (Fact L A)]
    [DecidableEq (Fact L A)] (hlin : IsLinOrd (WLe L A)) (φ : L.Sentence) :
    WeightedWorlds φ A = weightedCount fullPresWeight fullAbsWeight
      (fun v : Fact L A → Bool =>
        decide (@Sentence.Realize L A (worldStructure (factWorld v)) φ)) := by
  let P : (worldBlock L).Assignment A → Prop := fun ρ =>
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ
  let := Fintype.ofFinite {ρ : (worldBlock L).Assignment A // P ρ}
  let := Fintype.ofFinite ((worldBlock L).Assignment A)
  rw [weightedWorlds_eq_weightSum hlin, finsum_eq_sum_of_fintype, weightedCount]
  have h1 : (∑ ρ : {ρ : (worldBlock L).Assignment A // P ρ}, ∏ᶠ q : Fact L A,
      factWeight ρ.1 q) =
      ∑ ρ : (worldBlock L).Assignment A, if P ρ then ∏ᶠ q : Fact L A, factWeight ρ q else 0 := by
    rw [← Finset.sum_filter,
      Finset.sum_subtype (p := P) (Finset.univ.filter P) (by simp)]
  refine h1.trans ((Fintype.sum_equiv (factWorldEquiv L A) _ _ fun v => ?_).symm)
  change _ = if P (factWorld v) then ∏ᶠ q : Fact L A, factWeight (factWorld v) q else 0
  have hw := prod_fullWeight (L := L) (factWorld v)
  have hval : valWeight fullPresWeight fullAbsWeight v =
      if IsWeightedWorld (factWorld v) then ∏ᶠ q : Fact L A, factWeight (factWorld v) q
      else 0 := by
    rw [← hw, valWeight]
    exact Finset.prod_congr rfl fun q _ => if_congr Iff.rfl rfl rfl
  by_cases hφ : @Sentence.Realize L A (worldStructure (factWorld v)) φ
  · rw [if_pos (decide_eq_true hφ), hval]
    exact if_congr (and_iff_left hφ).symm rfl rfl
  · rw [if_neg (by simpa using hφ), if_neg fun h : P (factWorld v) => hφ h.2]

end DescriptiveComplexity
