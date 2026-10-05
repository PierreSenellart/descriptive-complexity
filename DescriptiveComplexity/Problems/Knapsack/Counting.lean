/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Membership
import DescriptiveComplexity.Counting.Class

/-!
# #Knapsack: counting the solutions of a subset-sum instance

The counting version of `DescriptiveComplexity.Knapsack`: the number of sets of items
whose binary weights sum exactly to the target
(`DescriptiveComplexity.KnapsackSol`).

Membership in `#P` (`DescriptiveComplexity.sharpKnapsack_mem_sharpP`) is where a
counting definition differs from a `Σ₁` one. The certificate of
`DescriptiveComplexity.knapsack_sigmaSODefinable` carries, besides the chosen items,
the running totals and the carries of an addition walk, and a count of
certificates is a count of solutions only if a solution has *one*: the totals
and carries are forced where the walk reads them
(`DescriptiveComplexity.isChain_agree`), and the counting kernel
(`DescriptiveComplexity.sharpKnapsackKernel`) forbids them anywhere else. The
certificates are then the solutions, bijectively
(`DescriptiveComplexity.knapsackEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Language.binWeights.Structure A]

/-- The set `S` of items is a solution: the instance is finite, its order is
linear, and the weights of `S` sum exactly to the target. -/
def KnapsackSol (S : A → Prop) : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧ (∀ i, S i → BWItem i) ∧
    (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

variable {A}

/-- The certificate built on a walk: the chosen items, and the totals and
carries of the walk kept only where a walk reads them. -/
def certOfWalk (S : A → Prop) (PS Cy : A → A → Prop) : knapsackGuessBlock.Assignment A :=
  fun idx => match idx with
    | .sel => fun w : Fin 1 → A => S (w 0)
    | .pS => fun w : Fin 2 → A => PS (w 0) (w 1) ∧ BWItem (w 0) ∧ BWPosn (w 1)
    | .carry => fun w : Fin 2 → A =>
        Cy (w 0) (w 1) ∧ BWItem (w 0) ∧ BWPosn (w 1) ∧ ¬MinPos BWLe BWItem (w 0)

/-- A walk ending on the target gives a certificate of the counting kernel. -/
theorem knapsackCert_certOfWalk (hlin : IsLinOrd (BWLe (A := A))) {S : A → Prop}
    {PS Cy : A → A → Prop} (hSitem : ∀ i, S i → BWItem i)
    (hchain : IsChain BWLe BWItem BWLe BWPosn S BWBit PS Cy)
    (hfinal : ∀ i p : A, MaxPos BWLe BWItem i → BWPosn p → (PS i p ↔ BWTgt p))
    (hempty : (∀ i : A, ¬BWItem i) → ∀ p : A, BWPosn p → ¬BWTgt p) :
    KnapsackCert A (certOfWalk S PS Cy) := by
  have hnmin : ∀ {i j : A}, SuccPos BWLe BWItem i j → ¬MinPos BWLe BWItem j := fun hij hmin =>
    hij.2.2.2.1 (hlin.2.2.1 _ _ hij.2.2.1 (hmin.2 _ hij.1))
  refine ⟨hlin, hSitem, ?_, fun i p hi hp => ?_, hempty, fun i p h => h.2,
    fun i p h => h.2⟩
  · exact hchain.congr (fun i p hi hp => (and_iff_left ⟨hi, hp⟩).symm)
      (fun i j p hij hp => (and_iff_left ⟨hij.2.1, hp, hnmin hij⟩).symm)
  · exact (and_iff_left ⟨hi.1, hp⟩).trans (hfinal i p hi hp)

variable [Finite A]

/-- A solution has a certificate. -/
theorem exists_knapsackCert {S : A → Prop} (h : KnapsackSol A S) :
    ∃ PS Cy : A → A → Prop, IsChain BWLe BWItem BWLe BWPosn S BWBit PS Cy ∧
      KnapsackCert A (certOfWalk S PS Cy) := by
  obtain ⟨-, hlin, hSitem, hsum⟩ := h
  obtain ⟨PS, Cy, hchain, hfinal, hempty⟩ := exists_chain_of_subsetSum hlin hSitem hsum
  exact ⟨PS, Cy, hchain, knapsackCert_certOfWalk hlin hSitem hchain hfinal hempty⟩

/-- The chosen items of a certificate are a solution. -/
theorem knapsackSol_of_cert {ρ : knapsackGuessBlock.Assignment A} (h : KnapsackCert A ρ) :
    KnapsackSol A fun i => ρ .sel ![i] := by
  obtain ⟨hlin, hsel, hchain, hfinal, hempty, -, -⟩ := h
  exact ⟨‹Finite A›, hlin, hsel, subsetSum_of_chain hlin hsel hchain hfinal hempty⟩

variable (A) in
/-- **The solutions of a subset-sum instance are the witnesses of the counting
kernel**, bijectively: a solution has exactly one certificate. -/
noncomputable def knapsackEquiv :
    {ρ : knapsackGuessBlock.Assignment A //
        @Sentence.Realize ksSOLang A
          (@sumStructure _ _ A _ (knapsackGuessBlock.structure ρ)) sharpKnapsackKernel} ≃
      {S : A → Prop // KnapsackSol A S} where
  toFun ρ := ⟨fun i => ρ.1 .sel ![i],
    knapsackSol_of_cert ((realize_sharpKnapsackKernel ρ.1).mp ρ.2)⟩
  invFun S := ⟨certOfWalk S.1 (exists_knapsackCert S.2).choose
      (exists_knapsackCert S.2).choose_spec.choose,
    (realize_sharpKnapsackKernel _).mpr (exists_knapsackCert S.2).choose_spec.choose_spec.2⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hcert := (realize_sharpKnapsackKernel ρ).mp hρ
    have hsol := knapsackSol_of_cert hcert
    obtain ⟨hlin, hsel, hchainρ, -, -, hpin₁, hpin₂⟩ := hcert
    have hchain := (exists_knapsackCert hsol).choose_spec.choose_spec.1
    obtain ⟨hPS, hCy⟩ := isChain_agree hlin hlin hsel hchain hchainρ
    refine Subtype.ext (funext fun idx => ?_)
    cases idx with
    | sel =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .sel) (funext fun k => by fin_cases k; rfl)
    | pS =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw : ρ .pS ![w 0, w 1] ↔ ρ .pS w :=
        iff_of_eq (congrArg (ρ .pS) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hi, hp⟩
        exact hw.mp ((hPS _ _ hi hp).mp h)
      · intro h
        obtain ⟨hi, hp⟩ := hpin₁ _ _ (hw.mpr h)
        exact ⟨(hPS _ _ hi hp).mpr (hw.mpr h), hi, hp⟩
    | carry =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw : ρ .carry ![w 0, w 1] ↔ ρ .carry w :=
        iff_of_eq (congrArg (ρ .carry) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hi, hp, hnmin⟩
        obtain ⟨j, hj⟩ := exists_predPos hlin hi hnmin
        exact hw.mp ((hCy _ _ _ hj hp).mp h)
      · intro h
        obtain ⟨hi, hp, hnmin⟩ := hpin₂ _ _ (hw.mpr h)
        obtain ⟨j, hj⟩ := exists_predPos hlin hi hnmin
        exact ⟨(hCy _ _ _ hj hp).mpr (hw.mpr h), hi, hp, hnmin⟩
  right_inv := fun _ => rfl

end Solutions

/-- **#Knapsack**: the number of sets of items whose weights sum exactly to the
target. -/
noncomputable def SharpKnapsack : CountingProblem Language.binWeights where
  Count := fun A inst => Nat.card {S : A → Prop // @KnapsackSol A inst S}
  iso_invariant := fun {A B} _ _ e => by
    by_cases hfin : Finite A
    · have : Finite B := Finite.of_equiv A e.toEquiv
      rw [← Nat.card_congr (knapsackEquiv A), ← Nat.card_congr (knapsackEquiv B)]
      exact witnessCount_iso knapsackGuessBlock sharpKnapsackKernel e
    · have hB : ¬Finite B := fun h => hfin (Finite.of_equiv B e.toEquiv.symm)
      have hA0 : IsEmpty {S : A → Prop // KnapsackSol A S} := ⟨fun S => hfin S.2.1⟩
      have hB0 : IsEmpty {S : B → Prop // KnapsackSol B S} := ⟨fun S => hB S.2.1⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

theorem sharpKnapsack_apply (A : Type) [Language.binWeights.Structure A] :
    SharpKnapsack A = Nat.card {S : A → Prop // KnapsackSol A S} :=
  rfl

/-- **The support of #Knapsack is Knapsack.** -/
theorem sharpKnapsack_support_iff (A : Type) [Language.binWeights.Structure A] [Finite A] :
    SharpKnapsack.support A ↔ Knapsack A := by
  rw [CountingProblem.support_iff, sharpKnapsack_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨S, hfin, hlin, hS, hsum⟩, -⟩
    exact ⟨hfin, hlin, S, hS, hsum⟩
  · rintro ⟨hfin, hlin, S, hS, hsum⟩
    exact ⟨⟨⟨S, hfin, hlin, hS, hsum⟩⟩, inferInstance⟩

/-- **#Knapsack is in `#P`**: a solution has exactly one certificate of the
counting kernel. -/
theorem sharpKnapsack_mem_sharpP : SharpKnapsack ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (knapsackEquiv A))
    (sharpPDefinable_ofKernel knapsackGuessBlock sharpKnapsackKernel)

end DescriptiveComplexity
