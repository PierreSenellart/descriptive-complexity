/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ZeroOneIP.Membership
import DescriptiveComplexity.Counting.Class

/-!
# #0-1 integer programming: counting the `0-1` solutions

The counting version of `DescriptiveComplexity.ZeroOneIP`: the number of `0-1` vectors
`x` with `C x = d` (`DescriptiveComplexity.ZeroOneSol`), the entries being written in
binary.

Membership in `#P` (`DescriptiveComplexity.sharpZeroOneIP_mem_sharpP`) is Knapsack's
argument once per row (`DescriptiveComplexity.Problems.Knapsack.Counting`): the walks
of a certificate are forced where they are read
(`DescriptiveComplexity.isChain_agree`) and forbidden elsewhere by the counting kernel,
so a solution has exactly one certificate
(`DescriptiveComplexity.zeroOneIPEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Language.zeroOneIP.Structure A]

/-- The set `x` of columns is a solution: the instance is finite, its order is
linear, and every equation holds. -/
def ZeroOneSol (x : A → Prop) : Prop :=
  Finite A ∧ IsLinOrd (IPLe (A := A)) ∧ (∀ j, x j → IPCol j) ∧
    ∀ r, IPRow r → (∑ᶠ j ∈ {j | x j}, IPCoefVal r j) = IPRhsVal r

variable {A}

/-- The certificate built on a family of walks: the chosen columns, and the
totals and carries of each row's walk kept only where a walk reads them. -/
def certOfWalks (x : A → Prop) (PS Cy : A → A → A → Prop) :
    zeroOneIPGuessBlock.Assignment A :=
  fun idx => match idx with
    | .x => fun w : Fin 1 → A => x (w 0)
    | .pS => fun w : Fin 3 → A =>
        PS (w 0) (w 1) (w 2) ∧ IPRow (w 0) ∧ IPCol (w 1) ∧ IPPosn (w 2)
    | .cy => fun w : Fin 3 → A =>
        Cy (w 0) (w 1) (w 2) ∧ IPRow (w 0) ∧ IPCol (w 1) ∧ IPPosn (w 2) ∧
          ¬MinPos IPLe IPCol (w 1)

/-- Walks ending on the right-hand sides give a certificate of the counting
kernel. -/
theorem zeroOneIPCert_certOfWalks (hlin : IsLinOrd (IPLe (A := A))) {x : A → Prop}
    {PS Cy : A → A → A → Prop} (hx : ∀ j, x j → IPCol j)
    (hchains : ∀ r : A, IPRow r → IsChain IPLe IPCol IPLe IPPosn x (IPCoef r) (PS r) (Cy r))
    (hfin : ∀ r j p : A, IPRow r → MaxPos IPLe IPCol j → IPPosn p → (PS r j p ↔ IPRhs r p))
    (hemp : (∀ j : A, ¬IPCol j) → ∀ r p : A, IPRow r → IPPosn p → ¬IPRhs r p) :
    ZeroOneIPCert A (certOfWalks x PS Cy) := by
  have hnmin : ∀ {i j : A}, SuccPos IPLe IPCol i j → ¬MinPos IPLe IPCol j := fun hij hmin =>
    hij.2.2.2.1 (hlin.2.2.1 _ _ hij.2.2.1 (hmin.2 _ hij.1))
  refine ⟨hlin, hx, fun r hr => ?_, fun r j p hr hj hp => ?_, hemp, fun r j p h => h.2,
    fun r j p h => h.2⟩
  · exact (hchains r hr).congr (fun j p hj hp => (and_iff_left ⟨hr, hj, hp⟩).symm)
      (fun i j p hij hp => (and_iff_left ⟨hr, hij.2.1, hp, hnmin hij⟩).symm)
  · exact (and_iff_left ⟨hr, hj.1, hp⟩).trans (hfin r j p hr hj hp)

variable [Finite A]

/-- A solution has a certificate. -/
theorem exists_zeroOneIPCert {x : A → Prop} (h : ZeroOneSol A x) :
    ∃ PS Cy : A → A → A → Prop,
      (∀ r : A, IPRow r → IsChain IPLe IPCol IPLe IPPosn x (IPCoef r) (PS r) (Cy r)) ∧
      ZeroOneIPCert A (certOfWalks x PS Cy) := by
  obtain ⟨-, hlin, hx, hsum⟩ := h
  obtain ⟨PS, Cy, hchains, hfin, hemp⟩ := exists_chains_of_zeroOneSol hlin hx hsum
  exact ⟨PS, Cy, hchains, zeroOneIPCert_certOfWalks hlin hx hchains hfin hemp⟩

/-- The chosen columns of a certificate are a solution. -/
theorem zeroOneSol_of_cert {ρ : zeroOneIPGuessBlock.Assignment A} (h : ZeroOneIPCert A ρ) :
    ZeroOneSol A fun j => ρ .x ![j] := by
  obtain ⟨hlin, hx, hchains, hfin, hemp, -, -⟩ := h
  exact ⟨‹Finite A›, hlin, hx, zeroOneSol_of_chains hlin hx hchains hfin hemp⟩

variable (A) in
/-- **The solutions of a 0-1 integer program are the witnesses of the counting
kernel**, bijectively: a solution has exactly one certificate. -/
noncomputable def zeroOneIPEquiv :
    {ρ : zeroOneIPGuessBlock.Assignment A //
        @Sentence.Realize zoSOLang A
          (@sumStructure _ _ A _ (zeroOneIPGuessBlock.structure ρ)) sharpZeroOneIPKernel} ≃
      {x : A → Prop // ZeroOneSol A x} where
  toFun ρ := ⟨fun j => ρ.1 .x ![j],
    zeroOneSol_of_cert ((realize_sharpZeroOneIPKernel ρ.1).mp ρ.2)⟩
  invFun x := ⟨certOfWalks x.1 (exists_zeroOneIPCert x.2).choose
      (exists_zeroOneIPCert x.2).choose_spec.choose,
    (realize_sharpZeroOneIPKernel _).mpr (exists_zeroOneIPCert x.2).choose_spec.choose_spec.2⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hcert := (realize_sharpZeroOneIPKernel ρ).mp hρ
    have hsol := zeroOneSol_of_cert hcert
    obtain ⟨hlin, hx, hchainρ, -, -, hpin₁, hpin₂⟩ := hcert
    have hchain := (exists_zeroOneIPCert hsol).choose_spec.choose_spec.1
    refine Subtype.ext (funext fun idx => ?_)
    cases idx with
    | x =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .x) (funext fun k => by fin_cases k; rfl)
    | pS =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw : ρ .pS ![w 0, w 1, w 2] ↔ ρ .pS w :=
        iff_of_eq (congrArg (ρ .pS) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hr, hj, hp⟩
        exact hw.mp (((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).1 _ _ hj hp).mp h)
      · intro h
        obtain ⟨hr, hj, hp⟩ := hpin₁ _ _ _ (hw.mpr h)
        exact ⟨((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).1 _ _ hj hp).mpr
          (hw.mpr h), hr, hj, hp⟩
    | cy =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw : ρ .cy ![w 0, w 1, w 2] ↔ ρ .cy w :=
        iff_of_eq (congrArg (ρ .cy) (funext fun k => by fin_cases k <;> rfl))
      constructor
      · rintro ⟨h, hr, hj, hp, hnmin⟩
        obtain ⟨i, hi⟩ := exists_predPos hlin hj hnmin
        exact hw.mp
          (((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).2 _ _ _ hi hp).mp h)
      · intro h
        obtain ⟨hr, hj, hp, hnmin⟩ := hpin₂ _ _ _ (hw.mpr h)
        obtain ⟨i, hi⟩ := exists_predPos hlin hj hnmin
        exact ⟨((isChain_agree hlin hlin hx (hchain _ hr) (hchainρ _ hr)).2 _ _ _ hi hp).mpr
          (hw.mpr h), hr, hj, hp, hnmin⟩
  right_inv := fun _ => rfl

end Solutions

/-- **#0-1 integer programming**: the number of `0-1` vectors satisfying every
equation of the program. -/
noncomputable def SharpZeroOneIP : CountingProblem Language.zeroOneIP where
  Count := fun A inst => Nat.card {x : A → Prop // @ZeroOneSol A inst x}
  iso_invariant := fun {A B} _ _ e => by
    by_cases hfin : Finite A
    · have : Finite B := Finite.of_equiv A e.toEquiv
      rw [← Nat.card_congr (zeroOneIPEquiv A), ← Nat.card_congr (zeroOneIPEquiv B)]
      exact witnessCount_iso zeroOneIPGuessBlock sharpZeroOneIPKernel e
    · have hB : ¬Finite B := fun h => hfin (Finite.of_equiv B e.toEquiv.symm)
      have hA0 : IsEmpty {x : A → Prop // ZeroOneSol A x} := ⟨fun x => hfin x.2.1⟩
      have hB0 : IsEmpty {x : B → Prop // ZeroOneSol B x} := ⟨fun x => hB x.2.1⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

theorem sharpZeroOneIP_apply (A : Type) [Language.zeroOneIP.Structure A] :
    SharpZeroOneIP A = Nat.card {x : A → Prop // ZeroOneSol A x} :=
  rfl

/-- **The support of #0-1 integer programming is 0-1 integer programming.**
Registered in the Lax archive as
[`Lax280166.ZeroOneIPComplete.sharpZeroOneIP_support_iff`](https://laxarchive.org/lax-280166/Lax280166.ZeroOneIPComplete.html#s-Lax280166.ZeroOneIPComplete.sharpZeroOneIP_support_iff). -/
theorem sharpZeroOneIP_support_iff (A : Type) [Language.zeroOneIP.Structure A] [Finite A] :
    SharpZeroOneIP.support A ↔ ZeroOneIP A := by
  rw [CountingProblem.support_iff, sharpZeroOneIP_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨x, hfin, hlin, hx, hsum⟩, -⟩
    exact ⟨hfin, hlin, x, hx, hsum⟩
  · rintro ⟨hfin, hlin, x, hx, hsum⟩
    exact ⟨⟨⟨x, hfin, hlin, hx, hsum⟩⟩, inferInstance⟩

/-- **#0-1 integer programming is in `#P`.** -/
theorem sharpZeroOneIP_mem_sharpP : SharpZeroOneIP ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (zeroOneIPEquiv A))
    (sharpPDefinable_ofKernel zeroOneIPGuessBlock sharpZeroOneIPKernel)

end DescriptiveComplexity
