/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Taut
import DescriptiveComplexity.Problems.Sat.CountingHardness
import DescriptiveComplexity.Counting.Reduction
import DescriptiveComplexity.Numbers.DigitExtract

/-!
# #DNF: counting the models of a DNF formula

The number of models of a formula in disjunctive normal form, on the
vocabulary of SAT read disjunctively as for `DescriptiveComplexity.TAUT`: a model is a set of
variables of the formula making every literal of some term true
(`DescriptiveComplexity.DnfModel`).

Deciding whether a DNF formula has a model is easy – it has one exactly when
some term contains no variable both positively and negatively – so #DNF is
not parsimoniously `#P`-hard unless `P = NP`. It is the first problem of the
catalog that is not parsimoniously complete:

* `DescriptiveComplexity.sharpDnf_mem_sharpP`: the models are the witnesses of
  an existential second-order sentence;
* `DescriptiveComplexity.sharpSat_oneCall_sharpDnf`: by De Morgan's law, the
  assignments that are *not* models of a CNF formula are the models of the DNF
  formula obtained by negating every literal
  (`DescriptiveComplexity.dnfModel_swap_iff`), and there are `2 ^ n`
  assignments of the `n` variables of the formula in all. So
  `#SAT(φ) = 2 ^ n - #DNF(¬φ)`: one call, at the sign swap
  `DescriptiveComplexity.swapSignInterp`, and a subtraction from a power of
  two whose exponent is a definable count;
* `DescriptiveComplexity.sharpDnf_sharpP_oneCallComplete`: #DNF is one-call
  `#P`-complete.

This is the reduction of
[Durand, Hermann, Kolaitis 2005][durand2005subtractive] (Proposition 3.4),
where it is the example of a *strong subtractive* reduction: the difference of
the counts at a tautology and at the negated formula, the models of the second
being among those of the first. So #DNF is also complete under subtractive
reductions, a notion under which `#P` is closed: that stronger statement is
`DescriptiveComplexity.sharpDnf_sharpP_complete`, in
`DescriptiveComplexity.Problems.Sat.CountingDnfSubtractive`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Models of a DNF formula -/

section Models

variable (A : Type) [Language.sat.Structure A]

/-- The set `ν` of true variables is a model of the DNF formula: it makes every
literal of some term true, and consists of variables of the formula. -/
def DnfModel (ν : A → Prop) : Prop :=
  (∃ c : A, RelMap satIsClause ![c] ∧
    ∀ x : A, (RelMap satPosIn ![c, x] → ν x) ∧ (RelMap satNegIn ![c, x] → ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

end Models

/-! ### The kernel -/

section Kernel

open SOBlock

/-- Kernel conjunct: some term has all its literals true. -/
noncomputable def dnfTermKernel : satSOLang.Sentence :=
  fo% ∃ c, kIsClSym(c) ∧ ∀ x, (kPosSym(c, x) → kNuSym(x)) ∧ (kNegSym(c, x) → ¬ kNuSym(x))

/-- The first-order kernel of #DNF: some term is true, and the truth assignment
only holds of variables of the formula. -/
noncomputable def sharpDnfKernel : satSOLang.Sentence :=
  dnfTermKernel ⊓ satVarKernel

/-- Realization of the term conjunct. -/
theorem realize_dnfTermKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) dnfTermKernel) ↔
      ∃ c : A, RelMap satIsClause ![c] ∧
        ∀ x : A, (RelMap satPosIn ![c, x] → (satAssignEquiv A).symm ρ x) ∧
          (RelMap satNegIn ![c, x] → ¬(satAssignEquiv A).symm ρ x) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [dnfTermKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c 0, hc, fun x => h fun _ => x⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨fun _ => c, hc, fun x => h (x 0)⟩

/-- Realization of the kernel of #DNF: the assignment is a model. -/
theorem realize_sharpDnfKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpDnfKernel) ↔
      DnfModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_dnfTermKernel ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpDnfKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

end Kernel

/-! ### The counting problem -/

/-- The number of models of a DNF formula is the number of witnesses of the
kernel of #DNF. -/
theorem card_dnfModel_eq_witnessCount (A : Type) [Language.sat.Structure A] :
    Nat.card {ν : A → Prop // DnfModel A ν} = witnessCount satAssignBlock sharpDnfKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpDnfKernel, Equiv.symm_apply_apply])

/-- **#DNF**: the number of models of a DNF formula. -/
noncomputable def SharpDNF : CountingProblem Language.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @DnfModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_dnfModel_eq_witnessCount A, card_dnfModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpDnfKernel e

theorem sharpDnf_apply (A : Type) [Language.sat.Structure A] :
    SharpDNF A = Nat.card {ν : A → Prop // DnfModel A ν} :=
  rfl

/-- **#DNF is in `#P`**: the models of a DNF formula are the witnesses of an
existential second-order sentence. -/
theorem sharpDnf_mem_sharpP : SharpDNF ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_dnfModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpDnfKernel)

/-! ### De Morgan: the non-models of a CNF formula -/

section DeMorgan

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

/-- **De Morgan's law, for models**: the models of the DNF formula `B`, the
sign swap of the CNF formula `A`, are the sets of variables of `A` that are not
models of `A`. -/
theorem dnfModel_swap_iff (e : A ≃ B)
    (hcl : ∀ c : A, RelMap satIsClause ![c] ↔ RelMap satIsClause ![e c])
    (hpos : ∀ c x : A, RelMap satPosIn ![c, x] ↔ RelMap satNegIn ![e c, e x])
    (hneg : ∀ c x : A, RelMap satNegIn ![c, x] ↔ RelMap satPosIn ![e c, e x])
    (ν : A → Prop) :
    DnfModel B (fun b => ν (e.symm b)) ↔ (∀ x, ν x → SatOccurs A x) ∧ ¬SatModel A ν := by
  have hocc : ∀ x : A, SatOccurs B (e x) ↔ SatOccurs A x := by
    intro x
    constructor
    · rintro ⟨d, hd, h⟩
      refine ⟨e.symm d, (hcl _).mpr (by simpa using hd), ?_⟩
      rcases h with h | h
      · exact Or.inr ((hneg (e.symm d) x).mpr (by simpa using h))
      · exact Or.inl ((hpos (e.symm d) x).mpr (by simpa using h))
    · rintro ⟨c, hc, h⟩
      exact ⟨e c, (hcl c).mp hc, h.symm.imp (hneg c x).mp (hpos c x).mp⟩
  constructor
  · rintro ⟨⟨d, hd, hall⟩, hsub⟩
    refine ⟨fun x hx => (hocc x).mp (hsub (e x) (by simpa using hx)), fun hm => ?_⟩
    obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := hm.1 (e.symm d) ((hcl _).mpr (by simpa using hd))
    · have h1 : RelMap satNegIn ![d, e x] := by simpa using (hpos (e.symm d) x).mp hp
      exact (hall (e x)).2 h1 (by simpa using hx)
    · have h1 : RelMap satPosIn ![d, e x] := by simpa using (hneg (e.symm d) x).mp hn
      exact hx (by simpa using (hall (e x)).1 h1)
  · rintro ⟨hsub, hnm⟩
    have hno : ¬∀ c : A, RelMap satIsClause ![c] →
        ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x) :=
      fun h => hnm ⟨h, hsub⟩
    obtain ⟨c, hc⟩ := not_forall.mp hno
    obtain ⟨hc, hx⟩ := Classical.not_imp.mp hc
    have hx' := not_exists.mp hx
    refine ⟨⟨e c, (hcl c).mp hc, fun y => ⟨fun hp => ?_, fun hn hy => ?_⟩⟩, fun y hy => ?_⟩
    · have h1 : RelMap satNegIn ![c, e.symm y] := (hneg c (e.symm y)).mpr (by simpa using hp)
      by_contra hy
      exact hx' (e.symm y) (Or.inr ⟨h1, hy⟩)
    · have h1 : RelMap satPosIn ![c, e.symm y] := (hpos c (e.symm y)).mpr (by simpa using hn)
      exact hx' (e.symm y) (Or.inl ⟨h1, hy⟩)
    · simpa using (hocc (e.symm y)).mpr (hsub _ hy)

/-- **Models and non-models share out the assignments**: a CNF formula with
`n` variables and its sign swap, read as a DNF formula, have `2 ^ n` models
between them. -/
theorem sharpSat_add_sharpDnf [Finite A] (e : A ≃ B)
    (hcl : ∀ c : A, RelMap satIsClause ![c] ↔ RelMap satIsClause ![e c])
    (hpos : ∀ c x : A, RelMap satPosIn ![c, x] ↔ RelMap satNegIn ![e c, e x])
    (hneg : ∀ c x : A, RelMap satNegIn ![c, x] ↔ RelMap satPosIn ![e c, e x]) :
    SharpSAT A + SharpDNF B = 2 ^ Nat.card {x : A // SatOccurs A x} := by
  classical
  have h2 : SharpDNF B =
      Nat.card {ν : A → Prop // (∀ x, ν x → SatOccurs A x) ∧ ¬SatModel A ν} := by
    exact (Nat.card_congr (Equiv.subtypeEquiv
      { toFun := fun ν b => ν (e.symm b)
        invFun := fun μ a => μ (e a)
        left_inv := fun ν => funext fun a => by simp
        right_inv := fun μ => funext fun b => by simp }
      fun ν => (dnfModel_swap_iff e hcl hpos hneg ν).symm)).symm
  have h3 : {ν : A → Prop // SatModel A ν} ⊕
      {ν : A → Prop // (∀ x, ν x → SatOccurs A x) ∧ ¬SatModel A ν} ≃
        {ν : A → Prop // ∀ x, ν x → SatOccurs A x} :=
    { toFun := Sum.elim (fun ν => ⟨ν.1, ν.2.2⟩) fun ν => ⟨ν.1, ν.2.1⟩
      invFun := fun ν =>
        if h : SatModel A ν.1 then Sum.inl ⟨ν.1, h⟩ else Sum.inr ⟨ν.1, ν.2, h⟩
      left_inv := by
        rintro (⟨ν, h⟩ | ⟨ν, h1, h2⟩)
        · simp [h]
        · simp [h2]
      right_inv := fun ν => by
        by_cases h : SatModel A ν.1 <;> simp [h] }
  rw [← card_subsets_eq_two_pow, ← Nat.card_congr h3, Nat.card_sum, h2, sharpSat_apply]

end DeMorgan

/-! ### The reduction -/

/-- “`x` is a variable of the formula”: it occurs in some clause. -/
noncomputable def satOccursAt {α : Type} (x : α) : Language.sat.Formula α :=
  fo%[x] ∃ c, satIsClause(c) ∧ (satPosIn(c, x) ∨ satNegIn(c, x))

theorem realize_satOccursAt {α : Type} (A : Type) [Language.sat.Structure A] (x : α)
    (v : α → A) : (satOccursAt x).Realize v ↔ SatOccurs A (v x) := by
  rw [satOccursAt]
  simp only [SatOccurs, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c 0, hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨fun _ => c, hc, h⟩

/-- “`x` is a variable of the formula”, over the ordered expansion. -/
noncomputable def satOccursFormula : (Language.sat.sum Language.order).Formula (Fin 1) :=
  LHom.sumInl.onFormula (satOccursAt (0 : Fin 1))

theorem realize_satOccursFormula (A : Type) [Language.sat.Structure A] [LinearOrder A]
    (a : A) : satOccursFormula.Realize (fun _ => a) ↔ SatOccurs A a := by
  rw [satOccursFormula, LHom.realize_onFormula, satOccursAt]
  simp only [SatOccurs, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c 0, hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨fun _ => c, hc, h⟩

/-- **#SAT reduces to #DNF with one call**: `#SAT(φ) = 2 ^ n - #DNF(¬φ)`, for
`n` the number of variables of `φ`. -/
noncomputable def sharpSat_oneCall_sharpDnf : SharpSAT ≤ᶜ[≤] SharpDNF :=
  (SharpDNF.pullbackReduction swapSignInterp).toOneCall.ofPost
    (.sub (.pow2 (.count satOccursFormula)) .oracle) fun A _ _ _ _ => by
      have h := sharpSat_add_sharpDnf (swapSignInterp.mapEquivSelf A).symm
        (fun c => (swapSign_isClause (A := A) fun _ => c).symm)
        (fun c x => (swapSign_negIn (A := A) (fun _ => c) fun _ => x).symm)
        fun c x => (swapSign_posIn (A := A) (fun _ => c) fun _ => x).symm
      have hc : (PolyTerm.count satOccursFormula).eval A =
          Nat.card {x : A // SatOccurs A x} := by
        rw [PolyTerm.eval_count_one]
        exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun a =>
          realize_satOccursFormula A a)
      change SharpSAT A = 2 ^ (PolyTerm.count satOccursFormula).eval A -
        SharpDNF (swapSignInterp.Map A)
      rw [hc, ← h]
      omega

/-- **#DNF is one-call `#P`-hard.** -/
theorem sharpDnf_sharpP_oneCallHard : SharpP.OneCallHard SharpDNF :=
  CountingClass.OneCallHard.of_oneCall sharpSat_oneCall_sharpDnf
    (oneCallHard_sharpP_of_parsimoniousHard sharpSat_sharpP_parsimoniousHard)

/-- **#DNF is one-call `#P`-complete**
([Durand, Hermann, Kolaitis 2005][durand2005subtractive]): in `#P`, and every
problem of `#P` reduces to it with one call. -/
theorem sharpDnf_sharpP_oneCallComplete : SharpP.OneCallComplete SharpDNF :=
  .of_mem sharpDnf_mem_sharpP sharpDnf_sharpP_oneCallHard

end DescriptiveComplexity
