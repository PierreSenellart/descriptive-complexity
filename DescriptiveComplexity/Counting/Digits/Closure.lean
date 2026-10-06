/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Digits.Formulas

/-!
# Numbers computed by a tower

A *family of numbers* (`DescriptiveComplexity.Digits.Fam`) attaches a number
to each tuple of parameters of each ordered structure. Its **digit relation**
(`DescriptiveComplexity.Digits.digRel`) holds of the parameters followed by a
position – an `ℓ`-tuple – when the digit of that position is `1`.

`DescriptiveComplexity.Digits.Dig e₀ ℓ F` says that the digit relation of `F`
can be added to any tower above the induction `e₀`: whatever the induction
extending `e₀`, one more extension computes it. Stating it over *every*
extension is what lets the constructions be chained, each starting from the
tower the previous one left.

This file holds the two ways of adding a relation to a tower – by a formula
(`DescriptiveComplexity.Digits.exists_ext_of_formula`) and by a sweep
(`DescriptiveComplexity.Digits.exists_ext_of_sweep`) – and the first closure
property, under addition (`DescriptiveComplexity.Digits.Dig.add`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Digits

variable {K : Language.{0, 0}}

/-- A family of numbers: one for each tuple of `a` parameters of each ordered
structure. -/
abbrev Fam (K : Language.{0, 0}) (a : ℕ) : Type 1 :=
  ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin a → A) → ℕ

/-- The digit relation of a family of numbers: the parameters, followed by the
positions of the digits `1`. -/
def digRel (ℓ : ℕ) {a : ℕ} (F : Fam K a) :
    ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin (a + ℓ) → A) → Prop :=
  fun A _ _ x => tupBits (F A fun k => x (Fin.castAdd ℓ k)) fun k => x (Fin.natAdd a k)

/-- The structure a stratum above an induction reads: the ordered structure,
expanded by the limit of the induction. -/
abbrev ctxStr (e : StepDef (K.sum Language.order)) (A : Type) [K.Structure A] [LinearOrder A] :
    ((K.sum Language.order).sum e.B.lang).Structure A :=
  e.B.structure₁ (L := K.sum Language.order) (e.inflLimit A)

/-- Vocabulary maps compose into expansions. -/
theorem isExpansionOn_comp {L₁ L₂ L₃ : Language.{0, 0}} (φ : L₁ →ᴸ L₂) (ψ : L₂ →ᴸ L₃)
    (A : Type) [L₁.Structure A] [L₂.Structure A] [L₃.Structure A] [φ.IsExpansionOn A]
    [ψ.IsExpansionOn A] : (ψ.comp φ).IsExpansionOn A where
  map_onFunction := fun f x =>
    (LHom.IsExpansionOn.map_onFunction (ϕ := ψ) (φ.onFunction f) x).trans
      (LHom.IsExpansionOn.map_onFunction f x)
  map_onRelation := fun R x =>
    (LHom.IsExpansionOn.map_onRelation (ϕ := ψ) (φ.onRelation R) x).trans
      (LHom.IsExpansionOn.map_onRelation R x)

/-! ### Reading a relation of the tower -/

section Atoms

variable {e : StepDef (K.sum Language.order)} {ℓ : ℕ} {γ : Type}

/-- An atom of a relation variable of the induction. -/
def ctxAt {r : ℕ} (j : e.B.lang.Relations r) (ts : Fin r → γ) :
    ((K.sum Language.order).sum e.B.lang).Formula γ :=
  Relations.formula (Sum.inr j : ((K.sum Language.order).sum e.B.lang).Relations r)
    fun k => Term.var (ts k)

theorem realize_ctxAt {r : ℕ} {j : e.B.lang.Relations r}
    {R : ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin r → A) → Prop}
    (h : e.Computes j R) (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ts : Fin r → γ) (v : γ → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (ctxAt j ts) v) ↔ R A fun k => v (ts k) := by
  let := e.B.structure (e.inflLimit A)
  exact Formula.realize_rel.trans (h A fun k => v (ts k))

/-- The number computed by a relation variable, at given parameters: a formula
of the position. -/
def numAt {a : ℕ} (j : e.B.lang.Relations (a + ℓ)) (ws : Fin a → γ) :
    ((K.sum Language.order).sum e.B.lang).Formula (γ ⊕ Fin ℓ) :=
  ctxAt j (Fin.append (fun i => Sum.inl (ws i)) Sum.inr)

theorem realize_numAt {a : ℕ} {j : e.B.lang.Relations (a + ℓ)} {F : Fam K a}
    (h : e.Computes j (digRel ℓ F)) (A : Type) [K.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] (ws : Fin a → γ) (g : γ → A) (p : Fin ℓ → A) :
    (@Formula.Realize _ A (ctxStr e A) _ (numAt j ws) (Sum.elim g p)) ↔
      tupBits (F A fun i => g (ws i)) p := by
  refine (realize_ctxAt h A _ _).trans (iff_of_eq ?_)
  simp only [digRel, Fin.append_left, Fin.append_right, Sum.elim_inl, Sum.elim_inr]

end Atoms

/-! ### Adding a relation to a tower -/

section Add

variable (e : StepDef (K.sum Language.order))

/-- **A relation defined by a formula over a tower is computed by an
extension of it.** -/
theorem exists_ext_of_formula {r : ℕ} (ψ : ((K.sum Language.order).sum e.B.lang).Formula (Fin r))
    (R : ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin r → A) → Prop)
    (h : ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (x : Fin r → A),
      (@Formula.Realize _ A (ctxStr e A) _ ψ x) ↔ R A x) :
    ∃ (e' : StepDef (K.sum Language.order)) (_ : e.Ext e') (j : e'.B.lang.Relations r),
      e'.Computes j R := by
  refine ⟨e.stratify (foStratum Unit (fun _ => r) fun _ => ψ), StepDef.Ext.stratify e _,
    ⟨.inr (), rfl⟩, ?_⟩
  intro A _ _ _ _ x
  refine (e.inflLimit_stratify_inr (foStratum Unit (fun _ => r) fun _ => ψ) A () _).trans ?_
  exact (@inflLimit_foStratum _ A (ctxStr e A) Unit _ (fun _ => r) (fun _ => ψ) () x).trans
    (h A x)

/-- **A family of relations defined by formulas over a tower is computed by
an extension of it.** -/
theorem exists_ext_of_family {J : Type} [Finite J] {r : ℕ}
    (ψ : J → ((K.sum Language.order).sum e.B.lang).Formula (Fin r))
    (R : J → ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin r → A) → Prop)
    (h : ∀ (τ : J) (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
      (x : Fin r → A), (@Formula.Realize _ A (ctxStr e A) _ (ψ τ) x) ↔ R τ A x) :
    ∃ (e' : StepDef (K.sum Language.order)) (_ : e.Ext e') (j : J → e'.B.lang.Relations r),
      Function.Injective (fun τ => (j τ).1) ∧ ∀ τ, e'.Computes (j τ) (R τ) := by
  refine ⟨e.stratify (foStratum J (fun _ => r) ψ), StepDef.Ext.stratify e _,
    fun τ => ⟨.inr τ, rfl⟩, fun τ τ' h => Sum.inr.inj h, ?_⟩
  intro τ A _ _ _ _ x
  refine (e.inflLimit_stratify_inr (foStratum J (fun _ => r) ψ) A τ _).trans ?_
  exact (@inflLimit_foStratum _ A (ctxStr e A) J _ (fun _ => r) ψ τ x).trans (h τ A x)

/-- **The digits of a number defined by a formula over a tower are computed
by an extension of it.** -/
theorem exists_ext_of_num {a ℓ : ℕ}
    (ψ : ((K.sum Language.order).sum e.B.lang).Formula (Fin a ⊕ Fin ℓ)) (F : Fam K a)
    (h : ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (w : Fin a → A)
      (p : Fin ℓ → A),
      (@Formula.Realize _ A (ctxStr e A) _ ψ (Sum.elim w p)) ↔ tupBits (F A w) p) :
    ∃ (e' : StepDef (K.sum Language.order)) (_ : e.Ext e')
      (j : e'.B.lang.Relations (a + ℓ)), e'.Computes j (digRel ℓ F) := by
  refine exists_ext_of_formula e (Formula.relabel g2 ψ) (digRel ℓ F) ?_
  intro A _ _ _ _ x
  let := ctxStr e A
  refine Formula.realize_relabel.trans ((iff_of_eq (congrArg _ ?_)).trans
    (h A (fun k => x (Fin.castAdd ℓ k)) fun k => x (Fin.natAdd a k)))
  funext y
  rcases y with k | k <;> rfl

/-- **The rows of a sweep over a tower are computed by an extension of it.** -/
theorem exists_ext_of_sweep {a q ℓ : ℕ}
    (bot : ((K.sum Language.order).sum e.B.lang).Formula (Fin q))
    (cov : ((K.sum Language.order).sum e.B.lang).Formula (Fin q ⊕ Fin q))
    (Θ : (((K.sum Language.order).sum e.B.lang).sum (sweepBlock a q ℓ).lang).Formula
      ((Fin a ⊕ Fin q) ⊕ Fin ℓ))
    (T : ∀ (A : Type) [K.Structure A] [LinearOrder A], (Fin (a + q + ℓ) → A) → Prop)
    (h : ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (w : Fin a → A)
      (i : Fin q → A) (p : Fin ℓ → A),
      @StepDef.inflLimit _ (sweep bot cov Θ) A (ctxStr e A) true (j3 w i p) ↔
        T A (j3 w i p)) :
    ∃ (e' : StepDef (K.sum Language.order)) (_ : e.Ext e')
      (j : e'.B.lang.Relations (a + q + ℓ)), e'.Computes j T := by
  refine ⟨e.stratify (sweep bot cov Θ), StepDef.Ext.stratify e _, ⟨.inr true, rfl⟩, ?_⟩
  intro A _ _ _ _ x
  refine (e.inflLimit_stratify_inr (sweep bot cov Θ) A true _).trans ?_
  obtain ⟨wi, p, rfl⟩ := exists_j2 x
  obtain ⟨w, i, rfl⟩ := exists_j2 wi
  exact h A w i p

end Add

/-! ### Numbers that can be added to any tower -/

section Dig

variable (e₀ : StepDef (K.sum Language.order)) (ℓ : ℕ)

/-- **The digits of the family `F` can be added to any tower above `e₀`.** -/
def Dig {a : ℕ} (F : Fam K a) : Prop :=
  ∀ e : StepDef (K.sum Language.order), e₀.Ext e →
    ∃ (e' : StepDef (K.sum Language.order)) (_ : e.Ext e')
      (j : e'.B.lang.Relations (a + ℓ)), e'.Computes j (digRel ℓ F)

variable {e₀ ℓ}

/-- Families with the same values. -/
theorem Dig.congr {a : ℕ} {F G : Fam K a}
    (h : ∀ (A : Type) [K.Structure A] [LinearOrder A] (w : Fin a → A), F A w = G A w)
    (hF : Dig e₀ ℓ F) : Dig e₀ ℓ G := by
  have : F = G := funext fun A => funext fun _ => funext fun _ => funext fun w => h A w
  exact this ▸ hF

/-- A family defined by a formula of the ordered vocabulary alone. -/
theorem Dig.of_base {a : ℕ} (F : Fam K a)
    (ψ : (K.sum Language.order).Formula (Fin a ⊕ Fin ℓ))
    (h : ∀ (A : Type) [K.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (w : Fin a → A)
      (p : Fin ℓ → A), ψ.Realize (Sum.elim w p) ↔ tupBits (F A w) p) : Dig e₀ ℓ F := by
  intro e _
  refine exists_ext_of_num e (LHom.sumInl.onFormula ψ) F fun A _ _ _ _ w p => ?_
  let := e.B.structure (e.inflLimit A)
  exact (LHom.realize_onFormula
    (LHom.sumInl : K.sum Language.order →ᴸ (K.sum Language.order).sum e.B.lang) ψ).trans
    (h A w p)

/-- The family constantly zero. -/
theorem Dig.zero (a : ℕ) : Dig e₀ ℓ (fun _ _ _ _ => 0 : Fam K a) :=
  Dig.of_base _ ⊥ fun _ _ _ _ _ _ _ => iff_of_false id (bitsOf_zero _)

/-- The family constantly one. -/
theorem Dig.one (a : ℕ) : Dig e₀ ℓ (fun _ _ _ _ => 1 : Fam K a) :=
  Dig.of_base _ (minTupF Sum.inr) fun _ _ _ _ _ w p =>
    ((realize_minTupF (L := K) (v := Sum.elim w p) Sum.inr).trans
      (tup_isBot_iff (t := p)).symm).trans (tupBits_one p).symm

/-- **Closure under addition**: the sum of two numbers is defined by carry
lookahead from their digits. -/
theorem Dig.add {a : ℕ} {F G : Fam K a} (hF : Dig e₀ ℓ F) (hG : Dig e₀ ℓ G) :
    Dig e₀ ℓ (fun A _ _ w => F A w + G A w) := by
  intro e x
  obtain ⟨e₁, y₁, jF, hjF⟩ := hF e x
  obtain ⟨e₂, y₂, jG, hjG⟩ := hG e₁ (x.trans y₁)
  have hjF' := hjF.ext y₂
  obtain ⟨e₃, y₃, j, hj⟩ := exists_ext_of_num e₂
    (addF LHom.sumInl (numAt (y₂.sym jF) id) (numAt jG id)) (fun A _ _ w => F A w + G A w)
    (fun A _ _ _ _ w p => by
      have h1 := fun p' => realize_numAt hjF' A id w p'
      have h2 := fun p' => realize_numAt hjG A id w p'
      let := e₂.B.structure (e₂.inflLimit A)
      refine (realize_addF (K := K) LHom.sumInl _ _ w p).trans ?_
      rw [← addSet_tupBits]
      exact iff_of_eq (congrArg₂ (fun X Y => AddSet X Y p)
        (funext fun p' => propext (h1 p')) (funext fun p' => propext (h2 p'))))
  exact ⟨e₃, (y₁.trans y₂).trans y₃, j, hj⟩

end Dig

end Digits

end DescriptiveComplexity
