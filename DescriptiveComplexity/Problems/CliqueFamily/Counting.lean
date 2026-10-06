/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Membership
import DescriptiveComplexity.Counting.Sized
import DescriptiveComplexity.Counting.Class

/-!
# #Clique: counting the cliques of the threshold size

The counting version of `DescriptiveComplexity.Clique`: the number of cliques having
*exactly* as many vertices as the marked set (`DescriptiveComplexity.CliqueOfSize`).
Its support is Clique, a clique at least as large as the threshold containing
one of exactly that size.

Membership in `#P` (`DescriptiveComplexity.sharpClique_mem_sharpP`) is the first in the
catalog whose kernel reads the order of the instance. The `Σ₁` definition of
Clique certifies the threshold by an injection of the marked set into the
clique, and a clique has many; even for the exact size, a bijection is one
among `k!`. The counting kernel asks for the *monotone* one, which exists and
is unique on a finite linear order. That argument is generic
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), and what this file supplies is
the order-free part: a set is a clique (`DescriptiveComplexity.cliqueSelKernel`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Language.markedGraph.Structure A]

/-- The set `S` is a clique with exactly as many vertices as the marked set, in
a finite marked graph. -/
def CliqueOfSize (S : A → Prop) : Prop :=
  Finite A ∧ (∀ x y, S x → S y → x ≠ y → MGAdj x y) ∧
    {x | S x}.ncard = {x : A | MGMarked x}.ncard

variable {A} {B : Type} [Language.markedGraph.Structure B]

/-- Cliques of the threshold size transport along an isomorphism. -/
theorem CliqueOfSize.map (e : A ≃[Language.markedGraph] B) {S : A → Prop}
    (h : CliqueOfSize A S) : CliqueOfSize B fun b => S (e.toEquiv.symm b) := by
  obtain ⟨hfin, hcl, hcard⟩ := h
  refine ⟨Finite.of_equiv A e.toEquiv, fun x y hx hy hxy => ?_, ?_⟩
  · have h' := (relMap_equiv₂ e mgAdj (e.toEquiv.symm x) (e.toEquiv.symm y)).mp
      (hcl _ _ hx hy fun h => hxy (e.toEquiv.symm.injective h))
    have hx' : e (e.toEquiv.symm x) = x := e.toEquiv.apply_symm_apply x
    have hy' : e (e.toEquiv.symm y) = y := e.toEquiv.apply_symm_apply y
    rw [hx', hy'] at h'
    exact h'
  · exact ((ncard_setOf_symm e.toEquiv S).symm.trans hcard).trans
      (ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e mgMarked a)

end Solutions

/-! ### The order-free kernel -/

/-- The block of the counting definition of Clique: the clique itself. Its
size is certified generically, by `DescriptiveComplexity.sharpPDefinable_of_sized_set`. -/
fo_block cliqueSelBlock over Language.markedGraph mg into cliqueSelLang with cs where
  /-- The clique. -/
  sel : 1

instance : Subsingleton cliqueSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Clique: the guessed set is a clique. -/
noncomputable def cliqueSelKernel : cliqueSelLang.Sentence :=
  fo% ∀ x y, (csSelSym(x) ∧ csSelSym(y)) ∧ ¬ x ≐ y → csAdjSym(x, y)

/-- Realization of the order-free kernel of #Clique. -/
theorem realize_cliqueSelKernel {A : Type} [Language.markedGraph.Structure A]
    (ρ : cliqueSelBlock.Assignment A) :
    (@Sentence.Realize cliqueSelLang A
        (@sumStructure _ _ A _ (cliqueSelBlock.structure ρ)) cliqueSelKernel) ↔
      ∀ a b : A, (ρ .sel fun _ => a) → (ρ .sel fun _ => b) → a ≠ b → MGAdj a b := by
  let := cliqueSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := cliqueSelLang) (M := A) csSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [cliqueSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  exact ⟨fun h a b ha hb hab => h ![a, b] ⟨⟨ha, hb⟩, hab⟩,
    fun h i hi => h (i 0) (i 1) hi.1.1 hi.1.2 hi.2⟩

/-! ### The counting problem -/

/-- **#Clique**: the number of cliques with exactly as many vertices as the
marked set. -/
noncomputable def SharpClique : CountingProblem Language.markedGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @CliqueOfSize A inst S}
  iso_invariant := fun {A B} _ _ e => by
    refine Nat.card_congr
      { toFun := fun S => ⟨fun b => S.1 (e.toEquiv.symm b), S.2.map e⟩
        invFun := fun T => ⟨fun a => T.1 (e.toEquiv a), ?_⟩
        left_inv := fun S => Subtype.ext (funext fun a => by simp)
        right_inv := fun T => Subtype.ext (funext fun b => by simp) }
    have h := T.2.map e.symm
    exact h

theorem sharpClique_apply (A : Type) [Language.markedGraph.Structure A] :
    SharpClique A = Nat.card {S : A → Prop // CliqueOfSize A S} :=
  rfl

/-- **The support of #Clique is Clique**: a clique at least as large as the
marked set contains one of exactly that size. -/
theorem sharpClique_support_iff (A : Type) [Language.markedGraph.Structure A] [Finite A] :
    SharpClique.support A ↔ Clique A := by
  rw [CountingProblem.support_iff, sharpClique_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨S, hfin, hS, hcard⟩, -⟩
    exact ⟨hfin, S, hS, hcard.ge⟩
  · rintro ⟨hfin, S, hS, hcard⟩
    obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq hcard
    exact ⟨⟨⟨fun x => x ∈ T, hfin, fun x y hx hy hxy => hS x y (hTS hx) (hTS hy) hxy, hT⟩⟩,
      inferInstance⟩

/-- **#Clique is in `#P`**: a clique of the threshold size has exactly one
monotone bijection with the marked set. -/
theorem sharpClique_mem_sharpP : SharpClique ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpClique cliqueSelBlock mgMarked .sel rfl cliqueSelKernel
    (fun A _ S => ∀ a b : A, S a → S b → a ≠ b → MGAdj a b)
    (fun _ _ ρ => realize_cliqueSelKernel ρ)
    fun _ _ hfin => Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)

end DescriptiveComplexity
