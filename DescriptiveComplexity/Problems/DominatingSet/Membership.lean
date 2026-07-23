/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.DominatingSet.Defs
import DescriptiveComplexity.SecondOrder

/-!
# Dominating Set is in NP

The `Σ₁` definition of `DescriptiveComplexity.DominatingSet`: guess the dominating set
and an injection of it into the marked set, then check first-order that every
vertex is dominated and that the injection is one.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Dominating Set: the
dominating set (unary) and an injection of it into the marked set (binary). -/
def dominatingGuessBlock : SOBlock where
  ι := Bool
  arity := fun i => cond i 2 1

/-- The symbol of the dominating-set relation variable. -/
def dsSetRel : dominatingGuessBlock.lang.Relations 1 := ⟨false, rfl⟩

/-- The symbol of the injection relation variable. -/
def dsInjRel : dominatingGuessBlock.lang.Relations 2 := ⟨true, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev dsSOLang : Language := Language.markedGraph.sum dominatingGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev dsAdjSym : dsSOLang.Relations 2 := Sum.inl mgAdj

/-- The mark symbol in the kernel's vocabulary. -/
abbrev dsMarkedSym : dsSOLang.Relations 1 := Sum.inl mgMarked

/-- The dominating-set symbol in the kernel's vocabulary. -/
abbrev dsSetSym : dsSOLang.Relations 1 := Sum.inr dsSetRel

/-- The injection symbol in the kernel's vocabulary. -/
abbrev dsInjSym : dsSOLang.Relations 2 := Sum.inr dsInjRel

/-- Kernel conjunct: every vertex is in the guessed set or has a neighbour in
it. -/
private noncomputable def dsDomClause : dsSOLang.Sentence :=
  (Relations.formula₁ dsSetSym (Term.var (Sum.inr 0)) ⊔
    (Relations.formula₁ dsSetSym (Term.var (Sum.inr ())) ⊓
      Relations.formula₂ dsAdjSym (Term.var (Sum.inr ()))
        (Term.var (Sum.inl (Sum.inr 0)))).iExs Unit).iAlls (Fin 1)

/-- Kernel conjunct: the guessed injection maps every vertex of the dominating
set to a marked vertex. -/
private noncomputable def dsTotalClause : dsSOLang.Sentence :=
  ((Relations.formula₁ dsSetSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ dsInjSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ())) ⊓
      Relations.formula₁ dsMarkedSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def dsInjClause : dsSOLang.Sentence :=
  ((Relations.formula₂ dsInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ dsInjSym (Term.var (Sum.inr 1))
        (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The first-order kernel of the `Σ₁` definition of Dominating Set. -/
noncomputable def dominatingKernel : dsSOLang.Sentence :=
  dsDomClause ⊓ (dsTotalClause ⊓ dsInjClause)

section Realize

variable {A : Type} [Language.markedGraph.Structure A]
  (ρ : dominatingGuessBlock.Assignment A)

private theorem realize_dominatingKernel :
    (@Sentence.Realize dsSOLang A
        (@sumStructure _ _ A _ (dominatingGuessBlock.structure ρ)) dominatingKernel) ↔
      (∀ v : A, ρ false ![v] ∨ ∃ u : A, ρ false ![u] ∧ MGAdj u v) ∧
        (∀ x : A, ρ false ![x] → ∃ y : A, ρ true ![x, y] ∧ MGMarked y) ∧
        ∀ x x' y : A, ρ true ![x, y] → ρ true ![x', y] → x = x' := by
  letI := dominatingGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := dsSOLang) (M := A) dsSetSym w ↔ ρ false w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := dsSOLang) (M := A) dsInjSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [dominatingKernel]
  simp only [dsDomClause, dsTotalClause, dsInjClause, Sentence.Realize,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsubS, hsubI]
  refine and_congr ⟨fun h v => ?_, fun h i => ?_⟩
    (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
      ⟨fun h x x' y h₁ h₂ => ?_, fun h i hi => ?_⟩)
  · rcases h (fun _ => v) with h' | ⟨u, hu1, hu2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨u (), hu1, hu2⟩
  · rcases h (i 0) with h' | ⟨u, hu1, hu2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨fun _ => u, hu1, hu2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y (), hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2

end Realize

/-- **Dominating Set is `Σ₁`-definable**: existentially guess the dominating
set and an injection of it into the marked set, then check both first-order.
Since NP is defined as `Σ₁`-definability, this is the membership half of the
NP-completeness of Dominating Set. -/
theorem dominatingSet_sigmaSODefinable : SigmaSODefinable 1 DominatingSet := by
  refine ⟨[dominatingGuessBlock], rfl, dominatingKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hds⟩
    obtain ⟨D, hdom, ⟨e⟩⟩ := (dominatesOn_iff_embedding _ _).mp hds
    refine ⟨fun i => match i with
      | false => fun w : Fin 1 → A => D (w 0)
      | true => fun w : Fin 2 → A =>
          ∃ h : D (w 0), (e ⟨w 0, h⟩ : {v // MGMarked v}).1 = w 1, ?_⟩
    refine (realize_dominatingKernel _).mpr ⟨hdom,
      fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hdom, htot, hinj⟩ := (realize_dominatingKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ false ![x]},
        ∃ y : A, ρ true ![x.1, y] ∧ MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (dominatesOn_iff_embedding _ _).mpr
      ⟨fun v => ρ false ![v], hdom, ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

end SigmaOne

end DescriptiveComplexity
