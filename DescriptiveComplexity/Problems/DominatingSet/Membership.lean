/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
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
fo_block dominatingGuessBlock over Language.markedGraph mg into dsSOLang with ds where
  /-- The guessed dominating set. -/
  set : 1
  /-- The guessed injection of the dominating set into the marked set. -/
  inj : 2

/-- Kernel conjunct: every vertex is in the guessed set or has a neighbor in
it. -/
private noncomputable def dsDomClause : dsSOLang.Sentence :=
  fo% ∀ x, dsSetSym(x) ∨ ∃ u, dsSetSym(u) ∧ dsAdjSym(u, x)

/-- Kernel conjunct: the guessed injection maps every vertex of the dominating
set to a marked vertex. -/
private noncomputable def dsTotalClause : dsSOLang.Sentence :=
  fo% ∀ x, dsSetSym(x) → ∃ y, dsInjSym(x, y) ∧ dsMarkedSym(y)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def dsInjClause : dsSOLang.Sentence :=
  fo% ∀ x x' y, dsInjSym(x, y) ∧ dsInjSym(x', y) → x ≐ x'

/-- The first-order kernel of the `Σ₁` definition of Dominating Set. -/
noncomputable def dominatingKernel : dsSOLang.Sentence :=
  dsDomClause ⊓ (dsTotalClause ⊓ dsInjClause)

section Realize

variable {A : Type} [Language.markedGraph.Structure A]
  (ρ : dominatingGuessBlock.Assignment A)

private theorem realize_dominatingKernel :
    (@Sentence.Realize dsSOLang A
        (@sumStructure _ _ A _ (dominatingGuessBlock.structure ρ)) dominatingKernel) ↔
      (∀ v : A, ρ .set ![v] ∨ ∃ u : A, ρ .set ![u] ∧ MGAdj u v) ∧
        (∀ x : A, ρ .set ![x] → ∃ y : A, ρ .inj ![x, y] ∧ MGMarked y) ∧
        ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  let := dominatingGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := dsSOLang) (M := A) dsSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := dsSOLang) (M := A) dsInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
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
    · exact Or.inr ⟨u 0, hu1, hu2⟩
  · rcases h (i 0) with h' | ⟨u, hu1, hu2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨fun _ => u, hu1, hu2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y 0, hy1, hy2⟩
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
      | .set => fun w : Fin 1 → A => D (w 0)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : D (w 0), (e ⟨w 0, h⟩ : {v // MGMarked v}).1 = w 1, ?_⟩
    refine (realize_dominatingKernel _).mpr ⟨hdom,
      fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hdom, htot, hinj⟩ := (realize_dominatingKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ .set ![x]},
        ∃ y : A, ρ .inj ![x.1, y] ∧ MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (dominatesOn_iff_embedding _ _).mpr
      ⟨fun v => ρ .set ![v], hdom, ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

end SigmaOne

end DescriptiveComplexity
