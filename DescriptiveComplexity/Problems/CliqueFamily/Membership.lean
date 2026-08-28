/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.CliqueFamily.Defs
import DescriptiveComplexity.SecondOrder

/-!
# Clique is existential second-order definable

The membership half of the NP-completeness of Clique: the clique threshold
property is `Σ₁`-definable in the sense of `DescriptiveComplexity.SecondOrder`
(`DescriptiveComplexity.clique_sigmaSODefinable`). The single existential block
guesses two relations – a unary one, the clique itself, and a binary one, an
injection of the marked set into the clique – and the first-order kernel
checks that the unary relation is a clique and that the binary relation is
total on the marked set, lands in the clique, and is injective. On (finite)
structures this is equivalent to the existence of an embedding of the marked
set into a clique, i.e., to `DescriptiveComplexity.HasLargeClique`.

Since NP is *defined* as `Σ₁`-definability, this is the statement
`Clique ∈ NP`; see `DescriptiveComplexity.Problems.CliqueFamily` for the
NP-completeness theorems of the whole clique family.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Clique: a unary
relation variable, the clique, and a binary one, an injection of the marked
set into the clique. -/
fo_block cliqueGuessBlock over Language.markedGraph mg into cliqueSOLang with k where
  /-- The guessed clique. -/
  clique : 1
  /-- The guessed injection of the marked set into the clique. -/
  inj : 2

/-- The first-order kernel of the `Σ₁` definition of Clique: the guessed
unary relation is a clique – any two distinct members are adjacent – and the
guessed binary relation maps every marked element to some clique member,
injectively. -/
noncomputable def cliqueKernel : cliqueSOLang.Sentence :=
  fo% (∀ x y, (kCliqueSym(x) ∧ kCliqueSym(y)) ∧ ¬ x ≐ y → kAdjSym(x, y)) ∧
    (∀ x, kMarkedSym(x) → ∃ y, kInjSym(x, y) ∧ kCliqueSym(y)) ∧
    ∀ x x' y, kInjSym(x, y) ∧ kInjSym(x', y) → x ≐ x'

/-- Realization of the kernel under an assignment of the two relation
variables: the guessed set is a clique, and the guessed binary relation maps
every marked element to some member of the set, injectively. -/
private theorem realize_cliqueKernel {A : Type} [Language.markedGraph.Structure A]
    (ρ : cliqueGuessBlock.Assignment A) :
    (@Sentence.Realize cliqueSOLang A
        (@sumStructure _ _ A _ (cliqueGuessBlock.structure ρ)) cliqueKernel) ↔
      (∀ a b : A, ρ .clique ![a] → ρ .clique ![b] → a ≠ b → RelMap mgAdj ![a, b]) ∧
        (∀ a : A, RelMap mgMarked ![a] →
          ∃ b : A, ρ .inj ![a, b] ∧ ρ .clique ![b]) ∧
        ∀ a a' b : A, ρ .inj ![a, b] → ρ .inj ![a', b] → a = a' := by
  let := cliqueGuessBlock.structure ρ
  have hsubC : ∀ (w : Fin 1 → A),
      RelMap (L := cliqueSOLang) (M := A) kCliqueSym w ↔ ρ .clique w :=
    fun _ => Iff.rfl
  have hsubF : ∀ (w : Fin 2 → A),
      RelMap (L := cliqueSOLang) (M := A) kInjSym w ↔ ρ .inj w :=
    fun _ => Iff.rfl
  rw [cliqueKernel]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iExs, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl,
    hsubC, hsubF]
  refine and_congr ⟨fun h a b ha hb hab => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h a ha => ?_, fun h i hi => ?_⟩
      ⟨fun h a a' b hab hab' => ?_, fun h i hi => ?_⟩)
  · exact h ![a, b] ⟨⟨ha, hb⟩, hab⟩
  · exact h (i 0) (i 1) hi.1.1 hi.1.2 hi.2
  · obtain ⟨b, hb1, hb2⟩ := h (fun _ => a) ha
    exact ⟨b 0, hb1, hb2⟩
  · obtain ⟨b, hb1, hb2⟩ := h (i 0) hi
    exact ⟨fun _ => b, hb1, hb2⟩
  · exact h ![a, a', b] ⟨hab, hab'⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2

/-- **Clique is `Σ₁`-definable**: existentially guess the clique and an
injection of the marked set into it, then check both first-order. Since NP is
defined as `Σ₁`-definability, this is the membership half of the
NP-completeness of Clique. -/
theorem clique_sigmaSODefinable : SigmaSODefinable 1 Clique := by
  refine ⟨[cliqueGuessBlock], rfl, cliqueKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hcl⟩
    obtain ⟨S, hS, ⟨e⟩⟩ := (cliqueOn_iff_embedding _ _).mp hcl
    refine ⟨fun i => match i with
      | .clique => fun w : Fin 1 → A => S (w 0)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : RelMap mgMarked ![w 0], (e ⟨w 0, h⟩ : {x // S x}).1 = w 1, ?_⟩
    refine (realize_cliqueKernel _).mpr
      ⟨fun a b ha hb hab => hS a b ha hb hab,
        fun a ha => ⟨(e ⟨a, ha⟩).1, ⟨ha, rfl⟩, (e ⟨a, ha⟩).2⟩, ?_⟩
    rintro a a' b ⟨h, hb⟩ ⟨h', hb'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hb.trans hb'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨h1, h2, h3⟩ := (realize_cliqueKernel ρ).mp hρ
    have hch : ∀ m : {x : A // MGMarked x},
        ∃ b : A, ρ .inj ![m.1, b] ∧ ρ .clique ![b] := fun m => h2 m.1 m.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (cliqueOn_iff_embedding _ _).mpr
      ⟨fun a => ρ .clique ![a], fun x y hx hy hxy => h1 x y hx hy hxy,
        ⟨⟨fun m => ⟨f m, hf2 m⟩, fun m m' hmm' => ?_⟩⟩⟩⟩
    have hval : f m = f m' := congrArg Subtype.val hmm'
    refine Subtype.ext (h3 m.1 m'.1 (f m) (hf1 m) ?_)
    rw [hval]
    exact hf1 m'

end SigmaOne

end DescriptiveComplexity
