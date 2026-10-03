/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.DominatingSet.Defs
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Dominating Set is in NP

The `Σ₁` definition of `Lax799700Proofs.DescriptiveComplexity.DominatingSet`: guess the dominating set
and an injection of it into the marked set, then check first-order that every
vertex is dominated and that the injection is one.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive DominatingGuessBlockIx where
/-- The guessed dominating set. -/

  | set
/-- The guessed injection of the dominating set into the marked set. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.DominatingGuessBlockIx :=
  ⟨List.toFinset [.set, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Dominating Set: the
dominating set (unary) and an injection of it into the marked set (binary). -/
def dominatingGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.DominatingGuessBlockIx
  arity := fun i =>
    match i with
    | .set => 1
    | .inj => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev dsSOLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.dominatingGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev dsAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.dsSOLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev dsMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.dsSOLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `set` relation variable. -/
def dsSetRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.dominatingGuessBlock).Relations 1 :=
  ⟨.set, rfl⟩

/-- The `set` symbol over the sum. -/
abbrev dsSetSym : (_root_.Lax799700Proofs.DescriptiveComplexity.dsSOLang).Relations 1 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.dsSetRel

/-- The `inj` relation variable. -/
def dsInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.dominatingGuessBlock).Relations 2 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev dsInjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.dsSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.dsInjRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- Kernel conjunct: every vertex is in the guessed set or has a neighbor in
it. -/
private noncomputable def dsDomClause : dsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Relations.formula₁ dsSetSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊔
        FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ dsSetSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₂ dsAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))))

/-- Kernel conjunct: the guessed injection maps every vertex of the dominating
set to a marked vertex. -/
private noncomputable def dsTotalClause : dsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ dsSetSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ dsInjSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
              (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₁ dsMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def dsInjClause : dsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₂ dsInjSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
            FirstOrder.Language.Relations.formula₂ dsInjSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- The first-order kernel of the `Σ₁` definition of Dominating Set. -/
noncomputable def dominatingKernel : dsSOLang.Sentence :=
  dsDomClause ⊓ (dsTotalClause ⊓ dsInjClause)

section Realize

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
  (ρ : dominatingGuessBlock.Assignment A)

private theorem realize_dominatingKernel :
    (@Sentence.Realize dsSOLang A
        (@sumStructure _ _ A _ (dominatingGuessBlock.structure ρ)) dominatingKernel) ↔
      (∀ v : A, ρ .set ![v] ∨ ∃ u : A, ρ .set ![u] ∧ Lax799700.CliqueFamily.MGAdj u v) ∧
        (∀ x : A, ρ .set ![x] → ∃ y : A, ρ .inj ![x, y] ∧ Lax799700.CliqueFamily.MGMarked y) ∧
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
theorem dominatingSet_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 DominatingSet := by
  refine ⟨[dominatingGuessBlock], rfl, dominatingKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hds⟩
    obtain ⟨D, hdom, ⟨e⟩⟩ := (dominatesOn_iff_embedding _ _).mp hds
    refine ⟨fun i => match i with
      | .set => fun w : Fin 1 → A => D (w 0)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : D (w 0), (e ⟨w 0, h⟩ : {v // Lax799700.CliqueFamily.MGMarked v}).1 = w 1, ?_⟩
    refine (realize_dominatingKernel _).mpr ⟨hdom,
      fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hdom, htot, hinj⟩ := (realize_dominatingKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ .set ![x]},
        ∃ y : A, ρ .inj ![x.1, y] ∧ Lax799700.CliqueFamily.MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (dominatesOn_iff_embedding _ _).mpr
      ⟨fun v => ρ .set ![v], hdom, ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


