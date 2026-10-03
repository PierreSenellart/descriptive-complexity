/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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
# Clique is existential second-order definable

The membership half of the NP-completeness of Clique: the clique threshold
property is `Σ₁`-definable in the sense of `Lax799700Proofs.DescriptiveComplexity.SecondOrder`
(`Lax799700Proofs.DescriptiveComplexity.clique_sigmaSODefinable`). The single existential block
guesses two relations – a unary one, the clique itself, and a binary one, an
injection of the marked set into the clique – and the first-order kernel
checks that the unary relation is a clique and that the binary relation is
total on the marked set, lands in the clique, and is injective. On (finite)
structures this is equivalent to the existence of an embedding of the marked
set into a clique, i.e., to `Lax799700Proofs.DescriptiveComplexity.HasLargeClique`.

Since NP is *defined* as `Σ₁`-definability, this is the statement
`Clique ∈ NP`; see `Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily` for the
NP-completeness theorems of the whole clique family.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive CliqueGuessBlockIx where
/-- The guessed clique. -/

  | clique
/-- The guessed injection of the marked set into the clique. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.CliqueGuessBlockIx :=
  ⟨List.toFinset [.clique, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Clique: a unary
relation variable, the clique, and a binary one, an injection of the marked
set into the clique. -/
def cliqueGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.CliqueGuessBlockIx
  arity := fun i =>
    match i with
    | .clique => 1
    | .inj => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev cliqueSOLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.cliqueGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev kAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.cliqueSOLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev kMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.cliqueSOLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `clique` relation variable. -/
def kCliqueRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.cliqueGuessBlock).Relations 1 :=
  ⟨.clique, rfl⟩

/-- The `clique` symbol over the sum. -/
abbrev kCliqueSym : (_root_.Lax799700Proofs.DescriptiveComplexity.cliqueSOLang).Relations 1 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.kCliqueRel

/-- The `inj` relation variable. -/
def kInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.cliqueGuessBlock).Relations 2 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev kInjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.cliqueSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.kInjRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- The first-order kernel of the `Σ₁` definition of Clique: the guessed
unary relation is a clique – any two distinct members are adjacent – and the
guessed binary relation maps every marked element to some clique member,
injectively. -/
noncomputable def cliqueKernel : cliqueSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₁ kCliqueSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₁ kCliqueSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
          (FirstOrder.Language.Relations.formula₂ kAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1)))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 1)
          ((FirstOrder.Language.Relations.formula₁ kMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
            (FirstOrder.Language.Formula.iExs (Fin 1)
              (FirstOrder.Language.Relations.formula₂ kInjSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                  (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₁ kCliqueSym (FirstOrder.Language.Term.var (Sum.inr 0))))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 3)
          ((FirstOrder.Language.Relations.formula₂ kInjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
                FirstOrder.Language.Relations.formula₂ kInjSym (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 2))).imp
            (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)))))

/-- Realization of the kernel under an assignment of the two relation
variables: the guessed set is a clique, and the guessed binary relation maps
every marked element to some member of the set, injectively. -/
private theorem realize_cliqueKernel {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    (ρ : cliqueGuessBlock.Assignment A) :
    (@Sentence.Realize cliqueSOLang A
        (@sumStructure _ _ A _ (cliqueGuessBlock.structure ρ)) cliqueKernel) ↔
      (∀ a b : A, ρ .clique ![a] → ρ .clique ![b] → a ≠ b → RelMap Lax799700.CliqueFamily.mgAdj ![a, b]) ∧
        (∀ a : A, RelMap Lax799700.CliqueFamily.mgMarked ![a] →
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
theorem clique_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 Clique := by
  refine ⟨[cliqueGuessBlock], rfl, cliqueKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hcl⟩
    obtain ⟨S, hS, ⟨e⟩⟩ := (cliqueOn_iff_embedding _ _).mp hcl
    refine ⟨fun i => match i with
      | .clique => fun w : Fin 1 → A => S (w 0)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : RelMap Lax799700.CliqueFamily.mgMarked ![w 0], (e ⟨w 0, h⟩ : {x // S x}).1 = w 1, ?_⟩
    refine (realize_cliqueKernel _).mpr
      ⟨fun a b ha hb hab => hS a b ha hb hab,
        fun a ha => ⟨(e ⟨a, ha⟩).1, ⟨ha, rfl⟩, (e ⟨a, ha⟩).2⟩, ?_⟩
    rintro a a' b ⟨h, hb⟩ ⟨h', hb'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hb.trans hb'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨h1, h2, h3⟩ := (realize_cliqueKernel ρ).mp hρ
    have hch : ∀ m : {x : A // Lax799700.CliqueFamily.MGMarked x},
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

end Lax799700Proofs.DescriptiveComplexity


