/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.MaxCut.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Membership
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.FinCases
import Lax799700Proofs.DescriptiveComplexity.Composition
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Lax799700Proofs.DescriptiveComplexity.OrderedComposition
import Lax799700Proofs.DescriptiveComplexity.Relativized
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.SecondOrderLift
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
# Max Cut is in NP

The `Σ₁` definition of `Lax799700Proofs.DescriptiveComplexity.MaxCut`: guess one side `S` of the cut
and an injection of the marked pairs into the cut, the injection being a
*quaternary* relation variable since it maps pairs to pairs, exactly as for
Feedback Arc Set, and reusing its `Lax799700Proofs.DescriptiveComplexity.realize_rel₄`.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive MaxCutGuessBlockIx where
/-- One side of the cut. -/

  | side
/-- The injection of the marked relation into the cut. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.MaxCutGuessBlockIx :=
  ⟨List.toFinset [.side, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Max Cut: one side
of the cut (unary) and an injection of the marked relation into the cut
(quaternary: it maps pairs to pairs). -/
def maxCutGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.MaxCutGuessBlockIx
  arity := fun i =>
    match i with
    | .side => 1
    | .inj => 4

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev mcSOLang : FirstOrder.Language :=
  (Lax799700.Feedback.markedArcGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.maxCutGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev mcAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.mcSOLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magAdj

/-- The `marked` symbol over the sum. -/
abbrev mcMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.mcSOLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magMarked

/-- The `side` relation variable. -/
def mcSideRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.maxCutGuessBlock).Relations 1 :=
  ⟨.side, rfl⟩

/-- The `side` symbol over the sum. -/
abbrev mcSideSym : (_root_.Lax799700Proofs.DescriptiveComplexity.mcSOLang).Relations 1 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.mcSideRel

/-- The `inj` relation variable. -/
def mcInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.maxCutGuessBlock).Relations 4 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev mcInjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.mcSOLang).Relations 4 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.mcInjRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- Kernel conjunct: the guessed injection maps every marked pair to a pair
crossing the cut. -/
private noncomputable def mcTotalClause : mcSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₂ mcMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1))).imp
        (FirstOrder.Language.Formula.iExs (Fin 2)
          (FirstOrder.Language.Relations.formula mcInjSym
              ![FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)), FirstOrder.Language.Term.var (Sum.inl (Sum.inr 1)),
                FirstOrder.Language.Term.var (Sum.inr 0), FirstOrder.Language.Term.var (Sum.inr 1)] ⊓
            (FirstOrder.Language.Relations.formula₂ mcAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              (FirstOrder.Language.Relations.formula₁ mcSideSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Relations.formula₁ mcSideSym (FirstOrder.Language.Term.var (Sum.inr 1))))))))

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def mcInjClause : mcSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 6)
      ((FirstOrder.Language.Relations.formula mcInjSym
              ![FirstOrder.Language.Term.var (Sum.inr 0), FirstOrder.Language.Term.var (Sum.inr 1),
                FirstOrder.Language.Term.var (Sum.inr 4), FirstOrder.Language.Term.var (Sum.inr 5)] ⊓
            FirstOrder.Language.Relations.formula mcInjSym
              ![FirstOrder.Language.Term.var (Sum.inr 2), FirstOrder.Language.Term.var (Sum.inr 3),
                FirstOrder.Language.Term.var (Sum.inr 4), FirstOrder.Language.Term.var (Sum.inr 5)]).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
          FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 3))))

/-- The first-order kernel of the `Σ₁` definition of Max Cut. -/
noncomputable def maxCutKernel : mcSOLang.Sentence :=
  mcTotalClause ⊓ mcInjClause

/-- Realization of the kernel under an assignment of the two relation
variables. -/
private theorem realize_maxCutKernel {A : Type} [Lax799700.Feedback.markedArcGraph.Structure A]
    (ρ : maxCutGuessBlock.Assignment A) :
    (@Sentence.Realize mcSOLang A
        (@sumStructure _ _ A _ (maxCutGuessBlock.structure ρ)) maxCutKernel) ↔
      (∀ a b : A, Lax799700.Feedback.MAGMarked a b → ∃ c d : A,
          ρ .inj ![a, b, c, d] ∧ Lax799700.Feedback.MAGAdj c d ∧ ρ .side ![c] ∧ ¬ρ .side ![d]) ∧
        ∀ a b a' b' c d : A, ρ .inj ![a, b, c, d] → ρ .inj ![a', b', c, d] →
          a = a' ∧ b = b' := by
  let := maxCutGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := mcSOLang) (M := A) mcSideSym w ↔ ρ .side w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 4 → A),
      RelMap (L := mcSOLang) (M := A) mcInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [maxCutKernel]
  simp only [mcTotalClause, mcInjClause, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs,
    Formula.realize_not, realize_rel₄, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsubS, hsubI]
  refine and_congr ⟨fun h a b hab => ?_, fun h i hi => ?_⟩
    ⟨fun h a b a' b' c d h₁ h₂ => ?_, fun h i hi => ?_⟩
  · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := h ![a, b] hab
    exact ⟨j 0, j 1, hj1, hj2, hj3, hj4⟩
  · obtain ⟨c, d, hc1, hc2, hc3, hc4⟩ := h (i 0) (i 1) hi
    exact ⟨![c, d], hc1, hc2, hc3, hc4⟩
  · exact h ![a, b, a', b', c, d] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) (i 5) hi.1 hi.2

/-- **Max Cut is `Σ₁`-definable**: existentially guess one side of the cut and
an injection of the marked relation into the cut – a *quaternary* relation
variable, the threshold being carried by pairs. Since NP is defined as
`Σ₁`-definability, this is the membership half of the NP-completeness of Max
Cut. -/
theorem maxCut_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 MaxCut := by
  refine ⟨[maxCutGuessBlock], rfl, maxCutKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hmc⟩
    obtain ⟨S, ⟨e⟩⟩ := (maxCutOn_iff_certificate _ _).mp hmc
    refine ⟨fun i => match i with
      | .side => fun w : Fin 1 → A => S (w 0)
      | .inj => fun w : Fin 4 → A =>
          ∃ h : Lax799700.Feedback.MAGMarked (w 0) (w 1),
            (e ⟨(w 0, w 1), h⟩ : {p : A × A // Lax799700.MaxCut.CutRel Lax799700.Feedback.MAGAdj S p.1 p.2}).1 = (w 2, w 3), ?_⟩
    refine (realize_maxCutKernel _).mpr ⟨fun a b hab =>
      ⟨(e ⟨(a, b), hab⟩).1.1, (e ⟨(a, b), hab⟩).1.2, ⟨hab, rfl⟩, (e ⟨(a, b), hab⟩).2.1,
        (e ⟨(a, b), hab⟩).2.2.1, (e ⟨(a, b), hab⟩).2.2.2⟩, ?_⟩
    rintro a b a' b' c d ⟨h, hcd⟩ ⟨h', hcd'⟩
    have heq := e.injective (Subtype.ext (hcd.trans hcd'.symm) :
      (e ⟨(a, b), h⟩ : {p : A × A // Lax799700.MaxCut.CutRel Lax799700.Feedback.MAGAdj S p.1 p.2}) = e ⟨(a', b'), h'⟩)
    exact ⟨congrArg Prod.fst (congrArg Subtype.val heq),
      congrArg Prod.snd (congrArg Subtype.val heq)⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htot, hinj⟩ := (realize_maxCutKernel ρ).mp hρ
    have hch : ∀ p : {p : A × A // Lax799700.Feedback.MAGMarked p.1 p.2},
        ∃ q : A × A, ρ .inj ![p.1.1, p.1.2, q.1, q.2] ∧
          Lax799700.MaxCut.CutRel Lax799700.Feedback.MAGAdj (fun a => ρ .side ![a]) q.1 q.2 := by
      rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨c, d, h₁, h₂, h₃, h₄⟩ := htot a b hab
      exact ⟨(c, d), h₁, h₂, h₃, h₄⟩
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (maxCutOn_iff_certificate _ _).mpr
      ⟨fun a => ρ .side ![a], ⟨⟨fun p => ⟨f p, hf2 p⟩, fun p p' hpp' => ?_⟩⟩⟩⟩
    have hval : f p = f p' := congrArg Subtype.val hpp'
    obtain ⟨h₁, h₂⟩ := hinj p.1.1 p.1.2 p'.1.1 p'.1.2 (f p).1 (f p).2 (hf1 p)
      (by rw [hval]; exact hf1 p')
    exact Subtype.ext (Prod.ext h₁ h₂)

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


