/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.Feedback.Defs
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
# The feedback problems are existential second-order definable

The membership half of the NP-completeness of both feedback problems:
`Lax799700Proofs.DescriptiveComplexity.feedbackVertexSet_sigmaSODefinable` and
`Lax799700Proofs.DescriptiveComplexity.feedbackArcSet_sigmaSODefinable`.

Acyclicity is not first-order, but its certificate is
(`Lax799700Proofs.DescriptiveComplexity.acyclicRel_iff_exists_order`), so both definitions have the
same five-clause shape. A single existential block guesses

* the removed object – a set of vertices for Feedback Vertex Set (arity 1), a
  set of arcs for Feedback Arc Set (arity 2);
* a strict partial order certifying that what survives is acyclic (arity 2);
* an injection of the removed object into the marked set, witnessing the
  threshold – arity 2 for Feedback Vertex Set, where it maps vertices to
  vertices, and **arity 4** for Feedback Arc Set, where it maps pairs to
  pairs, the threshold living one arity up (the unary encoding read at arity
  2, see `Lax799700Proofs.DescriptiveComplexity.nonempty_embedding_iff_ncard_le₂`);

and the kernel checks transitivity, irreflexivity, that every surviving arc
goes forward in the order, and that the injection is total and injective. The
arity-4 atom is the only thing the second definition needs beyond the first,
and it costs nothing beyond `Lax799700Proofs.DescriptiveComplexity.realize_rel₄`
(`Lax799700Proofs.DescriptiveComplexity.Interpretation`), Mathlib's `Formula.realize_rel₁`/`₂` stopping
at arity 2.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FeedbackGuessBlockIx where
/-- The guessed removed set. -/

  | set
/-- The guessed strict partial order certifying acyclicity. -/

  | lt
/-- The guessed injection of the removed set into the marked set. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.FeedbackGuessBlockIx :=
  ⟨List.toFinset [.set, .lt, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Feedback Vertex
Set: the removed set (unary), a strict partial order certifying acyclicity
(binary), and an injection of the removed set into the marked set
(binary). -/
def feedbackGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.FeedbackGuessBlockIx
  arity := fun i =>
    match i with
    | .set => 1
    | .lt => 2
    | .inj => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev fvsSOLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev fAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fvsSOLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev fMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fvsSOLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `set` relation variable. -/
def fSetRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackGuessBlock).Relations 1 :=
  ⟨.set, rfl⟩

/-- The `set` symbol over the sum. -/
abbrev fSetSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fvsSOLang).Relations 1 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fSetRel

/-- The `lt` relation variable. -/
def fLtRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackGuessBlock).Relations 2 :=
  ⟨.lt, rfl⟩

/-- The `lt` symbol over the sum. -/
abbrev fLtSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fvsSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fLtRel

/-- The `inj` relation variable. -/
def fInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackGuessBlock).Relations 2 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev fInjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fvsSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fInjRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def fvsTransClause : fvsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₂ fLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.Relations.formula₂ fLtSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Relations.formula₂ fLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Kernel conjunct: the guessed order is irreflexive. -/
private noncomputable def fvsIrreflClause : fvsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₂ fLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- Kernel conjunct: every surviving arc goes forward in the guessed
order. -/
private noncomputable def fvsArcClause : fvsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₂ fAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ fSetSym (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
            FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Relations.formula₁ fSetSym (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
        (FirstOrder.Language.Relations.formula₂ fLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Kernel conjunct: the guessed injection maps every removed vertex to a
marked element. -/
private noncomputable def fvsTotalClause : fvsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ fSetSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₂ fInjSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
              (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₁ fMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def fvsInjClause : fvsSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₂ fInjSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
            FirstOrder.Language.Relations.formula₂ fInjSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- The first-order kernel of the `Σ₁` definition of Feedback Vertex Set. -/
noncomputable def feedbackKernel : fvsSOLang.Sentence :=
  fvsTransClause ⊓ (fvsIrreflClause ⊓ (fvsArcClause ⊓ (fvsTotalClause ⊓ fvsInjClause)))

/-- Realization of the kernel under an assignment of the three relation
variables. -/
private theorem realize_feedbackKernel {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    (ρ : feedbackGuessBlock.Assignment A) :
    (@Sentence.Realize fvsSOLang A
        (@sumStructure _ _ A _ (feedbackGuessBlock.structure ρ)) feedbackKernel) ↔
      (∀ x y z : A, ρ .lt ![x, y] → ρ .lt ![y, z] → ρ .lt ![x, z]) ∧
        (∀ x : A, ¬ρ .lt ![x, x]) ∧
        (∀ x y : A, Lax799700.CliqueFamily.MGAdj x y → ¬ρ .set ![x] → ¬ρ .set ![y] → ρ .lt ![x, y]) ∧
        (∀ x : A, ρ .set ![x] → ∃ y : A, ρ .inj ![x, y] ∧ Lax799700.CliqueFamily.MGMarked y) ∧
        ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  let := feedbackGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := fvsSOLang) (M := A) fSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hsubL : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fLtSym w ↔ ρ .lt w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [feedbackKernel]
  simp only [fvsTransClause, fvsIrreflClause, fvsArcClause, fvsTotalClause,
    fvsInjClause, Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iExs, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl,
    hsubS, hsubL, hsubI]
  refine and_congr ⟨fun h x y z hxy hyz => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
      (and_congr ⟨fun h x y hadj hx hy => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
          ⟨fun h x x' y hxy hx'y => ?_, fun h i hi => ?_⟩)))
  · exact h ![x, y, z] ⟨hxy, hyz⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2
  · exact h fun _ => x
  · exact h (i 0)
  · exact h ![x, y] ⟨⟨hadj, hx⟩, hy⟩
  · exact h (i 0) (i 1) hi.1.1 hi.1.2 hi.2
  · obtain ⟨y, hy1, hy2⟩ := h (fun _ => x) hx
    exact ⟨y 0, hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨hxy, hx'y⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2

/-- **Feedback Vertex Set is `Σ₁`-definable**: existentially guess the
removed set, a strict partial order certifying that the rest is acyclic, and
an injection of the removed set into the marked set, then check all five
conditions first-order. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of Feedback Vertex Set. -/
theorem feedbackVertexSet_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 FeedbackVertexSet := by
  refine ⟨[feedbackGuessBlock], rfl, feedbackKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hfvs⟩
    obtain ⟨C, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackOn_iff_certificate _ _).mp hfvs
    refine ⟨fun i => match i with
      | .set => fun w : Fin 1 → A => C (w 0)
      | .lt => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : C (w 0), (e ⟨w 0, h⟩ : {x // Lax799700.CliqueFamily.MGMarked x}).1 = w 1, ?_⟩
    refine (realize_feedbackKernel _).mpr
      ⟨htrans, hirr,
        fun x y hadj hx hy => hmono x y ⟨hx, hy, hadj⟩,
        fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htrans, hirr, harc, htot, hinj⟩ := (realize_feedbackKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ .set ![x]},
        ∃ y : A, ρ .inj ![x.1, y] ∧ Lax799700.CliqueFamily.MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (feedbackOn_iff_certificate _ _).mpr
      ⟨fun a => ρ .set ![a],
        ⟨fun x y => ρ .lt ![x, y], htrans, hirr,
          fun a b hab => harc a b hab.2.2 hab.1 hab.2.1⟩,
        ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

/-! ### Feedback Arc Set -/

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive FeedbackArcGuessBlockIx where
/-- The removed set of arcs. -/

  | cut
/-- The strict partial order certifying acyclicity. -/

  | lt
/-- The injection of the removed arcs into the marked relation. -/

  | inj
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.FeedbackArcGuessBlockIx :=
  ⟨List.toFinset [.cut, .lt, .inj], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definition of Feedback Arc Set:
the removed set of arcs (binary), a strict partial order certifying acyclicity
(binary), and an injection of the removed arcs into the marked relation
(quaternary: it maps pairs to pairs). -/
def feedbackArcGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.FeedbackArcGuessBlockIx
  arity := fun i =>
    match i with
    | .cut => 2
    | .lt => 2
    | .inj => 4

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev fasSOLang : FirstOrder.Language :=
  (Lax799700.Feedback.markedArcGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackArcGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev fasAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fasSOLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magAdj

/-- The `marked` symbol over the sum. -/
abbrev fasMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fasSOLang).Relations 2 :=
  Sum.inl Lax799700.Feedback.magMarked

/-- The `cut` relation variable. -/
def fasCutRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackArcGuessBlock).Relations 2 :=
  ⟨.cut, rfl⟩

/-- The `cut` symbol over the sum. -/
abbrev fasCutSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fasSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fasCutRel

/-- The `lt` relation variable. -/
def fasLtRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackArcGuessBlock).Relations 2 :=
  ⟨.lt, rfl⟩

/-- The `lt` symbol over the sum. -/
abbrev fasLtSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fasSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fasLtRel

/-- The `inj` relation variable. -/
def fasInjRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.feedbackArcGuessBlock).Relations 4 :=
  ⟨.inj, rfl⟩

/-- The `inj` symbol over the sum. -/
abbrev fasInjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.fasSOLang).Relations 4 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.fasInjRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section SigmaOne

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def fasTransClause : fasSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₂ fasLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.Relations.formula₂ fasLtSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        (FirstOrder.Language.Relations.formula₂ fasLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- Kernel conjunct: the guessed order is irreflexive. -/
private noncomputable def fasIrreflClause : fasSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.BoundedFormula.not
        (FirstOrder.Language.Relations.formula₂ fasLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- Kernel conjunct: every arc that is not cut goes forward in the guessed
order. -/
private noncomputable def fasArcClause : fasSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₂ fasAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Relations.formula₂ fasCutSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
        (FirstOrder.Language.Relations.formula₂ fasLtSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Kernel conjunct: the guessed injection maps every cut arc to a marked
arc. -/
private noncomputable def fasTotalClause : fasSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₂ fasCutSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1))).imp
        (FirstOrder.Language.Formula.iExs (Fin 2)
          (FirstOrder.Language.Relations.formula fasInjSym
              ![FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)), FirstOrder.Language.Term.var (Sum.inl (Sum.inr 1)),
                FirstOrder.Language.Term.var (Sum.inr 0), FirstOrder.Language.Term.var (Sum.inr 1)] ⊓
            FirstOrder.Language.Relations.formula₂ fasMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)))))

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def fasInjClause : fasSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 6)
      ((FirstOrder.Language.Relations.formula fasInjSym
              ![FirstOrder.Language.Term.var (Sum.inr 0), FirstOrder.Language.Term.var (Sum.inr 1),
                FirstOrder.Language.Term.var (Sum.inr 4), FirstOrder.Language.Term.var (Sum.inr 5)] ⊓
            FirstOrder.Language.Relations.formula fasInjSym
              ![FirstOrder.Language.Term.var (Sum.inr 2), FirstOrder.Language.Term.var (Sum.inr 3),
                FirstOrder.Language.Term.var (Sum.inr 4), FirstOrder.Language.Term.var (Sum.inr 5)]).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
          FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 3))))

/-- The first-order kernel of the `Σ₁` definition of Feedback Arc Set. -/
noncomputable def feedbackArcKernel : fasSOLang.Sentence :=
  fasTransClause ⊓ (fasIrreflClause ⊓ (fasArcClause ⊓ (fasTotalClause ⊓ fasInjClause)))

/-- Realization of the kernel under an assignment of the three relation
variables. -/
private theorem realize_feedbackArcKernel {A : Type} [Lax799700.Feedback.markedArcGraph.Structure A]
    (ρ : feedbackArcGuessBlock.Assignment A) :
    (@Sentence.Realize fasSOLang A
        (@sumStructure _ _ A _ (feedbackArcGuessBlock.structure ρ)) feedbackArcKernel) ↔
      (∀ x y z : A, ρ .lt ![x, y] → ρ .lt ![y, z] → ρ .lt ![x, z]) ∧
        (∀ x : A, ¬ρ .lt ![x, x]) ∧
        (∀ x y : A, Lax799700.Feedback.MAGAdj x y → ¬ρ .cut ![x, y] → ρ .lt ![x, y]) ∧
        (∀ a b : A, ρ .cut ![a, b] →
          ∃ c d : A, ρ .inj ![a, b, c, d] ∧ Lax799700.Feedback.MAGMarked c d) ∧
        ∀ a b a' b' c d : A, ρ .inj ![a, b, c, d] → ρ .inj ![a', b', c, d] →
          a = a' ∧ b = b' := by
  let := feedbackArcGuessBlock.structure ρ
  have hsubC : ∀ (w : Fin 2 → A),
      RelMap (L := fasSOLang) (M := A) fasCutSym w ↔ ρ .cut w := fun _ => Iff.rfl
  have hsubL : ∀ (w : Fin 2 → A),
      RelMap (L := fasSOLang) (M := A) fasLtSym w ↔ ρ .lt w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 4 → A),
      RelMap (L := fasSOLang) (M := A) fasInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [feedbackArcKernel]
  simp only [fasTransClause, fasIrreflClause, fasArcClause, fasTotalClause,
    fasInjClause, Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iExs, Formula.realize_not, realize_rel₄,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Language.relMap_sumInl, hsubC, hsubL, hsubI]
  refine and_congr ⟨fun h x y z hxy hyz => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
      (and_congr ⟨fun h x y hadj hcut => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h a b hab => ?_, fun h i hi => ?_⟩
          ⟨fun h a b a' b' c d h₁ h₂ => ?_, fun h i hi => ?_⟩)))
  · exact h ![x, y, z] ⟨hxy, hyz⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2
  · exact h fun _ => x
  · exact h (i 0)
  · exact h ![x, y] ⟨hadj, hcut⟩
  · exact h (i 0) (i 1) hi.1 hi.2
  · obtain ⟨j, hj1, hj2⟩ := h ![a, b] hab
    exact ⟨j 0, j 1, hj1, hj2⟩
  · obtain ⟨c, d, hc1, hc2⟩ := h (i 0) (i 1) hi
    exact ⟨![c, d], hc1, hc2⟩
  · exact h ![a, b, a', b', c, d] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) (i 5) hi.1 hi.2

/-- **Feedback Arc Set is `Σ₁`-definable**: existentially guess the removed
arcs, a strict partial order certifying that the rest is acyclic, and an
injection of the removed arcs into the marked relation – a *quaternary*
relation variable, the threshold being carried by pairs. Since NP is defined
as `Σ₁`-definability, this is the membership half of the NP-completeness of
Feedback Arc Set. -/
theorem feedbackArcSet_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 FeedbackArcSet := by
  refine ⟨[feedbackArcGuessBlock], rfl, feedbackArcKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hfas⟩
    obtain ⟨F, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackArcOn_iff_certificate _ _).mp hfas
    refine ⟨fun i => match i with
      | .cut => fun w : Fin 2 → A => F (w 0) (w 1)
      | .lt => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | .inj => fun w : Fin 4 → A =>
          ∃ h : F (w 0) (w 1),
            (e ⟨(w 0, w 1), h⟩ : {p : A × A // Lax799700.Feedback.MAGMarked p.1 p.2}).1 = (w 2, w 3), ?_⟩
    refine (realize_feedbackArcKernel _).mpr
      ⟨htrans, hirr, fun x y hadj hcut => hmono x y ⟨hadj, hcut⟩, fun a b hab =>
        ⟨(e ⟨(a, b), hab⟩).1.1, (e ⟨(a, b), hab⟩).1.2, ⟨hab, rfl⟩, (e ⟨(a, b), hab⟩).2⟩, ?_⟩
    rintro a b a' b' c d ⟨h, hcd⟩ ⟨h', hcd'⟩
    have heq := e.injective (Subtype.ext (hcd.trans hcd'.symm) :
      (e ⟨(a, b), h⟩ : {p : A × A // Lax799700.Feedback.MAGMarked p.1 p.2}) = e ⟨(a', b'), h'⟩)
    exact ⟨congrArg Prod.fst (congrArg Subtype.val heq),
      congrArg Prod.snd (congrArg Subtype.val heq)⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htrans, hirr, harc, htot, hinj⟩ := (realize_feedbackArcKernel ρ).mp hρ
    have hch : ∀ p : {p : A × A // ρ .cut ![p.1, p.2]},
        ∃ q : A × A, ρ .inj ![p.1.1, p.1.2, q.1, q.2] ∧ Lax799700.Feedback.MAGMarked q.1 q.2 := by
      rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨c, d, h₁, h₂⟩ := htot a b hab
      exact ⟨(c, d), h₁, h₂⟩
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (feedbackArcOn_iff_certificate _ _).mpr
      ⟨fun a b => ρ .cut ![a, b],
        ⟨fun x y => ρ .lt ![x, y], htrans, hirr,
          fun a b hab => harc a b hab.1 hab.2⟩,
        ⟨⟨fun p => ⟨f p, hf2 p⟩, fun p p' hpp' => ?_⟩⟩⟩⟩
    have hval : f p = f p' := congrArg Subtype.val hpp'
    obtain ⟨h₁, h₂⟩ := hinj p.1.1 p.1.2 p'.1.1 p'.1.2 (f p).1 (f p).2 (hf1 p)
      (by rw [hval]; exact hf1 p')
    exact Subtype.ext (Prod.ext h₁ h₂)

end SigmaOne

end Lax799700Proofs.DescriptiveComplexity


