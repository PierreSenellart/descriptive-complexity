/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MaxCut.Defs
import DescriptiveComplexity.Problems.Feedback.Membership
import DescriptiveComplexity.Hierarchy

/-!
# Max Cut is in NP

The `Σ₁` definition of `DescriptiveComplexity.MaxCut`: guess one side `S` of the cut
and an injection of the marked pairs into the cut, the injection being a
*quaternary* relation variable since it maps pairs to pairs, exactly as for
Feedback Arc Set (whose `DescriptiveComplexity.realize_rel₄` this file reuses).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Max Cut: one side
of the cut (unary) and an injection of the marked relation into the cut
(quaternary: it maps pairs to pairs). -/
def maxCutGuessBlock : SOBlock where
  ι := Bool
  arity := fun i => match i with
    | false => 1
    | true => 4

/-- The symbol of the relation variable holding one side of the cut. -/
def mcSideRel : maxCutGuessBlock.lang.Relations 1 := ⟨false, rfl⟩

/-- The symbol of the injection relation variable. -/
def mcInjRel : maxCutGuessBlock.lang.Relations 4 := ⟨true, rfl⟩

/-- The vocabulary of the kernel: arc-marked graphs together with the two
guessed relation variables. -/
abbrev mcSOLang : Language := Language.markedArcGraph.sum maxCutGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev mcAdjSym : mcSOLang.Relations 2 := Sum.inl magAdj

/-- The mark symbol in the kernel's vocabulary. -/
abbrev mcMarkedSym : mcSOLang.Relations 2 := Sum.inl magMarked

/-- The cut-side symbol in the kernel's vocabulary. -/
abbrev mcSideSym : mcSOLang.Relations 1 := Sum.inr mcSideRel

/-- The injection symbol in the kernel's vocabulary. -/
abbrev mcInjSym : mcSOLang.Relations 4 := Sum.inr mcInjRel

/-- Kernel conjunct: the guessed injection maps every marked pair to a pair
crossing the cut. -/
private noncomputable def mcTotalClause : mcSOLang.Sentence :=
  ((Relations.formula₂ mcMarkedSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    ((Relations.formula mcInjSym ![Term.var (Sum.inl (Sum.inr 0)),
          Term.var (Sum.inl (Sum.inr 1)), Term.var (Sum.inr 0), Term.var (Sum.inr 1)] ⊓
      (Relations.formula₂ mcAdjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
        (Relations.formula₁ mcSideSym (Term.var (Sum.inr 0)) ⊓
          ∼(Relations.formula₁ mcSideSym (Term.var (Sum.inr 1)))))).iExs
      (Fin 2))).iAlls (Fin 2)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def mcInjClause : mcSOLang.Sentence :=
  ((Relations.formula mcInjSym ![Term.var (Sum.inr 0), Term.var (Sum.inr 1),
        Term.var (Sum.inr 4), Term.var (Sum.inr 5)] ⊓
      Relations.formula mcInjSym ![Term.var (Sum.inr 2), Term.var (Sum.inr 3),
        Term.var (Sum.inr 4), Term.var (Sum.inr 5)]).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3)))).iAlls (Fin 6)

/-- The first-order kernel of the `Σ₁` definition of Max Cut. -/
noncomputable def maxCutKernel : mcSOLang.Sentence :=
  mcTotalClause ⊓ mcInjClause

/-- Realization of the kernel under an assignment of the two relation
variables. -/
private theorem realize_maxCutKernel {A : Type} [Language.markedArcGraph.Structure A]
    (ρ : maxCutGuessBlock.Assignment A) :
    (@Sentence.Realize mcSOLang A
        (@sumStructure _ _ A _ (maxCutGuessBlock.structure ρ)) maxCutKernel) ↔
      (∀ a b : A, MAGMarked a b → ∃ c d : A,
          ρ true ![a, b, c, d] ∧ MAGAdj c d ∧ ρ false ![c] ∧ ¬ρ false ![d]) ∧
        ∀ a b a' b' c d : A, ρ true ![a, b, c, d] → ρ true ![a', b', c, d] →
          a = a' ∧ b = b' := by
  letI := maxCutGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := mcSOLang) (M := A) mcSideSym w ↔ ρ false w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 4 → A),
      RelMap (L := mcSOLang) (M := A) mcInjSym w ↔ ρ true w := fun _ => Iff.rfl
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
theorem maxCut_sigmaSODefinable : SigmaSODefinable 1 MaxCut := by
  refine ⟨[maxCutGuessBlock], rfl, maxCutKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hmc⟩
    obtain ⟨S, ⟨e⟩⟩ := (maxCutOn_iff_certificate _ _).mp hmc
    refine ⟨fun i => match i with
      | false => fun w : Fin 1 → A => S (w 0)
      | true => fun w : Fin 4 → A =>
          ∃ h : MAGMarked (w 0) (w 1),
            (e ⟨(w 0, w 1), h⟩ : {p : A × A // CutRel MAGAdj S p.1 p.2}).1 = (w 2, w 3), ?_⟩
    refine (realize_maxCutKernel _).mpr ⟨fun a b hab =>
      ⟨(e ⟨(a, b), hab⟩).1.1, (e ⟨(a, b), hab⟩).1.2, ⟨hab, rfl⟩, (e ⟨(a, b), hab⟩).2.1,
        (e ⟨(a, b), hab⟩).2.2.1, (e ⟨(a, b), hab⟩).2.2.2⟩, ?_⟩
    rintro a b a' b' c d ⟨h, hcd⟩ ⟨h', hcd'⟩
    have heq := e.injective (Subtype.ext (hcd.trans hcd'.symm) :
      (e ⟨(a, b), h⟩ : {p : A × A // CutRel MAGAdj S p.1 p.2}) = e ⟨(a', b'), h'⟩)
    exact ⟨congrArg Prod.fst (congrArg Subtype.val heq),
      congrArg Prod.snd (congrArg Subtype.val heq)⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htot, hinj⟩ := (realize_maxCutKernel ρ).mp hρ
    have hch : ∀ p : {p : A × A // MAGMarked p.1 p.2},
        ∃ q : A × A, ρ true ![p.1.1, p.1.2, q.1, q.2] ∧
          CutRel MAGAdj (fun a => ρ false ![a]) q.1 q.2 := by
      rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨c, d, h₁, h₂, h₃, h₄⟩ := htot a b hab
      exact ⟨(c, d), h₁, h₂, h₃, h₄⟩
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (maxCutOn_iff_certificate _ _).mpr
      ⟨fun a => ρ false ![a], ⟨⟨fun p => ⟨f p, hf2 p⟩, fun p p' hpp' => ?_⟩⟩⟩⟩
    have hval : f p = f p' := congrArg Subtype.val hpp'
    obtain ⟨h₁, h₂⟩ := hinj p.1.1 p.1.2 p'.1.1 p'.1.2 (f p).1 (f p).2 (hf1 p)
      (by rw [hval]; exact hf1 p')
    exact Subtype.ext (Prod.ext h₁ h₂)

end SigmaOne

end DescriptiveComplexity
