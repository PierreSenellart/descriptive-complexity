/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.Defs
import DescriptiveComplexity.SecondOrder

/-!
# The feedback problems are existential second-order definable

The membership half of the NP-completeness of both feedback problems:
`DescriptiveComplexity.feedbackVertexSet_sigmaSODefinable` and
`DescriptiveComplexity.feedbackArcSet_sigmaSODefinable`.

Acyclicity is not first-order, but its certificate is
(`DescriptiveComplexity.acyclicRel_iff_exists_order`), so both definitions have the
same five-clause shape. A single existential block guesses

* the removed object – a set of vertices for Feedback Vertex Set (arity 1), a
  set of arcs for Feedback Arc Set (arity 2);
* a strict partial order certifying that what survives is acyclic (arity 2);
* an injection of the removed object into the marked set, witnessing the
  threshold – arity 2 for Feedback Vertex Set, where it maps vertices to
  vertices, and **arity 4** for Feedback Arc Set, where it maps pairs to
  pairs, the threshold living one arity up (representation (A) read at arity
  2, see `DescriptiveComplexity.nonempty_embedding_iff_ncard_le₂`);

and the kernel checks transitivity, irreflexivity, that every surviving arc
goes forward in the order, and that the injection is total and injective. The
arity-4 atom is the only thing the second definition needs beyond the first,
and it costs nothing beyond `DescriptiveComplexity.realize_rel₄`
(`DescriptiveComplexity.Interpretation`), Mathlib's `Formula.realize_rel₁`/`₂` stopping
at arity 2.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Feedback Vertex
Set: the removed set (unary), a strict partial order certifying acyclicity
(binary), and an injection of the removed set into the marked set
(binary). -/
def feedbackGuessBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | none => 1
    | some _ => 2

/-- The symbol of the removed-set relation variable. -/
def fvsSetSym : feedbackGuessBlock.lang.Relations 1 := ⟨none, rfl⟩

/-- The symbol of the order relation variable. -/
def fvsLtSym : feedbackGuessBlock.lang.Relations 2 := ⟨some true, rfl⟩

/-- The symbol of the injection relation variable. -/
def fvsInjSym : feedbackGuessBlock.lang.Relations 2 := ⟨some false, rfl⟩

/-- The vocabulary of the kernel: marked graphs together with the three
guessed relation variables. -/
abbrev fvsSOLang : Language := Language.markedGraph.sum feedbackGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev fAdjSym : fvsSOLang.Relations 2 := Sum.inl mgAdj

/-- The mark symbol in the kernel's vocabulary. -/
abbrev fMarkedSym : fvsSOLang.Relations 1 := Sum.inl mgMarked

/-- The removed-set symbol in the kernel's vocabulary. -/
abbrev fSetSym : fvsSOLang.Relations 1 := Sum.inr fvsSetSym

/-- The order symbol in the kernel's vocabulary. -/
abbrev fLtSym : fvsSOLang.Relations 2 := Sum.inr fvsLtSym

/-- The injection symbol in the kernel's vocabulary. -/
abbrev fInjSym : fvsSOLang.Relations 2 := Sum.inr fvsInjSym

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def fvsTransClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ fLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ fLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel conjunct: the guessed order is irreflexive. -/
private noncomputable def fvsIrreflClause : fvsSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ fLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel conjunct: every surviving arc goes forward in the guessed
order. -/
private noncomputable def fvsArcClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fAdjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      ∼(Relations.formula₁ fSetSym (Term.var (Sum.inr 0))) ⊓
      ∼(Relations.formula₁ fSetSym (Term.var (Sum.inr 1)))).imp
    (Relations.formula₂ fLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel conjunct: the guessed injection maps every removed vertex to a
marked element. -/
private noncomputable def fvsTotalClause : fvsSOLang.Sentence :=
  ((Relations.formula₁ fSetSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ fInjSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ())) ⊓
      Relations.formula₁ fMarkedSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def fvsInjClause : fvsSOLang.Sentence :=
  ((Relations.formula₂ fInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ fInjSym (Term.var (Sum.inr 1))
        (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The first-order kernel of the `Σ₁` definition of Feedback Vertex Set. -/
noncomputable def feedbackKernel : fvsSOLang.Sentence :=
  fvsTransClause ⊓ (fvsIrreflClause ⊓ (fvsArcClause ⊓ (fvsTotalClause ⊓ fvsInjClause)))

/-- Realization of the kernel under an assignment of the three relation
variables. -/
private theorem realize_feedbackKernel {A : Type} [Language.markedGraph.Structure A]
    (ρ : feedbackGuessBlock.Assignment A) :
    (@Sentence.Realize fvsSOLang A
        (@sumStructure _ _ A _ (feedbackGuessBlock.structure ρ)) feedbackKernel) ↔
      (∀ x y z : A, ρ (some true) ![x, y] → ρ (some true) ![y, z] → ρ (some true) ![x, z]) ∧
        (∀ x : A, ¬ρ (some true) ![x, x]) ∧
        (∀ x y : A, MGAdj x y → ¬ρ none ![x] → ¬ρ none ![y] → ρ (some true) ![x, y]) ∧
        (∀ x : A, ρ none ![x] → ∃ y : A, ρ (some false) ![x, y] ∧ MGMarked y) ∧
        ∀ x x' y : A, ρ (some false) ![x, y] → ρ (some false) ![x', y] → x = x' := by
  letI := feedbackGuessBlock.structure ρ
  have hsubS : ∀ (w : Fin 1 → A),
      RelMap (L := fvsSOLang) (M := A) fSetSym w ↔ ρ none w := fun _ => Iff.rfl
  have hsubL : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fLtSym w ↔ ρ (some true) w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := fvsSOLang) (M := A) fInjSym w ↔ ρ (some false) w := fun _ => Iff.rfl
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
    exact ⟨y (), hy1, hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩
  · exact h ![x, x', y] ⟨hxy, hx'y⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2

/-- **Feedback Vertex Set is `Σ₁`-definable**: existentially guess the
removed set, a strict partial order certifying that the rest is acyclic, and
an injection of the removed set into the marked set, then check all five
conditions first-order. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of Feedback Vertex Set. -/
theorem feedbackVertexSet_sigmaSODefinable : SigmaSODefinable 1 FeedbackVertexSet := by
  refine ⟨[feedbackGuessBlock], rfl, feedbackKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hfvs⟩
    obtain ⟨C, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackOn_iff_certificate _ _).mp hfvs
    refine ⟨fun i => match i with
      | none => fun w : Fin 1 → A => C (w 0)
      | some true => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | some false => fun w : Fin 2 → A =>
          ∃ h : C (w 0), (e ⟨w 0, h⟩ : {x // MGMarked x}).1 = w 1, ?_⟩
    refine (realize_feedbackKernel _).mpr
      ⟨htrans, hirr,
        fun x y hadj hx hy => hmono x y ⟨hx, hy, hadj⟩,
        fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htrans, hirr, harc, htot, hinj⟩ := (realize_feedbackKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ none ![x]},
        ∃ y : A, ρ (some false) ![x.1, y] ∧ MGMarked y := fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (feedbackOn_iff_certificate _ _).mpr
      ⟨fun a => ρ none ![a],
        ⟨fun x y => ρ (some true) ![x, y], htrans, hirr,
          fun a b hab => harc a b hab.2.2 hab.1 hab.2.1⟩,
        ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    have hval : f x = f x' := congrArg Subtype.val hxx'
    refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
    rw [hval]
    exact hf1 x'

/-! ### Feedback Arc Set -/

/-- The single existential block of the `Σ₁` definition of Feedback Arc Set:
the removed set of arcs (binary), a strict partial order certifying acyclicity
(binary), and an injection of the removed arcs into the marked relation
(quaternary: it maps pairs to pairs). -/
def feedbackArcGuessBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with
    | none => 2
    | some true => 2
    | some false => 4

/-- The symbol of the removed-arc relation variable. -/
def fasCutRel : feedbackArcGuessBlock.lang.Relations 2 := ⟨none, rfl⟩

/-- The symbol of the order relation variable. -/
def fasLtRel : feedbackArcGuessBlock.lang.Relations 2 := ⟨some true, rfl⟩

/-- The symbol of the injection relation variable. -/
def fasInjRel : feedbackArcGuessBlock.lang.Relations 4 := ⟨some false, rfl⟩

/-- The vocabulary of the kernel: arc-marked digraphs together with the three
guessed relation variables. -/
abbrev fasSOLang : Language := Language.markedArcGraph.sum feedbackArcGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev fasAdjSym : fasSOLang.Relations 2 := Sum.inl magAdj

/-- The mark symbol in the kernel's vocabulary. -/
abbrev fasMarkedSym : fasSOLang.Relations 2 := Sum.inl magMarked

/-- The removed-arc symbol in the kernel's vocabulary. -/
abbrev fasCutSym : fasSOLang.Relations 2 := Sum.inr fasCutRel

/-- The order symbol in the kernel's vocabulary. -/
abbrev fasLtSym : fasSOLang.Relations 2 := Sum.inr fasLtRel

/-- The injection symbol in the kernel's vocabulary. -/
abbrev fasInjSym : fasSOLang.Relations 4 := Sum.inr fasInjRel

/-- Kernel conjunct: the guessed order is transitive. -/
private noncomputable def fasTransClause : fasSOLang.Sentence :=
  ((Relations.formula₂ fasLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ fasLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ fasLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel conjunct: the guessed order is irreflexive. -/
private noncomputable def fasIrreflClause : fasSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ fasLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel conjunct: every arc that is not cut goes forward in the guessed
order. -/
private noncomputable def fasArcClause : fasSOLang.Sentence :=
  ((Relations.formula₂ fasAdjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      ∼(Relations.formula₂ fasCutSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).imp
    (Relations.formula₂ fasLtSym (Term.var (Sum.inr 0))
      (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel conjunct: the guessed injection maps every cut arc to a marked
arc. -/
private noncomputable def fasTotalClause : fasSOLang.Sentence :=
  ((Relations.formula₂ fasCutSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    ((Relations.formula fasInjSym ![Term.var (Sum.inl (Sum.inr 0)),
          Term.var (Sum.inl (Sum.inr 1)), Term.var (Sum.inr 0), Term.var (Sum.inr 1)] ⊓
      Relations.formula₂ fasMarkedSym (Term.var (Sum.inr 0))
        (Term.var (Sum.inr 1))).iExs (Fin 2))).iAlls (Fin 2)

/-- Kernel conjunct: the guessed injection is injective. -/
private noncomputable def fasInjClause : fasSOLang.Sentence :=
  ((Relations.formula fasInjSym ![Term.var (Sum.inr 0), Term.var (Sum.inr 1),
        Term.var (Sum.inr 4), Term.var (Sum.inr 5)] ⊓
      Relations.formula fasInjSym ![Term.var (Sum.inr 2), Term.var (Sum.inr 3),
        Term.var (Sum.inr 4), Term.var (Sum.inr 5)]).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3)))).iAlls (Fin 6)

/-- The first-order kernel of the `Σ₁` definition of Feedback Arc Set. -/
noncomputable def feedbackArcKernel : fasSOLang.Sentence :=
  fasTransClause ⊓ (fasIrreflClause ⊓ (fasArcClause ⊓ (fasTotalClause ⊓ fasInjClause)))

/-- Realization of the kernel under an assignment of the three relation
variables. -/
private theorem realize_feedbackArcKernel {A : Type} [Language.markedArcGraph.Structure A]
    (ρ : feedbackArcGuessBlock.Assignment A) :
    (@Sentence.Realize fasSOLang A
        (@sumStructure _ _ A _ (feedbackArcGuessBlock.structure ρ)) feedbackArcKernel) ↔
      (∀ x y z : A, ρ (some true) ![x, y] → ρ (some true) ![y, z] → ρ (some true) ![x, z]) ∧
        (∀ x : A, ¬ρ (some true) ![x, x]) ∧
        (∀ x y : A, MAGAdj x y → ¬ρ none ![x, y] → ρ (some true) ![x, y]) ∧
        (∀ a b : A, ρ none ![a, b] →
          ∃ c d : A, ρ (some false) ![a, b, c, d] ∧ MAGMarked c d) ∧
        ∀ a b a' b' c d : A, ρ (some false) ![a, b, c, d] → ρ (some false) ![a', b', c, d] →
          a = a' ∧ b = b' := by
  letI := feedbackArcGuessBlock.structure ρ
  have hsubC : ∀ (w : Fin 2 → A),
      RelMap (L := fasSOLang) (M := A) fasCutSym w ↔ ρ none w := fun _ => Iff.rfl
  have hsubL : ∀ (w : Fin 2 → A),
      RelMap (L := fasSOLang) (M := A) fasLtSym w ↔ ρ (some true) w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 4 → A),
      RelMap (L := fasSOLang) (M := A) fasInjSym w ↔ ρ (some false) w := fun _ => Iff.rfl
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
theorem feedbackArcSet_sigmaSODefinable : SigmaSODefinable 1 FeedbackArcSet := by
  refine ⟨[feedbackArcGuessBlock], rfl, feedbackArcKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hfas⟩
    obtain ⟨F, ⟨Lt, htrans, hirr, hmono⟩, ⟨e⟩⟩ := (feedbackArcOn_iff_certificate _ _).mp hfas
    refine ⟨fun i => match i with
      | none => fun w : Fin 2 → A => F (w 0) (w 1)
      | some true => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | some false => fun w : Fin 4 → A =>
          ∃ h : F (w 0) (w 1),
            (e ⟨(w 0, w 1), h⟩ : {p : A × A // MAGMarked p.1 p.2}).1 = (w 2, w 3), ?_⟩
    refine (realize_feedbackArcKernel _).mpr
      ⟨htrans, hirr, fun x y hadj hcut => hmono x y ⟨hadj, hcut⟩, fun a b hab =>
        ⟨(e ⟨(a, b), hab⟩).1.1, (e ⟨(a, b), hab⟩).1.2, ⟨hab, rfl⟩, (e ⟨(a, b), hab⟩).2⟩, ?_⟩
    rintro a b a' b' c d ⟨h, hcd⟩ ⟨h', hcd'⟩
    have heq := e.injective (Subtype.ext (hcd.trans hcd'.symm) :
      (e ⟨(a, b), h⟩ : {p : A × A // MAGMarked p.1 p.2}) = e ⟨(a', b'), h'⟩)
    exact ⟨congrArg Prod.fst (congrArg Subtype.val heq),
      congrArg Prod.snd (congrArg Subtype.val heq)⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htrans, hirr, harc, htot, hinj⟩ := (realize_feedbackArcKernel ρ).mp hρ
    have hch : ∀ p : {p : A × A // ρ none ![p.1, p.2]},
        ∃ q : A × A, ρ (some false) ![p.1.1, p.1.2, q.1, q.2] ∧ MAGMarked q.1 q.2 := by
      rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨c, d, h₁, h₂⟩ := htot a b hab
      exact ⟨(c, d), h₁, h₂⟩
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (feedbackArcOn_iff_certificate _ _).mpr
      ⟨fun a b => ρ none ![a, b],
        ⟨fun x y => ρ (some true) ![x, y], htrans, hirr,
          fun a b hab => harc a b hab.1 hab.2⟩,
        ⟨⟨fun p => ⟨f p, hf2 p⟩, fun p p' hpp' => ?_⟩⟩⟩⟩
    have hval : f p = f p' := congrArg Subtype.val hpp'
    obtain ⟨h₁, h₂⟩ := hinj p.1.1 p.1.2 p'.1.1 p'.1.2 (f p).1 (f p).2 (hf1 p)
      (by rw [hval]; exact hf1 p')
    exact Subtype.ext (Prod.ext h₁ h₂)

end SigmaOne

end DescriptiveComplexity
