/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SetFamily.Defs
import DescriptiveComplexity.SecondOrder

/-!
# The set family is existential second-order definable

The membership half of the NP-completeness of Set Cover and Set Packing:
both are `Σ₁`-definable in the sense of `DescriptiveComplexity.SecondOrder`
(`DescriptiveComplexity.setCover_sigmaSODefinable`,
`DescriptiveComplexity.setPacking_sigmaSODefinable`). Hitting Set needs no definition
of its own: it FO-reduces to Set Cover
(`DescriptiveComplexity.Problems.SetFamily.Reductions`).

The two definitions share everything but their goal clause. A single
existential block (`DescriptiveComplexity.familyGuessBlock`) guesses a unary
relation – the subfamily – and a binary one – an injection witnessing the
threshold – and the first-order kernel is a conjunction of clauses built from
a common kit:

* `DescriptiveComplexity.sfFamClause`: the guessed subfamily consists of sets of the
  family (shared);
* the goal clause: `DescriptiveComplexity.sfCoverClause` (every ground element belongs
  to a guessed set) for Set Cover, `DescriptiveComplexity.sfDisjClause` (no ground
  element belongs to two distinct guessed sets) for Set Packing;
* the threshold clauses `DescriptiveComplexity.sfGuessToMarkedClause` (Set Cover, an
  upper bound: the subfamily injects into the marked set) or
  `DescriptiveComplexity.sfMarkedToGuessClause` (Set Packing, a lower bound: the marked
  set injects into the subfamily), together with the shared injectivity clause
  `DescriptiveComplexity.sfInjClause`.

The direction of the injection is the *only* semantic difference the threshold
makes, which is exactly what the embedding forms of
`DescriptiveComplexity.Problems.SetFamily.Defs`
(`DescriptiveComplexity.coversOn_iff_embedding`,
`DescriptiveComplexity.packsOn_iff_embedding`) say. This mirrors
`DescriptiveComplexity.clique_sigmaSODefinable`, whose threshold is a lower bound like
Set Packing's.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The single existential block shared by the `Σ₁` definitions of the set
family: a unary relation variable (`true`: the guessed subfamily) and a binary
one (`false`: the injection witnessing the threshold). -/
def familyGuessBlock : SOBlock where
  ι := Bool
  arity := fun i => cond i 1 2

/-- The symbol of the subfamily relation variable. -/
def sfGuessRel : familyGuessBlock.lang.Relations 1 := ⟨true, rfl⟩

/-- The symbol of the injection relation variable. -/
def sfInjRel : familyGuessBlock.lang.Relations 2 := ⟨false, rfl⟩

/-- The vocabulary of the kernels: set systems together with the two guessed
relation variables. -/
abbrev setFamilySOLang : Language := Language.setSystem.sum familyGuessBlock.lang

/-- The ground-element symbol in the kernels' vocabulary. -/
abbrev sfElemSym : setFamilySOLang.Relations 1 := Sum.inl ssElem

/-- The family symbol in the kernels' vocabulary. -/
abbrev sfFamSym : setFamilySOLang.Relations 1 := Sum.inl ssFam

/-- The incidence symbol in the kernels' vocabulary. -/
abbrev sfMemSym : setFamilySOLang.Relations 2 := Sum.inl ssMem

/-- The mark symbol in the kernels' vocabulary. -/
abbrev sfMarkedSym : setFamilySOLang.Relations 1 := Sum.inl ssMarked

/-- The subfamily symbol in the kernels' vocabulary. -/
abbrev sfGuessSym : setFamilySOLang.Relations 1 := Sum.inr sfGuessRel

/-- The injection symbol in the kernels' vocabulary. -/
abbrev sfInjSym : setFamilySOLang.Relations 2 := Sum.inr sfInjRel

/-! ### The clauses -/

/-- Kernel clause: the guessed subfamily consists of sets of the family. -/
noncomputable def sfFamClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfGuessSym (Term.var (Sum.inr 0))).imp
    (Relations.formula₁ sfFamSym (Term.var (Sum.inr 0)))).iAlls (Fin 1)

/-- Kernel clause (Set Cover): every ground element belongs to a guessed
set. -/
noncomputable def sfCoverClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfElemSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₁ sfGuessSym (Term.var (Sum.inr ())) ⊓
      Relations.formula₂ sfMemSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel clause (Set Packing): no ground element belongs to two distinct
guessed sets. -/
noncomputable def sfDisjClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfGuessSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ sfGuessSym (Term.var (Sum.inr 1)) ⊓
      ∼(Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))) ⊓
      Relations.formula₁ sfElemSym (Term.var (Sum.inr 2))).imp
    ∼(Relations.formula₂ sfMemSym (Term.var (Sum.inr 2)) (Term.var (Sum.inr 0)) ⊓
      Relations.formula₂ sfMemSym (Term.var (Sum.inr 2))
        (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- Kernel clause (Set Cover's threshold, an upper bound): the guessed
injection maps every member of the subfamily to a marked element. -/
noncomputable def sfGuessToMarkedClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfGuessSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ sfInjSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ())) ⊓
      Relations.formula₁ sfMarkedSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel clause (Set Packing's threshold, a lower bound): the guessed
injection maps every marked element to a member of the subfamily. -/
noncomputable def sfMarkedToGuessClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfMarkedSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ sfInjSym (Term.var (Sum.inl (Sum.inr 0)))
        (Term.var (Sum.inr ())) ⊓
      Relations.formula₁ sfGuessSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel clause: the guessed injection is injective. -/
noncomputable def sfInjClause : setFamilySOLang.Sentence :=
  ((Relations.formula₂ sfInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ sfInjSym (Term.var (Sum.inr 1))
        (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The kernel of the `Σ₁` definition of Set Cover. -/
noncomputable def setCoverKernel : setFamilySOLang.Sentence :=
  sfFamClause ⊓ (sfCoverClause ⊓ (sfGuessToMarkedClause ⊓ sfInjClause))

/-- The first-order kernel of the `Σ₁` definition of Exact Cover: the same
kit again, this time asking for a subfamily that both covers and is pairwise
disjoint – and, exactness replacing the threshold, no injection clause. -/
noncomputable def exactCoverKernel : setFamilySOLang.Sentence :=
  sfFamClause ⊓ (sfCoverClause ⊓ sfDisjClause)

/-- Kernel clause (Set Splitting): every set of the family contains a
coloured ground element. -/
noncomputable def sfSplitInClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfFamSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₁ sfElemSym (Term.var (Sum.inr ())) ⊓
      Relations.formula₂ sfMemSym (Term.var (Sum.inr ()))
        (Term.var (Sum.inl (Sum.inr 0))) ⊓
      Relations.formula₁ sfGuessSym (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- Kernel clause (Set Splitting): every set of the family contains an
uncoloured ground element. -/
noncomputable def sfSplitOutClause : setFamilySOLang.Sentence :=
  ((Relations.formula₁ sfFamSym (Term.var (Sum.inr 0))).imp
    ((Relations.formula₁ sfElemSym (Term.var (Sum.inr ())) ⊓
      Relations.formula₂ sfMemSym (Term.var (Sum.inr ()))
        (Term.var (Sum.inl (Sum.inr 0))) ⊓
      ∼(Relations.formula₁ sfGuessSym (Term.var (Sum.inr ())))).iExs Unit)).iAlls (Fin 1)

/-- The first-order kernel of the `Σ₁` definition of Set Splitting: the
guessed relation is read as one colour class, and every set of the family
meets it and its complement. -/
noncomputable def setSplittingKernel : setFamilySOLang.Sentence :=
  sfSplitInClause ⊓ sfSplitOutClause

/-- The kernel of the `Σ₁` definition of Set Packing. -/
noncomputable def setPackingKernel : setFamilySOLang.Sentence :=
  sfFamClause ⊓ (sfDisjClause ⊓ (sfMarkedToGuessClause ⊓ sfInjClause))

/-! ### Realization of the clauses -/

section Realize

variable {A : Type} [Language.setSystem.Structure A] (ρ : familyGuessBlock.Assignment A)

/-- Realization at a set system expanded by an assignment of the block. -/
private abbrev SFRealize (φ : setFamilySOLang.Sentence) : Prop :=
  @Sentence.Realize setFamilySOLang A
    (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) φ

private theorem realize_sfFamClause :
    SFRealize ρ sfFamClause ↔ ∀ s : A, ρ true ![s] → SSFam s := by
  letI := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [sfFamClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub]
  exact ⟨fun h s hs => h (fun _ => s) hs, fun h i hi => h (i 0) hi⟩

private theorem realize_sfCoverClause :
    SFRealize ρ sfCoverClause ↔ ∀ x : A, SSElem x → ∃ s : A, ρ true ![s] ∧ SSMem x s := by
  letI := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [sfCoverClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub]
  constructor
  · intro h x hx
    obtain ⟨s, hs1, hs2⟩ := h (fun _ => x) hx
    exact ⟨s (), hs1, hs2⟩
  · intro h i hi
    obtain ⟨s, hs1, hs2⟩ := h (i 0) hi
    exact ⟨fun _ => s, hs1, hs2⟩

private theorem realize_sfDisjClause :
    SFRealize ρ sfDisjClause ↔ ∀ s s' x : A, ρ true ![s] → ρ true ![s'] → s ≠ s' →
      SSElem x → ¬(SSMem x s ∧ SSMem x s') := by
  letI := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [sfDisjClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub]
  exact ⟨fun h s s' x hs hs' hne hx => h ![s, s', x] ⟨⟨⟨hs, hs'⟩, hne⟩, hx⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2⟩

private theorem realize_sfGuessToMarkedClause :
    SFRealize ρ sfGuessToMarkedClause ↔
      ∀ s : A, ρ true ![s] → ∃ y : A, ρ false ![s, y] ∧ SSMarked y := by
  letI := familyGuessBlock.structure ρ
  have hsubG : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := setFamilySOLang) (M := A) sfInjSym w ↔ ρ false w := fun _ => Iff.rfl
  rw [sfGuessToMarkedClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubG, hsubI]
  constructor
  · intro h s hs
    obtain ⟨y, hy1, hy2⟩ := h (fun _ => s) hs
    exact ⟨y (), hy1, hy2⟩
  · intro h i hi
    obtain ⟨y, hy1, hy2⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy1, hy2⟩

private theorem realize_sfMarkedToGuessClause :
    SFRealize ρ sfMarkedToGuessClause ↔
      ∀ y : A, SSMarked y → ∃ s : A, ρ false ![y, s] ∧ ρ true ![s] := by
  letI := familyGuessBlock.structure ρ
  have hsubG : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := setFamilySOLang) (M := A) sfInjSym w ↔ ρ false w := fun _ => Iff.rfl
  rw [sfMarkedToGuessClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubG, hsubI]
  constructor
  · intro h y hy
    obtain ⟨s, hs1, hs2⟩ := h (fun _ => y) hy
    exact ⟨s (), hs1, hs2⟩
  · intro h i hi
    obtain ⟨s, hs1, hs2⟩ := h (i 0) hi
    exact ⟨fun _ => s, hs1, hs2⟩

private theorem realize_sfInjClause :
    SFRealize ρ sfInjClause ↔ ∀ x x' y : A, ρ false ![x, y] → ρ false ![x', y] → x = x' := by
  letI := familyGuessBlock.structure ρ
  have hsubI : ∀ (w : Fin 2 → A),
      RelMap (L := setFamilySOLang) (M := A) sfInjSym w ↔ ρ false w := fun _ => Iff.rfl
  rw [sfInjClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, hsubI]
  exact ⟨fun h x x' y hxy hx'y => h ![x, x', y] ⟨hxy, hx'y⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

/-- Realization of the Set Cover kernel: the guessed subfamily consists of
sets and covers every element, and the guessed binary relation injects it into
the marked set. -/
private theorem realize_setCoverKernel :
    SFRealize ρ setCoverKernel ↔
      (∀ s : A, ρ true ![s] → SSFam s) ∧
        (∀ x : A, SSElem x → ∃ s : A, ρ true ![s] ∧ SSMem x s) ∧
        (∀ s : A, ρ true ![s] → ∃ y : A, ρ false ![s, y] ∧ SSMarked y) ∧
        ∀ x x' y : A, ρ false ![x, y] → ρ false ![x', y] → x = x' := by
  rw [setCoverKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfFamClause ρ)
    (and_congr (realize_sfCoverClause ρ)
      (and_congr (realize_sfGuessToMarkedClause ρ) (realize_sfInjClause ρ)))

/-- Realization of the Set Packing kernel: the guessed subfamily consists of
pairwise disjoint sets, and the guessed binary relation injects the marked set
into it. -/
private theorem realize_setPackingKernel :
    SFRealize ρ setPackingKernel ↔
      (∀ s : A, ρ true ![s] → SSFam s) ∧
        (∀ s s' x : A, ρ true ![s] → ρ true ![s'] → s ≠ s' → SSElem x →
          ¬(SSMem x s ∧ SSMem x s')) ∧
        (∀ y : A, SSMarked y → ∃ s : A, ρ false ![y, s] ∧ ρ true ![s]) ∧
        ∀ x x' y : A, ρ false ![x, y] → ρ false ![x', y] → x = x' := by
  rw [setPackingKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfFamClause ρ)
    (and_congr (realize_sfDisjClause ρ)
      (and_congr (realize_sfMarkedToGuessClause ρ) (realize_sfInjClause ρ)))

/-- Realization of the Exact Cover kernel: the guessed subfamily consists of
sets of the family, covers every ground element, and no element belongs to two
distinct members. -/
private theorem realize_exactCoverKernel :
    SFRealize ρ exactCoverKernel ↔
      (∀ s : A, ρ true ![s] → SSFam s) ∧
        (∀ x : A, SSElem x → ∃ s : A, ρ true ![s] ∧ SSMem x s) ∧
        ∀ s s' x : A, ρ true ![s] → ρ true ![s'] → s ≠ s' → SSElem x →
          ¬(SSMem x s ∧ SSMem x s') := by
  rw [exactCoverKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfFamClause ρ)
    (and_congr (realize_sfCoverClause ρ) (realize_sfDisjClause ρ))

private theorem realize_sfSplitInClause :
    SFRealize ρ sfSplitInClause ↔
      ∀ f : A, SSFam f → ∃ x : A, SSElem x ∧ SSMem x f ∧ ρ true ![x] := by
  letI := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [sfSplitInClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub]
  constructor
  · intro h f hf
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := h (fun _ => f) hf
    exact ⟨x (), hx1, hx2, hx3⟩
  · intro h i hi
    obtain ⟨x, hx1, hx2, hx3⟩ := h (i 0) hi
    exact ⟨fun _ => x, ⟨hx1, hx2⟩, hx3⟩

private theorem realize_sfSplitOutClause :
    SFRealize ρ sfSplitOutClause ↔
      ∀ f : A, SSFam f → ∃ x : A, SSElem x ∧ SSMem x f ∧ ¬ρ true ![x] := by
  letI := familyGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := setFamilySOLang) (M := A) sfGuessSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [sfSplitOutClause]
  simp only [SFRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h f hf
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := h (fun _ => f) hf
    exact ⟨x (), hx1, hx2, hx3⟩
  · intro h i hi
    obtain ⟨x, hx1, hx2, hx3⟩ := h (i 0) hi
    exact ⟨fun _ => x, ⟨hx1, hx2⟩, hx3⟩

/-- Realization of the Set Splitting kernel. -/
private theorem realize_setSplittingKernel :
    SFRealize ρ setSplittingKernel ↔
      (∀ f : A, SSFam f → ∃ x : A, SSElem x ∧ SSMem x f ∧ ρ true ![x]) ∧
        ∀ f : A, SSFam f → ∃ x : A, SSElem x ∧ SSMem x f ∧ ¬ρ true ![x] := by
  rw [setSplittingKernel]
  simp only [SFRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_sfSplitInClause ρ) (realize_sfSplitOutClause ρ)

end Realize

/-! ### The two definitions -/

/-- **Set Cover is `Σ₁`-definable**: existentially guess the covering
subfamily and an injection of it into the marked set, then check both
first-order. Since NP is defined as `Σ₁`-definability, this is the membership
half of the NP-completeness of Set Cover. -/
theorem setCover_sigmaSODefinable : SigmaSODefinable 1 SetCover := by
  refine ⟨[familyGuessBlock], rfl, setCoverKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hsc⟩
    obtain ⟨G, hGfam, hcov, ⟨e⟩⟩ := (coversOn_iff_embedding _ _ _ _).mp hsc
    refine ⟨fun i => match i with
      | true => fun w : Fin 1 → A => G (w 0)
      | false => fun w : Fin 2 → A =>
          ∃ h : G (w 0), (e ⟨w 0, h⟩ : {x // SSMarked x}).1 = w 1, ?_⟩
    refine (realize_setCoverKernel _).mpr
      ⟨fun s hs => hGfam s hs, fun x hx => hcov x hx,
        fun s hs => ⟨(e ⟨s, hs⟩).1, ⟨hs, rfl⟩, (e ⟨s, hs⟩).2⟩, ?_⟩
    rintro s s' y ⟨h, hs⟩ ⟨h', hs'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hs.trans hs'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨h1, h2, h3, h4⟩ := (realize_setCoverKernel ρ).mp hρ
    have hch : ∀ s : {x : A // ρ true ![x]},
        ∃ y : A, ρ false ![s.1, y] ∧ SSMarked y := fun s => h3 s.1 s.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (coversOn_iff_embedding _ _ _ _).mpr
      ⟨fun a => ρ true ![a], fun s hs => h1 s hs, fun x hx => h2 x hx,
        ⟨⟨fun s => ⟨f s, hf2 s⟩, fun s s' hss' => ?_⟩⟩⟩⟩
    have hval : f s = f s' := congrArg Subtype.val hss'
    refine Subtype.ext (h4 s.1 s'.1 (f s) (hf1 s) ?_)
    rw [hval]
    exact hf1 s'

/-- **Set Packing is `Σ₁`-definable**: existentially guess the packing and an
injection of the marked set into it, then check both first-order. Since NP is
defined as `Σ₁`-definability, this is the membership half of the
NP-completeness of Set Packing. -/
theorem setPacking_sigmaSODefinable : SigmaSODefinable 1 SetPacking := by
  refine ⟨[familyGuessBlock], rfl, setPackingKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hsp⟩
    obtain ⟨G, hGfam, hdisj, ⟨e⟩⟩ := (packsOn_iff_embedding _ _ _ _).mp hsp
    refine ⟨fun i => match i with
      | true => fun w : Fin 1 → A => G (w 0)
      | false => fun w : Fin 2 → A =>
          ∃ h : SSMarked (w 0), (e ⟨w 0, h⟩ : {s // G s}).1 = w 1, ?_⟩
    refine (realize_setPackingKernel _).mpr
      ⟨fun s hs => hGfam s hs, fun s s' x hs hs' hne hx => hdisj s s' hs hs' hne x hx,
        fun y hy => ⟨(e ⟨y, hy⟩).1, ⟨hy, rfl⟩, (e ⟨y, hy⟩).2⟩, ?_⟩
    rintro y y' s ⟨h, hs⟩ ⟨h', hs'⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext (hs.trans hs'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨h1, h2, h3, h4⟩ := (realize_setPackingKernel ρ).mp hρ
    have hch : ∀ y : {x : A // SSMarked x},
        ∃ s : A, ρ false ![y.1, s] ∧ ρ true ![s] := fun y => h3 y.1 y.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (packsOn_iff_embedding _ _ _ _).mpr
      ⟨fun a => ρ true ![a], fun s hs => h1 s hs,
        fun s s' hs hs' hne x hx => h2 s s' x hs hs' hne hx,
        ⟨⟨fun y => ⟨f y, hf2 y⟩, fun y y' hyy' => ?_⟩⟩⟩⟩
    have hval : f y = f y' := congrArg Subtype.val hyy'
    refine Subtype.ext (h4 y.1 y'.1 (f y) (hf1 y) ?_)
    rw [hval]
    exact hf1 y'

end SigmaOne

/-- **Exact Cover is `Σ₁`-definable**: existentially guess the subfamily and
check first-order that it covers every ground element and that no element is
covered twice. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of Exact Cover. -/
theorem exactCover_sigmaSODefinable : SigmaSODefinable 1 ExactCover := by
  refine ⟨[familyGuessBlock], rfl, exactCoverKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨G, hGfam, hcov, hdisj⟩
    refine ⟨fun i => match i with
      | true => fun w : Fin 1 → A => G (w 0)
      | false => fun _ : Fin 2 → A => False, ?_⟩
    exact (realize_exactCoverKernel _).mpr
      ⟨fun s hs => hGfam s hs, fun x hx => hcov x hx,
        fun s s' x hs hs' hne hx => hdisj s s' hs hs' hne x hx⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hGfam, hcov, hdisj⟩ := (realize_exactCoverKernel ρ).mp hρ
    exact ⟨fun s => ρ true ![s], hGfam, hcov,
      fun s s' hs hs' hne x hx => hdisj s s' x hs hs' hne hx⟩

/-- **Set Splitting is `Σ₁`-definable**: existentially guess one colour class
and check first-order that every set of the family meets it and its
complement. -/
theorem setSplitting_sigmaSODefinable : SigmaSODefinable 1 SetSplitting := by
  refine ⟨[familyGuessBlock], rfl, setSplittingKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨fun i => match i with
      | true => fun w : Fin 1 → A => S (w 0)
      | false => fun _ : Fin 2 → A => False, ?_⟩
    exact (realize_setSplittingKernel _).mpr
      ⟨fun f hf => (hS f hf).1, fun f hf => (hS f hf).2⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hin, hout⟩ := (realize_setSplittingKernel ρ).mp hρ
    exact ⟨fun x => ρ true ![x], fun f hf => ⟨hin f hf, hout f hf⟩⟩

end DescriptiveComplexity
