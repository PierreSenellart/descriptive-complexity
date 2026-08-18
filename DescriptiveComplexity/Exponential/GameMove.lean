/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GamePhase

/-!
# Reading a block sentence in a copy, and moving one variable onto another

Two gadgets every phased game needs beyond
`DescriptiveComplexity.Exponential.GamePhase`, both stated for an **arbitrary**
block `C` and finite tag type `T`.

* **A one-copy sentence, read in a copy of a move.** The four sentences of a
  `DescriptiveComplexity.SOGameSpec` live at three different vocabularies, and
  everything a move says about *one* of its two states is a sentence over
  `(L + ≤) + C.lang` – the leaf kernel of a quantifier prefix, a guard, the
  order. `DescriptiveComplexity.moveFstLHom` and
  `DescriptiveComplexity.moveSndLHom` read such a sentence in the first and in
  the second copy, dropping the tag bits, and
  `DescriptiveComplexity.realize_moveFstLHom` /
  `DescriptiveComplexity.realize_moveSndLHom` say so.

* **One variable moved onto another.**
  `DescriptiveComplexity.varsFrozenS` freezes a variable *in place*, which is
  what a move that must not disturb the state says.
  `DescriptiveComplexity.varPairAgreeS` is the same statement between two
  *different* variables of equal arity – the first copy's `i` and the second
  copy's `j` – which is what a move that **shifts** part of the state says:
  copying the points of the node just chosen onto the slots the next position
  reads them from. Freezing is the diagonal case `j = i`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0}) (C : SOBlock) (T : Type) [Finite T]

/-! ### A one-copy sentence, read in a copy -/

/-- A sentence about one assignment of `C`, read in the **first** copy of a
move: the tag bits are invisible to it. -/
def moveFstLHom :
    ((L.sum Language.order).sum C.lang) →ᴸ
      (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s => Sum.inl (Sum.inr ⟨Sum.inr s.1, s.2⟩)

/-- A sentence about one assignment of `C`, read in the **second** copy of a
move – the state the move enters. -/
def moveSndLHom :
    ((L.sum Language.order).sum C.lang) →ᴸ
      (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl s => Sum.inl (Sum.inl s)
    | Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

variable {L C T} {A : Type} [instL : L.Structure A] [LinearOrder A]

theorem moveFstLHom_isExpansionOn (σ τ : (C.withTag T).Assignment A) :
    @LHom.IsExpansionOn _ _ (moveFstLHom L C T) A
      (@SOBlock.structure₁ (L.sum Language.order) C A
        (@sumOrderStructure L A instL _) (SOBlock.dropTag σ))
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ τ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) C A
    (@sumOrderStructure L A instL _) (SOBlock.dropTag σ)
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl g => rfl
    | Sum.inr g => exact isEmptyElim g
  · match n, r with
    | _, Sum.inl s => rfl
    | _, Sum.inr s => rfl

theorem moveSndLHom_isExpansionOn (σ τ : (C.withTag T).Assignment A) :
    @LHom.IsExpansionOn _ _ (moveSndLHom L C T) A
      (@SOBlock.structure₁ (L.sum Language.order) C A
        (@sumOrderStructure L A instL _) (SOBlock.dropTag τ))
      (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ τ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) C A
    (@sumOrderStructure L A instL _) (SOBlock.dropTag τ)
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl g => rfl
    | Sum.inr g => exact isEmptyElim g
  · match n, r with
    | _, Sum.inl s => rfl
    | _, Sum.inr s => rfl

/-- **The first copy of a move is the state it leaves.** -/
theorem realize_moveFstLHom (σ τ : (C.withTag T).Assignment A)
    (ψ : ((L.sum Language.order).sum C.lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ τ) ((moveFstLHom L C T).onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) C A
          (@sumOrderStructure L A instL _) (SOBlock.dropTag σ)) ψ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) C A
    (@sumOrderStructure L A instL _) (SOBlock.dropTag σ)
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  have := moveFstLHom_isExpansionOn (L := L) (C := C) (T := T) σ τ
  exact LHom.realize_onSentence (M := A) (moveFstLHom L C T) ψ

/-- **The second copy of a move is the state it enters.** -/
theorem realize_moveSndLHom (σ τ : (C.withTag T).Assignment A)
    (ψ : ((L.sum Language.order).sum C.lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ τ) ((moveSndLHom L C T).onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) C A
          (@sumOrderStructure L A instL _) (SOBlock.dropTag τ)) ψ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) C A
    (@sumOrderStructure L A instL _) (SOBlock.dropTag τ)
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  have := moveSndLHom_isExpansionOn (L := L) (C := C) (T := T) σ τ
  exact LHom.realize_onSentence (M := A) (moveSndLHom L C T) ψ

/-- **A sentence about the state a move leaves, tag bits included.** Unlike
`DescriptiveComplexity.realize_moveFstLHom` this reads a sentence over the
*tagged* block, which is what a move's guard on its own phase
(`DescriptiveComplexity.atTagF`) is. -/
theorem realize_tagFst (σ τ : (C.withTag T).Assignment A)
    (ψ : ((L.sum Language.order).sum (C.withTag T).lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ τ) (LHom.sumInl.onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ) ψ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ
  let := (C.withTag T).structure τ
  exact LHom.realize_onSentence (M := A) LHom.sumInl ψ

/-- **A state at a phase is a tagged one.** `DescriptiveComplexity.atTagF` is
the one-copy counterpart of
`DescriptiveComplexity.exists_tagAssign_two`: a start sentence that asserts it
admits no junk assignment. -/
theorem eq_tagAssign_of_atTagF (p : T) (σ : (C.withTag T).Assignment A)
    (h : @Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
        (@sumOrderStructure L A instL _) σ) (atTagF L C T p)) :
    σ = SOBlock.tagAssign p (SOBlock.dropTag σ) := by
  let := @SOBlock.structure₁ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ
  obtain ⟨hguard, -⟩ := Formula.realize_inf.mp h
  obtain ⟨q, ν, rfl⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) σ).mp hguard
  rw [(realize_atTagF p q ν).mp h]
  rfl

/-! ### One variable moved onto another -/

variable (L C T)

/-- **The move copies the variable `i` of the state it leaves onto the variable
`j` of the state it enters.** With `j = i` this is
`DescriptiveComplexity.varAgreeS`, i.e., freezing. -/
noncomputable def varPairAgreeS (i j : C.ι) (h : C.arity j = C.arity i) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  Formula.iAlls (Fin (C.arity i))
    (((Relations.formula (varFstSym L C T i) fun k => Term.var (Sum.inr k)).imp
        (Relations.formula (varSndSym L C T j) fun k => Term.var (Sum.inr (Fin.cast h k)))) ⊓
      ((Relations.formula (varSndSym L C T j) fun k =>
          Term.var (Sum.inr (Fin.cast h k))).imp
        (Relations.formula (varFstSym L C T i) fun k => Term.var (Sum.inr k))))

/-- **The listed variables are moved into place by the move.** -/
noncomputable def varsPairAgreeS (ps : List ({p : C.ι × C.ι // C.arity p.2 = C.arity p.1})) :
    (((L.sum Language.order).sum (C.withTag T).lang).sum (C.withTag T).lang).Sentence :=
  listInf (ps.map fun p => varPairAgreeS L C T p.1.1 p.1.2 p.2)

variable {L C T}

theorem realize_varPairAgreeS (σ τ : (C.withTag T).Assignment A) (i j : C.ι)
    (h : C.arity j = C.arity i) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ τ) (varPairAgreeS L C T i j h) ↔
      ∀ x : Fin (C.arity i) → A,
        σ (Sum.inr i) x ↔ τ (Sum.inr j) fun k => x (Fin.cast h k)) := by
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  rw [varPairAgreeS, Sentence.Realize, Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  simp only [Formula.realize_inf, Formula.realize_imp, Formula.realize_rel, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun hh => ⟨hh.1, hh.2⟩, fun hh => ⟨hh.1, hh.2⟩⟩

theorem realize_varsPairAgreeS (σ τ : (C.withTag T).Assignment A)
    (ps : List ({p : C.ι × C.ι // C.arity p.2 = C.arity p.1})) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
          (@sumOrderStructure L A instL _) σ τ) (varsPairAgreeS L C T ps) ↔
      ∀ p ∈ ps, ∀ x : Fin (C.arity p.1.1) → A,
        σ (Sum.inr p.1.1) x ↔ τ (Sum.inr p.1.2) fun k => x (Fin.cast p.2 k)) := by
  let := @SOBlock.structure₂ (L.sum Language.order) (C.withTag T) A
    (@sumOrderStructure L A instL _) σ τ
  rw [varsPairAgreeS, Sentence.Realize, realize_listInf]
  constructor
  · intro hh p hp
    exact (realize_varPairAgreeS σ τ p.1.1 p.1.2 p.2).mp
      (hh _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  · intro hh ψ hψ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hψ
    exact (realize_varPairAgreeS σ τ p.1.1 p.1.2 p.2).mpr (hh p hp)

end DescriptiveComplexity
