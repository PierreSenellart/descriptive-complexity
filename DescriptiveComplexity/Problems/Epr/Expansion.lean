/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Expansion
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Problems.Epr.Small

/-!
# The expansion whose points are the relations on the instance

What EPR's membership is read over. `DescriptiveComplexity.AddrExp.addrExp` has
a block of one *unary* variable, so its points are the subsets of the instance;
here the block's variable is **binary**, so a point is a binary relation – and
an assignment of the universal variables of an `∃*∀*` sentence is exactly that,
a function being a relation.

Three tags keep the smaller objects visible inside the expansion:

* `elt`, whose points are the singletons of the diagonal – one per element of
  the instance;
* `pair`, whose points are the singletons – one per *ordered pair* of elements,
  which is what lets every symbol of the expanded vocabulary stay binary: a
  ternary fact about the instance is read as a binary one about a pair;
* `asg`, whose points are unrestricted – the assignments themselves.

The size is what the class needs: with `n` elements there are `2^(n²)` points,
so a `Σ₁` sentence read here is a nondeterministic computation of exponential
time in a *polynomial* of the instance, which is what NEXPTIME is.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Epr

/-! ### The block and the vocabularies -/

section Vocabularies

/-- **The block of the expansion**: one binary relation variable, so an
assignment of it is a binary relation on the instance.

Marked `@[reducible]` so that the numerals of a tuple of its arity elaborate. -/
@[reducible]
def pairBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2

/-- The instance's vocabulary together with the order, over which the defining
sentences of the expansion live. -/
abbrev peOrd : Language.{0, 0} := Language.epr.sum Language.order

/-- One copy of the block. -/
abbrev peLang1 : Language.{0, 0} := peOrd.sum pairBlock.lang

/-- Two copies of the block. -/
abbrev peLang2 : Language.{0, 0} := peLang1.sum pairBlock.lang

/-- The block's variable, in the one-copy vocabulary. -/
abbrev peSym1 : peLang1.Relations 2 := Sum.inr ⟨(), rfl⟩

/-- The first copy's variable, in the two-copy vocabulary. -/
abbrev peSymA : peLang2.Relations 2 := Sum.inl (Sum.inr ⟨(), rfl⟩)

/-- The second copy's variable, in the two-copy vocabulary. -/
abbrev peSymB : peLang2.Relations 2 := Sum.inr ⟨(), rfl⟩

/-- An instance symbol, in the ordered vocabulary. -/
abbrev peIn {n : ℕ} (r : Language.epr.Relations n) : peOrd.Relations n := Sum.inl r

end Vocabularies

/-! ### Relations, as assignments of the block -/

section Assignments

variable {A : Type}

/-- The relation an assignment of the block is. -/
def peRel (ρ : pairBlock.Assignment A) : A → A → Prop := fun x y => ρ () ![x, y]

/-- And the assignment a relation is. -/
def peAssign (R : A → A → Prop) : pairBlock.Assignment A := fun _ v => R (v 0) (v 1)

@[simp]
theorem peRel_peAssign (R : A → A → Prop) : peRel (peAssign R) = R := rfl

theorem peAssign_peRel (ρ : pairBlock.Assignment A) : peAssign (peRel ρ) = ρ := by
  funext i v
  cases i
  refine congrArg (ρ ()) (funext fun j => ?_)
  fin_cases j <;> rfl

theorem peRel_injective : Function.Injective (peRel (A := A)) := by
  intro ρ σ h
  rw [← peAssign_peRel ρ, ← peAssign_peRel σ, h]

end Assignments

/-! ### The atoms of the block and the lifts -/

section Atoms

variable {γ : Type}

/-- The block's variable, as a formula over one copy. -/
noncomputable def peF1 (x y : γ) : peLang1.Formula γ :=
  Relations.formula₂ peSym1 (Term.var x) (Term.var y)

/-- The first copy's variable, as a formula over two copies. -/
noncomputable def peFA (x y : γ) : peLang2.Formula γ :=
  Relations.formula₂ peSymA (Term.var x) (Term.var y)

/-- The second copy's variable, as a formula over two copies. -/
noncomputable def peFB (x y : γ) : peLang2.Formula γ :=
  Relations.formula₂ peSymB (Term.var x) (Term.var y)

/-- A unary relation of the instance, as a formula. -/
noncomputable def peMarkG (r : Language.epr.Relations 1) (x : γ) : peOrd.Formula γ :=
  Relations.formula₁ (peIn r) (Term.var x)

/-- A binary relation of the instance, as a formula. -/
noncomputable def peBinG (r : Language.epr.Relations 2) (x y : γ) : peOrd.Formula γ :=
  Relations.formula₂ (peIn r) (Term.var x) (Term.var y)

/-- A ternary relation of the instance, as a formula. -/
noncomputable def peTerG (r : Language.epr.Relations 3) (x y z : γ) : peOrd.Formula γ :=
  Relations.formula (peIn r) ![Term.var x, Term.var y, Term.var z]

/-- Equality of two variables, as a formula. -/
noncomputable def peEqG (x y : γ) : peOrd.Formula γ :=
  Term.equal (Term.var x) (Term.var y)

/-- Reading a sentence of the base vocabulary in the one-copy vocabulary. -/
noncomputable def peLift1 (φ : peOrd.Formula γ) : peLang1.Formula γ :=
  LHom.sumInl.onFormula φ

/-- And in the two-copy vocabulary. -/
noncomputable def peLift2 (φ : peOrd.Formula γ) : peLang2.Formula γ :=
  LHom.sumInl.onFormula (LHom.sumInl.onFormula φ)

variable {A : Type} [Language.epr.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_peF1 (ρ : pairBlock.Assignment A) (x y : γ) :
    (@Formula.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) _ (peF1 x y) v ↔
      peRel ρ (v x) (v y)) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  simp only [peF1, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_peFA (ρ σ : pairBlock.Assignment A) (x y : γ) :
    (@Formula.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) _ (peFA x y) v ↔
      peRel ρ (v x) (v y)) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [peFA, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_peFB (ρ σ : pairBlock.Assignment A) (x y : γ) :
    (@Formula.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) _ (peFB x y) v ↔
      peRel σ (v x) (v y)) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [peFB, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_peMarkG (r : Language.epr.Relations 1) (x : γ) :
    ((peMarkG r x).Realize v ↔ RelMap r ![v x]) := by
  simp only [peMarkG, Formula.realize_rel₁]
  rfl

@[simp]
theorem realize_peBinG (r : Language.epr.Relations 2) (x y : γ) :
    ((peBinG r x y).Realize v ↔ RelMap r ![v x, v y]) := by
  simp only [peBinG, Formula.realize_rel₂]
  rfl

@[simp]
theorem realize_peTerG (r : Language.epr.Relations 3) (x y z : γ) :
    ((peTerG r x y z).Realize v ↔ RelMap r ![v x, v y, v z]) := by
  simp only [peTerG, realize_rel₃]
  rfl

@[simp]
theorem realize_peEqG (x y : γ) : ((peEqG x y).Realize v ↔ v x = v y) := by
  rw [peEqG, Formula.realize_equal, Term.realize_var, Term.realize_var]

@[simp]
theorem realize_peLift1 (ρ : pairBlock.Assignment A) (φ : peOrd.Formula γ) :
    (@Formula.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) _ (peLift1 φ) v ↔
      φ.Realize v) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  exact LHom.realize_onFormula LHom.sumInl φ

@[simp]
theorem realize_peLift2 (ρ σ : pairBlock.Assignment A) (φ : peOrd.Formula γ) :
    (@Formula.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) _ (peLift2 φ) v ↔
      φ.Realize v) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  exact (LHom.realize_onFormula LHom.sumInl (LHom.sumInl.onFormula φ)).trans
    (LHom.realize_onFormula LHom.sumInl φ)

end Atoms

/-! ### The tags and their domains -/

section Tags

/-- The tags of the expansion: the elements, the ordered pairs, and the
assignments. -/
inductive ETag
  /-- The point is an element of the instance. -/
  | elt
  /-- The point is an ordered pair of elements. -/
  | pair
  /-- The point is an assignment – any binary relation. -/
  | asg
  deriving DecidableEq

instance : Fintype ETag := ⟨{ETag.elt, ETag.pair, ETag.asg}, by intro x; cases x <;> simp⟩

variable {A : Type}

/-- **A relation that is the diagonal singleton of an element**: the reading
that makes an element of the instance a point of the expansion. -/
def PEDiag (R : A → A → Prop) : Prop := ∃ x, ∀ y z, R y z ↔ (y = x ∧ z = x)

/-- **A relation that is a singleton**: the reading that makes an ordered pair
one. -/
def PEPairRel (R : A → A → Prop) : Prop := ∃ x y, ∀ z w, R z w ↔ (z = x ∧ w = y)

theorem peDiag_diag (x : A) : PEDiag (fun y z : A => y = x ∧ z = x) := ⟨x, fun _ _ => Iff.rfl⟩

theorem pePairRel_pair (x y : A) : PEPairRel (fun z w : A => z = x ∧ w = y) :=
  ⟨x, y, fun _ _ => Iff.rfl⟩

/-- The domain sentence of the elements: the relation is a diagonal
singleton. -/
noncomputable def diagS : peLang1.Sentence :=
  Formula.iExs (Fin 1) (Formula.iAlls (Fin 2)
    (peF1 (Sum.inr 0) (Sum.inr 1) ⇔
      (peLift1 (peEqG (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⊓
        peLift1 (peEqG (Sum.inr 1) (Sum.inl (Sum.inr 0))))))

/-- The domain sentence of the pairs: the relation is a singleton. -/
noncomputable def pairS : peLang1.Sentence :=
  Formula.iExs (Fin 2) (Formula.iAlls (Fin 2)
    (peF1 (Sum.inr 0) (Sum.inr 1) ⇔
      (peLift1 (peEqG (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⊓
        peLift1 (peEqG (Sum.inr 1) (Sum.inl (Sum.inr 1))))))

/-- The domain sentence of each tag. -/
noncomputable def domT : ETag → peLang1.Sentence
  | .elt => diagS
  | .pair => pairS
  | .asg => ⊤

variable [Language.epr.Structure A] [LinearOrder A]

@[simp]
theorem realize_diagS (ρ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) diagS ↔
      PEDiag (peRel ρ)) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  simp only [diagS, PEDiag, Sentence.Realize, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_iff, Formula.realize_inf, realize_peF1, realize_peLift1, realize_peEqG,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, fun y z => hw ![y, z]⟩,
    fun ⟨x, hx⟩ => ⟨fun _ => x, fun w => hx (w 0) (w 1)⟩⟩

@[simp]
theorem realize_pairS (ρ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) pairS ↔
      PEPairRel (peRel ρ)) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  simp only [pairS, PEPairRel, Sentence.Realize, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_iff, Formula.realize_inf, realize_peF1, realize_peLift1, realize_peEqG,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, fun y z => hw ![y, z]⟩,
    fun ⟨x, y, hxy⟩ => ⟨![x, y], fun w => hxy (w 0) (w 1)⟩⟩

end Tags

end Epr

end DescriptiveComplexity

/- The vocabulary the points of the expansion are read in lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.epr`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the vocabulary the expansion's points are read in: the
three kinds of point, the instance's own relations read at elements, the
components of a pair, the argument of a literal-position pair, and membership of
a pair in an assignment. Every symbol is unary or binary, the pairs being points
of their own. -/
inductive eprPtRel : ℕ → Type
  /-- `isElt p`: the point `p` is an element of the instance. -/
  | isElt : eprPtRel 1
  /-- `isPair p`: the point `p` is an ordered pair of elements. -/
  | isPair : eprPtRel 1
  /-- `isAsg p`: the point `p` is an assignment. -/
  | isAsg : eprPtRel 1
  /-- `evarE x`: the element `x` is an existential variable. -/
  | evarE : eprPtRel 1
  /-- `clE c`: the element `c` is a clause. -/
  | clE : eprPtRel 1
  /-- `inClE c l`: the literal `l` occurs in the clause `c`. -/
  | inClE : eprPtRel 2
  /-- `posLE l s`: the literal `l` is the positive atom of `s`. -/
  | posLE : eprPtRel 2
  /-- `negLE l s`: the literal `l` is the negated atom of `s`. -/
  | negLE : eprPtRel 2
  /-- `sigE s p`: the symbol `s` has the argument position `p`. -/
  | sigE : eprPtRel 2
  /-- `fstP q x`: the first component of the pair `q` is `x`. -/
  | fstP : eprPtRel 2
  /-- `sndP q y`: the second component of the pair `q` is `y`. -/
  | sndP : eprPtRel 2
  /-- `argP q x`: the pair `q` is a literal and a position whose argument is the
  variable `x`. -/
  | argP : eprPtRel 2
  /-- `memP r q`: the assignment `r` contains the pair `q`. -/
  | memP : eprPtRel 2
  deriving DecidableEq

/-- The vocabulary of the expansion's points. -/
protected def eprPt : Language :=
  ⟨fun _ => Empty, eprPtRel⟩

instance : IsRelational Language.eprPt :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The symbol marking the points that are elements. -/
abbrev peIsEltSym : Language.eprPt.Relations 1 := .isElt

/-- The symbol marking the points that are pairs. -/
abbrev peIsPairSym : Language.eprPt.Relations 1 := .isPair

/-- The symbol marking the points that are assignments. -/
abbrev peIsAsgSym : Language.eprPt.Relations 1 := .isAsg

/-- The existential-variable symbol, at the points. -/
abbrev peEVarSym : Language.eprPt.Relations 1 := .evarE

/-- The clause symbol, at the points. -/
abbrev peClSym : Language.eprPt.Relations 1 := .clE

/-- The literal-of-a-clause symbol, at the points. -/
abbrev peInClSym : Language.eprPt.Relations 2 := .inClE

/-- The positive-literal symbol, at the points. -/
abbrev pePosSym : Language.eprPt.Relations 2 := .posLE

/-- The negated-literal symbol, at the points. -/
abbrev peNegSym : Language.eprPt.Relations 2 := .negLE

/-- The signature symbol, at the points. -/
abbrev peSigSym : Language.eprPt.Relations 2 := .sigE

/-- The first-component symbol. -/
abbrev peFstSym : Language.eprPt.Relations 2 := .fstP

/-- The second-component symbol. -/
abbrev peSndSym : Language.eprPt.Relations 2 := .sndP

/-- The argument symbol, read at a literal-position pair. -/
abbrev peArgSym : Language.eprPt.Relations 2 := .argP

/-- The membership symbol of an assignment. -/
abbrev peMemSym : Language.eprPt.Relations 2 := .memP

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Epr

/-! ### The defining sentences -/

section Sentences

/-- Reading a one-copy sentence inside the block replicated once. -/
noncomputable def onS1 (φ : peLang1.Sentence) :
    (peOrd.sum (pairBlock.replicate 1).lang).Sentence :=
  (pairBlock.oneLHom peOrd).onSentence φ

/-- Reading a two-copy sentence inside the block replicated twice. -/
noncomputable def onS2 (φ : peLang2.Sentence) :
    (peOrd.sum (pairBlock.replicate 2).lang).Sentence :=
  (pairBlock.twoLHom peOrd).onSentence φ

open Classical in
/-- A static choice on the tags. -/
noncomputable def tagS1 (b : Prop) : peLang1.Sentence := if b then ⊤ else ⊥

/-- **A mark of the instance, at an element**: the point is the element `x`, and
`x` carries the mark. -/
noncomputable def markS (r : Language.epr.Relations 1) : peLang1.Sentence :=
  Formula.iExs (Fin 1) (peF1 (Sum.inr 0) (Sum.inr 0) ⊓
    peLift1 (peMarkG r (Sum.inr 0)))

/-- **A binary relation of the instance, at two elements**. -/
noncomputable def binS (r : Language.epr.Relations 2) : peLang2.Sentence :=
  Formula.iExs (Fin 2) (peFA (Sum.inr 0) (Sum.inr 0) ⊓
    (peFB (Sum.inr 1) (Sum.inr 1) ⊓ peLift2 (peBinG r (Sum.inr 0) (Sum.inr 1))))

/-- **The first component of a pair**: the pair is `(x, y)` and the second point
is the element `x`. -/
noncomputable def fstS : peLang2.Sentence :=
  Formula.iExs (Fin 2) (peFA (Sum.inr 0) (Sum.inr 1) ⊓ peFB (Sum.inr 0) (Sum.inr 0))

/-- **The second component of a pair.** -/
noncomputable def sndS : peLang2.Sentence :=
  Formula.iExs (Fin 2) (peFA (Sum.inr 0) (Sum.inr 1) ⊓ peFB (Sum.inr 1) (Sum.inr 1))

/-- **The argument of a literal at a position**: the pair is a literal `l` and a
position `p`, the second point is the element `x`, and the encoding declares `x`
there. -/
noncomputable def argS : peLang2.Sentence :=
  Formula.iExs (Fin 3) (peFA (Sum.inr 0) (Sum.inr 1) ⊓
    (peFB (Sum.inr 2) (Sum.inr 2) ⊓
      peLift2 (peTerG Language.eprArgSym (Sum.inr 0) (Sum.inr 1) (Sum.inr 2))))

/-- **A pair belongs to an assignment**: the second point is the pair `(x, y)`
and the first, as a relation, holds of `x` and `y`. -/
noncomputable def memS : peLang2.Sentence :=
  Formula.iExs (Fin 2) (peFB (Sum.inr 0) (Sum.inr 1) ⊓ peFA (Sum.inr 0) (Sum.inr 1))

/-- The defining sentence of a unary symbol at a tag. -/
noncomputable def unT (r : Language.epr.Relations 1) : ETag → peLang1.Sentence
  | .elt => markS r
  | _ => ⊥

/-- The defining sentence of a binary symbol at a pair of tags: both points must
be elements. -/
noncomputable def binT (r : Language.epr.Relations 2) : ETag → ETag → peLang2.Sentence
  | .elt, .elt => binS r
  | _, _ => ⊥

/-- The defining sentence of the two component symbols. -/
noncomputable def compT (φ : peLang2.Sentence) : ETag → ETag → peLang2.Sentence
  | .pair, .elt => φ
  | _, _ => ⊥

/-- The defining sentence of the membership symbol. -/
noncomputable def memT : ETag → ETag → peLang2.Sentence
  | .asg, .pair => memS
  | _, _ => ⊥

open Classical in
/-- **The expansion whose points are the relations on the instance.** -/
noncomputable def eprExp : ExpExpansion Language.epr where
  Tag := ETag
  B := pairBlock
  E := Language.eprPt
  dom := domT
  relSentence {n} r τ :=
    match n, r with
    | _, .isElt => onS1 (tagS1 (τ 0 = ETag.elt))
    | _, .isPair => onS1 (tagS1 (τ 0 = ETag.pair))
    | _, .isAsg => onS1 (tagS1 (τ 0 = ETag.asg))
    | _, .evarE => onS1 (unT Language.eprEVarSym (τ 0))
    | _, .clE => onS1 (unT Language.eprClSym (τ 0))
    | _, .inClE => onS2 (binT Language.eprInClSym (τ 0) (τ 1))
    | _, .posLE => onS2 (binT Language.eprPosSym (τ 0) (τ 1))
    | _, .negLE => onS2 (binT Language.eprNegSym (τ 0) (τ 1))
    | _, .sigE => onS2 (binT Language.eprSigSym (τ 0) (τ 1))
    | _, .fstP => onS2 (compT fstS (τ 0) (τ 1))
    | _, .sndP => onS2 (compT sndS (τ 0) (τ 1))
    | _, .argP => onS2 (compT argS (τ 0) (τ 1))
    | _, .memP => onS2 (memT (τ 0) (τ 1))
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨ETag.asg, pairBlock.botAssign A, ?_⟩
    letI := pairBlock.structure₁ (L := peOrd) (pairBlock.botAssign A)
    exact Formula.realize_top.mpr trivial

end Sentences

/-! ### Reading the expansion at its points -/

section Reading

variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

variable (A) in
/-- The expanded structure, at the vocabulary of the points – equal to the
expansion's own by definition, but not syntactically, so instance search has to
be handed it. -/
@[instance_reducible]
noncomputable def eprPtStructure : Language.eprPt.Structure (eprExp.Map A) :=
  eprExp.mapStructure A

/-- Reading a unary symbol of the expanded vocabulary at one point. -/
theorem realize_one (rt : Language.eprPt.Relations 1) (φ : ETag → peLang1.Sentence)
    (h : ∀ τ : Fin 1 → ETag, eprExp.relSentence rt τ = onS1 (φ (τ 0)))
    (x : eprExp.Map A) :
    letI := eprPtStructure A
    (RelMap rt ![x] ↔
      @Sentence.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) x.1.2) (φ x.1.1)) := by
  letI := eprPtStructure A
  have h1 := eprExp.relMap_map rt ![x]
  rw [show eprExp.relSentence rt (fun i => (![x] i).1.1) =
    onS1 (φ ((![x] : Fin 1 → eprExp.Map A) 0).1.1) from h _] at h1
  exact h1.trans (pairBlock.realize_oneLHom (L := peOrd) _ _)

/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : Language.eprPt.Relations 2) (φ : ETag → ETag → peLang2.Sentence)
    (h : ∀ τ : Fin 2 → ETag, eprExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : eprExp.Map A) :
    letI := eprPtStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize peLang2 A
        (pairBlock.structure₂ (L := peOrd) x.1.2 y.1.2) (φ x.1.1 y.1.1)) := by
  letI := eprPtStructure A
  have h1 := eprExp.relMap_map rt ![x, y]
  rw [show eprExp.relSentence rt (fun i => (![x, y] i).1.1) =
    onS2 (φ ((![x, y] : Fin 2 → eprExp.Map A) 0).1.1
      ((![x, y] : Fin 2 → eprExp.Map A) 1).1.1) from h _] at h1
  exact h1.trans (pairBlock.realize_twoLHom (L := peOrd) _ _)

/-! ### The three kinds of point -/

theorem domHolds_elt (x : A) :
    ExpExpansion.DomHolds (X := eprExp)
      (ETag.elt, peAssign (fun y z : A => y = x ∧ z = x)) :=
  (realize_diagS _).mpr (peDiag_diag x)

theorem domHolds_pair (x y : A) :
    ExpExpansion.DomHolds (X := eprExp)
      (ETag.pair, peAssign (fun z w : A => z = x ∧ w = y)) :=
  (realize_pairS _).mpr (pePairRel_pair x y)

theorem domHolds_asg (R : A → A → Prop) :
    ExpExpansion.DomHolds (X := eprExp) (ETag.asg, peAssign R) := by
  letI := eprExp.B.structure₁ (L := peOrd) (peAssign R)
  exact Formula.realize_top.mpr trivial

/-- **The point an element is**: the diagonal singleton, tagged `elt`. -/
noncomputable def eltPt (x : A) : eprExp.Map A :=
  ⟨(ETag.elt, peAssign (fun y z : A => y = x ∧ z = x)), domHolds_elt x⟩

/-- **The point an ordered pair is**. -/
noncomputable def pairPt (x y : A) : eprExp.Map A :=
  ⟨(ETag.pair, peAssign (fun z w : A => z = x ∧ w = y)), domHolds_pair x y⟩

/-- **The point an assignment is**. -/
noncomputable def asgPt (R : A → A → Prop) : eprExp.Map A :=
  ⟨(ETag.asg, peAssign R), domHolds_asg R⟩

@[simp]
theorem eltPt_tag (x : A) : (eltPt x).1.1 = ETag.elt := rfl

@[simp]
theorem pairPt_tag (x y : A) : (pairPt x y).1.1 = ETag.pair := rfl

@[simp]
theorem asgPt_tag (R : A → A → Prop) : (asgPt R).1.1 = ETag.asg := rfl

theorem eltPt_injective : Function.Injective (eltPt (A := A)) := by
  intro x y h
  have h2 : (fun a b : A => a = x ∧ b = x) = (fun a b : A => a = y ∧ b = y) :=
    congrArg (fun p => peRel p.1.2) h
  have h3 := congrFun (congrFun h2 x) x
  exact (h3 ▸ (⟨rfl, rfl⟩ : x = x ∧ x = x)).1

/-- **Every point is an element, a pair or an assignment**: what the domain
sentences say, read back. -/
theorem cases_point (p : eprExp.Map A) :
    (∃ x, p = eltPt x) ∨ (∃ x y, p = pairPt x y) ∨ ∃ R, p = asgPt R := by
  obtain ⟨⟨t, ρ⟩, hdom⟩ := p
  match t with
  | ETag.elt =>
    obtain ⟨x, hx⟩ := (realize_diagS ρ).mp hdom
    refine Or.inl ⟨x, ExpExpansion.map_ext rfl ?_⟩
    refine peRel_injective ?_
    funext y z
    exact propext (hx y z)
  | ETag.pair =>
    obtain ⟨x, y, hxy⟩ := (realize_pairS ρ).mp hdom
    refine Or.inr (Or.inl ⟨x, y, ExpExpansion.map_ext rfl ?_⟩)
    refine peRel_injective ?_
    funext z w
    exact propext (hxy z w)
  | ETag.asg =>
    exact Or.inr (Or.inr ⟨peRel ρ, ExpExpansion.map_ext rfl (peAssign_peRel ρ).symm⟩)

end Reading

/-! ### What the defining sentences say -/

section SentenceRealize

variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

@[simp]
theorem realize_tagS1 (b : Prop) (ρ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) (tagS1 b) ↔ b) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  classical
  by_cases hb : b
  · rw [tagS1, if_pos hb]
    exact iff_of_true (Formula.realize_top.mpr trivial) hb
  · rw [tagS1, if_neg hb]
    exact iff_of_false (fun h => Formula.realize_bot.mp h) hb

@[simp]
theorem realize_markS (r : Language.epr.Relations 1) (ρ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang1 A (pairBlock.structure₁ (L := peOrd) ρ) (markS r) ↔
      ∃ x, peRel ρ x x ∧ RelMap r ![x]) := by
  letI := pairBlock.structure₁ (L := peOrd) ρ
  simp only [markS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peF1, realize_peLift1, realize_peMarkG, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩

@[simp]
theorem realize_binS (r : Language.epr.Relations 2) (ρ σ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) (binS r) ↔
      ∃ x y, peRel ρ x x ∧ peRel σ y y ∧ RelMap r ![x, y]) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [binS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peFA, realize_peFB, realize_peLift2, realize_peBinG, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨x, y, hx⟩ => ⟨![x, y], hx⟩⟩

@[simp]
theorem realize_fstS (ρ σ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) fstS ↔
      ∃ x y, peRel ρ x y ∧ peRel σ x x) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [fstS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peFA, realize_peFB, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨x, y, hx⟩ => ⟨![x, y], hx⟩⟩

@[simp]
theorem realize_sndS (ρ σ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) sndS ↔
      ∃ x y, peRel ρ x y ∧ peRel σ y y) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [sndS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peFA, realize_peFB, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨x, y, hx⟩ => ⟨![x, y], hx⟩⟩

@[simp]
theorem realize_argS (ρ σ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) argS ↔
      ∃ l p x, peRel ρ l p ∧ peRel σ x x ∧ ArgG l p x) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [argS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peFA, realize_peFB, realize_peLift2, realize_peTerG, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, w 2, hw⟩, fun ⟨l, p, x, hx⟩ => ⟨![l, p, x], hx⟩⟩

@[simp]
theorem realize_memS (ρ σ : pairBlock.Assignment A) :
    (@Sentence.Realize peLang2 A (pairBlock.structure₂ (L := peOrd) ρ σ) memS ↔
      ∃ x y, peRel σ x y ∧ peRel ρ x y) := by
  letI := pairBlock.structure₂ (L := peOrd) ρ σ
  simp only [memS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_peFA, realize_peFB, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨x, y, hx⟩ => ⟨![x, y], hx⟩⟩

end SentenceRealize

/-! ### What the symbols say at the points -/

section PointRealize

variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

@[simp]
theorem peRel_eltPt (x y z : A) : peRel (eltPt x).1.2 y z ↔ (y = x ∧ z = x) := Iff.rfl

@[simp]
theorem peRel_pairPt (x y z w : A) : peRel (pairPt x y).1.2 z w ↔ (z = x ∧ w = y) := Iff.rfl

@[simp]
theorem peRel_asgPt (R : A → A → Prop) (x y : A) : peRel (asgPt R).1.2 x y ↔ R x y := Iff.rfl

theorem realize_isElt (p : eprExp.Map A) :
    letI := eprPtStructure A
    (RelMap Language.peIsEltSym ![p] ↔ p.1.1 = ETag.elt) := by
  letI := eprPtStructure A
  exact (realize_one Language.peIsEltSym (fun t => tagS1 (t = ETag.elt))
    (fun _ => rfl) p).trans (realize_tagS1 _ _)

theorem realize_isPair (p : eprExp.Map A) :
    letI := eprPtStructure A
    (RelMap Language.peIsPairSym ![p] ↔ p.1.1 = ETag.pair) := by
  letI := eprPtStructure A
  exact (realize_one Language.peIsPairSym (fun t => tagS1 (t = ETag.pair))
    (fun _ => rfl) p).trans (realize_tagS1 _ _)

theorem realize_isAsg (p : eprExp.Map A) :
    letI := eprPtStructure A
    (RelMap Language.peIsAsgSym ![p] ↔ p.1.1 = ETag.asg) := by
  letI := eprPtStructure A
  exact (realize_one Language.peIsAsgSym (fun t => tagS1 (t = ETag.asg))
    (fun _ => rfl) p).trans (realize_tagS1 _ _)

/-- A unary mark of the instance, read at the point of an element. -/
theorem realize_un (rt : Language.eprPt.Relations 1) (r : Language.epr.Relations 1)
    (h : ∀ τ : Fin 1 → ETag, eprExp.relSentence rt τ = onS1 (unT r (τ 0))) (x : A) :
    letI := eprPtStructure A
    (RelMap rt ![eltPt x] ↔ RelMap r ![x]) := by
  letI := eprPtStructure A
  refine (realize_one rt (unT r) h (eltPt x)).trans ?_
  rw [show (eltPt x).1.1 = ETag.elt from rfl, unT]
  refine (realize_markS r _).trans ⟨fun ⟨y, hy, hr⟩ => ?_, fun hr => ⟨x, ⟨rfl, rfl⟩, hr⟩⟩
  exact ((peRel_eltPt x y y).mp hy).1 ▸ hr

/-- A binary relation of the instance, read at the points of two elements. -/
theorem realize_bin (rt : Language.eprPt.Relations 2) (r : Language.epr.Relations 2)
    (h : ∀ τ : Fin 2 → ETag, eprExp.relSentence rt τ = onS2 (binT r (τ 0) (τ 1))) (x y : A) :
    letI := eprPtStructure A
    (RelMap rt ![eltPt x, eltPt y] ↔ RelMap r ![x, y]) := by
  letI := eprPtStructure A
  refine (realize_two rt (binT r) h (eltPt x) (eltPt y)).trans ?_
  rw [show (eltPt x).1.1 = ETag.elt from rfl, show (eltPt y).1.1 = ETag.elt from rfl, binT]
  refine (realize_binS r _ _).trans ⟨fun ⟨a, b, ha, hb, hr⟩ => ?_,
    fun hr => ⟨x, y, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hr⟩⟩
  rw [← ((peRel_eltPt x a a).mp ha).1, ← ((peRel_eltPt y b b).mp hb).1]
  exact hr

theorem realize_evarE (x : A) :
    letI := eprPtStructure A
    (RelMap Language.peEVarSym ![eltPt x] ↔ EVarG x) :=
  realize_un Language.peEVarSym Language.eprEVarSym (fun _ => rfl) x

theorem realize_clE (c : A) :
    letI := eprPtStructure A
    (RelMap Language.peClSym ![eltPt c] ↔ ClauseG c) :=
  realize_un Language.peClSym Language.eprClSym (fun _ => rfl) c

theorem realize_inClE (c l : A) :
    letI := eprPtStructure A
    (RelMap Language.peInClSym ![eltPt c, eltPt l] ↔ InClG c l) :=
  realize_bin Language.peInClSym Language.eprInClSym (fun _ => rfl) c l

theorem realize_posLE (l s : A) :
    letI := eprPtStructure A
    (RelMap Language.pePosSym ![eltPt l, eltPt s] ↔ PosG l s) :=
  realize_bin Language.pePosSym Language.eprPosSym (fun _ => rfl) l s

theorem realize_negLE (l s : A) :
    letI := eprPtStructure A
    (RelMap Language.peNegSym ![eltPt l, eltPt s] ↔ NegG l s) :=
  realize_bin Language.peNegSym Language.eprNegSym (fun _ => rfl) l s

theorem realize_sigE (s p : A) :
    letI := eprPtStructure A
    (RelMap Language.peSigSym ![eltPt s, eltPt p] ↔ SigG s p) :=
  realize_bin Language.peSigSym Language.eprSigSym (fun _ => rfl) s p

theorem realize_fstP (x y z : A) :
    letI := eprPtStructure A
    (RelMap Language.peFstSym ![pairPt x y, eltPt z] ↔ z = x) := by
  letI := eprPtStructure A
  refine (realize_two Language.peFstSym (compT fstS) (fun _ => rfl) (pairPt x y) (eltPt z)).trans ?_
  rw [show (pairPt x y).1.1 = ETag.pair from rfl, show (eltPt z).1.1 = ETag.elt from rfl, compT]
  refine (realize_fstS _ _).trans ⟨fun ⟨a, b, hab, ha⟩ => ?_, fun hz => ⟨x, y, ⟨rfl, rfl⟩, ?_⟩⟩
  · obtain ⟨rfl, rfl⟩ := (peRel_pairPt x y a b).mp hab
    exact ((peRel_eltPt z a a).mp ha).1.symm
  · exact ⟨hz.symm, hz.symm⟩

theorem realize_sndP (x y z : A) :
    letI := eprPtStructure A
    (RelMap Language.peSndSym ![pairPt x y, eltPt z] ↔ z = y) := by
  letI := eprPtStructure A
  refine (realize_two Language.peSndSym (compT sndS) (fun _ => rfl) (pairPt x y) (eltPt z)).trans ?_
  rw [show (pairPt x y).1.1 = ETag.pair from rfl, show (eltPt z).1.1 = ETag.elt from rfl, compT]
  refine (realize_sndS _ _).trans ⟨fun ⟨a, b, hab, hb⟩ => ?_, fun hz => ⟨x, y, ⟨rfl, rfl⟩, ?_⟩⟩
  · obtain ⟨rfl, rfl⟩ := (peRel_pairPt x y a b).mp hab
    exact ((peRel_eltPt z b b).mp hb).1.symm
  · exact ⟨hz.symm, hz.symm⟩

theorem realize_argP (l p x : A) :
    letI := eprPtStructure A
    (RelMap Language.peArgSym ![pairPt l p, eltPt x] ↔ ArgG l p x) := by
  letI := eprPtStructure A
  refine (realize_two Language.peArgSym (compT argS) (fun _ => rfl) (pairPt l p) (eltPt x)).trans ?_
  rw [show (pairPt l p).1.1 = ETag.pair from rfl, show (eltPt x).1.1 = ETag.elt from rfl, compT]
  refine (realize_argS _ _).trans ⟨fun ⟨a, b, c, hab, hc, harg⟩ => ?_,
    fun harg => ⟨l, p, x, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, harg⟩⟩
  obtain ⟨rfl, rfl⟩ := (peRel_pairPt l p a b).mp hab
  exact ((peRel_eltPt x c c).mp hc).1 ▸ harg

theorem realize_memP (R : A → A → Prop) (x y : A) :
    letI := eprPtStructure A
    (RelMap Language.peMemSym ![asgPt R, pairPt x y] ↔ R x y) := by
  letI := eprPtStructure A
  refine (realize_two Language.peMemSym memT (fun _ => rfl) (asgPt R) (pairPt x y)).trans ?_
  rw [show (asgPt R).1.1 = ETag.asg from rfl, show (pairPt x y).1.1 = ETag.pair from rfl, memT]
  refine (realize_memS _ _).trans ⟨fun ⟨a, b, hab, hr⟩ => ?_, fun hr => ⟨x, y, ⟨rfl, rfl⟩, hr⟩⟩
  obtain ⟨rfl, rfl⟩ := (peRel_pairPt x y a b).mp hab
  exact hr

end PointRealize

end Epr

end DescriptiveComplexity
