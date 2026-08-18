/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Double
import DescriptiveComplexity.SecondOrderTransitiveClosure

/-!
# Reading the instance inside the doubled universe

`DescriptiveComplexity.Problems.Wide.Double` runs the machinery at a universe
that is never a singleton, at the price of a universe that is no longer the
instance. This file pays that price for **one sentence at a time**: a sentence
about the instance's ordered vocabulary, expanded by a block, is renamed into the
extended vocabulary (`DescriptiveComplexity.Draw.newBlockLHom`) and relativized to
the mark (`DescriptiveComplexity.relativizeTo`), and then says in the doubled
universe exactly what it said in the instance
(`DescriptiveComplexity.Draw.realize_relOldBlock`).

The block assignment travels with it. An assignment of the instance is extended
to the doubled universe by `DescriptiveComplexity.Draw.extAssign` – it holds of a
tuple exactly when every entry is marked and the entries' elements satisfy it –
and that is the shape the *support* condition of the relativized expansion will
pin down: an assignment over the doubled universe that only ever holds of marked
tuples is an assignment of the instance and nothing more.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### The lexicographic order, on the doubled universe -/

section Order

variable {A : Type} [LinearOrder A]

/-- On a one-coordinate tuple the lexicographic order is the order itself. -/
theorem tupLeLex_one (u v : Fin 1 → A) : tupLeLex u v ↔ u 0 ≤ v 0 := by
  constructor
  · rintro (rfl | ⟨j, -, hj⟩)
    · exact le_rfl
    · rw [Subsingleton.elim (0 : Fin 1) j]
      exact hj.le
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact Or.inr ⟨0, fun i hi => absurd hi (Fin.not_lt_zero i), hlt⟩
    · exact Or.inl (funext fun j => by rw [Subsingleton.elim j 0]; exact heq)

/-- Two points of the doubled universe with the same tag compare as their
elements do. -/
theorem tagTupleLe_dblPt {L : Language.{0, 0}} [L.IsRelational] [L.Structure A]
    (b : Bool) (a a' : A) :
    tagTupleLe (dblPt (L := L) b a) (dblPt (L := L) b a') ↔ a ≤ a' := by
  rw [tagTupleLe]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (lt_irrefl b)
    · exact (tupLeLex_one _ _).mp h
  · intro h
    exact Or.inr ⟨rfl, (tupLeLex_one _ _).mpr h⟩

end Order

/-! ### The renaming, and the mark -/

section RelBlock

variable {L : Language.{0, 0}} [L.IsRelational] (B : SOBlock)

/-- **Renaming a sentence about the instance** – over its ordered vocabulary,
expanded by a block – into the extended vocabulary. -/
def newBlockLHom : ((L.sum Language.order).sum B.lang) →ᴸ
    (((newLang L).sum Language.order).sum B.lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl g) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl s) => Sum.inl (Sum.inl (Sum.inl s))
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
    | Sum.inr s => Sum.inr s

/-- **The mark of the instance's own elements**, in the block-expanded extended
vocabulary. -/
abbrev oldGuard : (((newLang L).sum Language.order).sum B.lang).Relations 1 :=
  Sum.inl (Sum.inl (Sum.inr Language.oldSym))

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The order the reduction puts on the doubled universe: the instance's copy
and the junk copy, each in the instance's order. -/
noncomputable instance dblOrder : LinearOrder ((dblInterp L).Map A) := tagTupleOrder

variable {B}

/-- **An assignment of the instance, extended to the doubled universe**: it
holds of a tuple exactly when every entry is marked and the entries' elements
satisfy it. -/
def extAssign (ρ₀ : B.Assignment A) : B.Assignment ((dblInterp L).Map A) :=
  fun i w => (∀ j, (w j).1 = false) ∧ ρ₀ i fun j => (w j).2 0

/-- **An assignment of the doubled universe, restricted to the instance.** -/
def resAssign (ρ : B.Assignment ((dblInterp L).Map A)) : B.Assignment A :=
  fun i w => ρ i fun j => dblPt false (w j)

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
@[simp] theorem resAssign_extAssign (ρ₀ : B.Assignment A) :
    resAssign (extAssign (L := L) ρ₀) = ρ₀ := by
  funext i w
  exact propext ⟨fun h => h.2, fun h => ⟨fun _ => rfl, h⟩⟩

/-- **An assignment is supported** when it only ever holds of marked tuples:
the condition the relativized expansion pins down, and exactly what makes an
assignment of the doubled universe an assignment of the instance. -/
def Supported (ρ : B.Assignment ((dblInterp L).Map A)) : Prop :=
  ∀ (i : B.ι) (w : Fin (B.arity i) → (dblInterp L).Map A), ρ i w → ∀ j, (w j).1 = false

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
theorem extAssign_resAssign {ρ : B.Assignment ((dblInterp L).Map A)} (h : Supported ρ) :
    extAssign (resAssign ρ) = ρ := by
  funext i w
  refine propext ⟨fun hw => ?_, fun hw => ⟨h i w hw, ?_⟩⟩
  · have : (fun j => dblPt (L := L) false ((w j).2 0)) = w :=
      funext fun j => by rw [dblPt_eta (w j), hw.1 j]
    exact this ▸ hw.2
  · have : (fun j => dblPt (L := L) false ((w j).2 0)) = w :=
      funext fun j => by rw [dblPt_eta (w j), h i w hw j]
    exact this ▸ hw

/-! ### The transport

The structures the transport is about are built from block assignments, so they
are never instances: every statement below names them. -/

section Transport

variable (L B)

/-- The marked part of the doubled universe, as a substructure: the vocabulary
is relational, so there is nothing to be closed under. -/
def oldSubD (A : Type) [L.Structure A] [LinearOrder A] (ρ₀ : B.Assignment A) :
    @Language.Substructure (((newLang L).sum Language.order).sum B.lang)
      ((dblInterp L).Map A) (B.structure₁ (extAssign ρ₀)) :=
  letI := B.structure₁ (L := (newLang L).sum Language.order) (extAssign (L := L) ρ₀)
  { carrier := {p | p.1 = false}
    fun_mem := fun {_} f _ _ => isEmptyElim f }

variable {L B}
variable {A : Type} [L.Structure A] [LinearOrder A] (ρ₀ : B.Assignment A)

/-- The marked part is the instance: an element and its marked copy. -/
noncomputable def oldSubDEquiv : A ≃ (oldSubD L B A ρ₀) where
  toFun a := ⟨dblPt false a, rfl⟩
  invFun x := (x : (dblInterp L).Map A).2 0
  left_inv _ := rfl
  right_inv x := Subtype.ext (((dblPt_eta (x : (dblInterp L).Map A)).trans
    (congrArg (fun b => dblPt b ((x : (dblInterp L).Map A).2 0)) x.2)).symm)

/-- **The marked part carries the instance**, over the instance's own ordered
vocabulary expanded by the block: an isomorphism, the reduct of the induced
structure along the renaming being what the extended assignment restricts to. -/
noncomputable def oldSubDLEquiv :
    @Language.Equiv ((L.sum Language.order).sum B.lang) A (oldSubD L B A ρ₀)
      (B.structure₁ ρ₀) ((newBlockLHom (L := L) B).reduct (oldSubD L B A ρ₀)) :=
  letI := B.structure₁ (L := (newLang L).sum Language.order) (extAssign (L := L) ρ₀)
  letI := (newBlockLHom (L := L) B).reduct (oldSubD L B A ρ₀)
  letI := B.structure₁ (L := L.sum Language.order) ρ₀
  { toEquiv := oldSubDEquiv ρ₀
    map_fun' := fun {_} f _ => isEmptyElim f
    map_rel' := fun {n} r =>
      match n, r with
      | _, Sum.inl (Sum.inl s) => fun x => by
        change RelMap (newSym s) (fun i => dblPt (L := L) false (x i)) ↔ _
        rw [relMap_dbl_inl]
        exact ⟨fun h => h.2, fun h => ⟨fun _ => rfl, h⟩⟩
      | _, Sum.inl (Sum.inr .le) => fun x => by
        change (dblPt (L := L) false (x 0) : (dblInterp L).Map A) ≤
          dblPt (L := L) false (x 1) ↔ (x 0 ≤ x 1)
        exact (tagTupleLe_iff_le _ _).symm.trans
          (tagTupleLe_dblPt (L := L) false (x 0) (x 1))
      | _, Sum.inr s => fun x => by
        change extAssign (L := L) ρ₀ s.1
          (fun j => dblPt false (x (Fin.cast s.2 j))) ↔ _
        exact ⟨fun h => h.2, fun h => ⟨fun _ => rfl, h⟩⟩ }

/-- **Reading a sentence about the instance inside the doubled universe**: its
renaming, relativized to the mark, says of the extended assignment exactly what
it said of the assignment. -/
theorem realize_relOldBlock (σ : ((L.sum Language.order).sum B.lang).Sentence) :
    @Sentence.Realize _ ((dblInterp L).Map A) (B.structure₁ (extAssign ρ₀))
        (relativizeTo (oldGuard (L := L) B) ((newBlockLHom B).onSentence σ)) ↔
      @Sentence.Realize _ A (B.structure₁ ρ₀) σ := by
  let := B.structure₁ (L := (newLang L).sum Language.order) (extAssign (L := L) ρ₀)
  let := (newBlockLHom (L := L) B).reduct (oldSubD L B A ρ₀)
  let := B.structure₁ (L := L.sum Language.order) ρ₀
  have hS : ∀ x : (dblInterp L).Map A,
      x ∈ oldSubD L B A ρ₀ ↔ RelMap (oldGuard (L := L) B) ![x] := by
    intro x
    have hb : RelMap (oldGuard (L := L) B) ![x] ↔ RelMap (oldNewSym L) ![x] := Iff.rfl
    rw [hb, relMap_dbl_old]
    exact Iff.rfl
  have h1 := realize_relativizeTo (R := oldGuard (L := L) B) (oldSubD L B A ρ₀) hS
    ((newBlockLHom B).onSentence σ) (default : Empty → (oldSubD L B A ρ₀))
    (default : Fin 0 → (oldSubD L B A ρ₀))
  have h2 := LHom.realize_onSentence (M := (oldSubD L B A ρ₀)) (newBlockLHom B) σ
  have h3 := realize_sentence_of_equiv (oldSubDLEquiv ρ₀) σ
  refine Iff.trans ?_ (h1.trans (h2.trans h3.symm))
  exact iff_of_eq (congrArg₂
    (fun v xs => @BoundedFormula.Realize _ ((dblInterp L).Map A) _ _ 0
      (relativizeTo (oldGuard (L := L) B) ((newBlockLHom B).onSentence σ)) v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end Transport

/-! ### The support condition, as a sentence

An assignment of the doubled universe is an assignment of the instance exactly
when it never holds of an unmarked entry. That is one sentence per relation
variable of the block, and it is the conjunct the relativized expansion's domain
sentence carries beside the relativized original. -/

section Support

variable (L B)

/-- A relation variable of the block, as a symbol of the expanded extended
vocabulary: named, because a raw `Sum.inr` is not recognized at the transparency
`rw` matches at. -/
abbrev blkSym (i : B.ι) :
    (((newLang L).sum Language.order).sum B.lang).Relations (B.arity i) :=
  Sum.inr ⟨i, rfl⟩

/-- **One relation variable holds only of marked tuples**, as a sentence. -/
noncomputable def suppAt (i : B.ι) :
    (((newLang L).sum Language.order).sum B.lang).Sentence :=
  Formula.iAlls (Fin (B.arity i))
    ((Relations.formula (blkSym L B i) fun k => Term.var (Sum.inr k)) ⟹
      listInf ((List.finRange (B.arity i)).map fun j =>
        Relations.formula₁ (oldGuard (L := L) B) (Term.var (Sum.inr j))))

open Classical in
/-- **The support condition**, as a sentence: every relation variable of the
block holds only of marked tuples. -/
noncomputable def suppSentence : (((newLang L).sum Language.order).sum B.lang).Sentence :=
  letI := Fintype.ofFinite B.ι
  listInf ((Finset.univ : Finset B.ι).toList.map (suppAt L B))

variable {L B}

end Support

end RelBlock

/-! ### The marked part of an arbitrary extended structure

The doubled universe is not the only structure the relativized expansion will be
read at: `FirstOrder.Language.ExpExpansion` demands its domain sentence be
satisfiable at *every* structure, so the marked part has to be an instance in its
own right wherever there is one. -/

section MarkPart

variable {L : Language.{0, 0}} [L.IsRelational]
variable {M : Type} [(newLang L).Structure M]

/-- **The marked part** of an extended structure. A `def`, so that its instances
below are found by their own head rather than by the subtype's. -/
def MarkPart (L : Language.{0, 0}) [L.IsRelational] (M : Type)
    [(newLang L).Structure M] : Type :=
  {x : M // RelMap (oldNewSym L) ![x]}

/-- The element a marked point is. -/
def MarkPart.val (x : MarkPart L M) : M := x.1

theorem MarkPart.isMark (x : MarkPart L M) : RelMap (oldNewSym L) ![x.val] := x.2

theorem MarkPart.ext {x y : MarkPart L M} (h : x.val = y.val) : x = y := Subtype.ext h

/-- A marked element, as a point of the marked part. -/
def MarkPart.mk (x : M) (h : RelMap (oldNewSym L) ![x]) : MarkPart L M := ⟨x, h⟩

@[simp] theorem MarkPart.val_mk (x : M) (h : RelMap (oldNewSym L) ![x]) :
    (MarkPart.mk x h).val = x := rfl

instance [LinearOrder M] : LinearOrder (MarkPart L M) :=
  inferInstanceAs (LinearOrder {x : M // RelMap (oldNewSym L) ![x]})

instance [Finite M] : Finite (MarkPart L M) :=
  inferInstanceAs (Finite {x : M // RelMap (oldNewSym L) ![x]})

/-- The instance's own relations, on its marked part. -/
instance markStructure : L.Structure (MarkPart L M) where
  funMap f := isEmptyElim f
  RelMap {_} r x := RelMap (newSym r) fun i => (x i).val

variable (B : SOBlock)

/-- **An assignment of the marked part, extended to the whole structure**: it
holds of a tuple exactly when every entry is marked and the marked entries
satisfy it. -/
def extAssignM (ρ₀ : B.Assignment (MarkPart L M)) : B.Assignment M :=
  fun i w => ∃ h : ∀ j, RelMap (oldNewSym L) ![w j], ρ₀ i fun j => MarkPart.mk (w j) (h j)

/-- The marked part, as a substructure of the block-expanded extended
vocabulary. -/
def markSub [LinearOrder M] (ρ : B.Assignment M) :
    @Language.Substructure (((newLang L).sum Language.order).sum B.lang) M
      (B.structure₁ ρ) :=
  letI := B.structure₁ (L := (newLang L).sum Language.order) ρ
  { carrier := {x | RelMap (oldNewSym L) ![x]}
    fun_mem := fun {_} f _ _ => isEmptyElim f }

variable [LinearOrder M]

/-- **The marked part carries the instance it marks**: the identity map is an
isomorphism from the marked part, with the structures above, onto the
substructure with the reduct of its induced structure. -/
noncomputable def markSubLEquiv (ρ₀ : B.Assignment (MarkPart L M)) :
    @Language.Equiv ((L.sum Language.order).sum B.lang) (MarkPart L M)
      (markSub (L := L) B (extAssignM B ρ₀)) (B.structure₁ ρ₀)
      ((newBlockLHom (L := L) B).reduct (markSub (L := L) B (extAssignM B ρ₀))) :=
  letI := B.structure₁ (L := (newLang L).sum Language.order) (extAssignM B ρ₀)
  letI := (newBlockLHom (L := L) B).reduct (markSub (L := L) B (extAssignM B ρ₀))
  letI := B.structure₁ (L := L.sum Language.order) ρ₀
  { toEquiv :=
      { toFun := fun x => ⟨x.val, x.isMark⟩
        invFun := fun x => MarkPart.mk (x : M) x.2
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    map_fun' := fun {_} f _ => isEmptyElim f
    map_rel' := fun {n} r =>
      match n, r with
      | _, Sum.inl (Sum.inl s) => fun x => Iff.rfl
      | _, Sum.inl (Sum.inr .le) => fun x => Iff.rfl
      | _, Sum.inr s => fun x => by
        change extAssignM (L := L) B ρ₀ s.1 (fun j => (x (Fin.cast s.2 j)).val) ↔ _
        exact ⟨fun h => h.2, fun h => ⟨fun j => (x (Fin.cast s.2 j)).isMark, h⟩⟩ }

/-- **Reading a sentence about the marked part inside the structure**: its
renaming, relativized to the mark, says of the extended assignment exactly what
it said of the assignment. -/
theorem realize_relOldMark (ρ₀ : B.Assignment (MarkPart L M))
    (σ : ((L.sum Language.order).sum B.lang).Sentence) :
    @Sentence.Realize _ M (B.structure₁ (extAssignM B ρ₀))
        (relativizeTo (oldGuard (L := L) B) ((newBlockLHom B).onSentence σ)) ↔
      @Sentence.Realize _ (MarkPart L M) (B.structure₁ ρ₀) σ := by
  let := B.structure₁ (L := (newLang L).sum Language.order) (extAssignM (L := L) B ρ₀)
  let := (newBlockLHom (L := L) B).reduct (markSub (L := L) B (extAssignM B ρ₀))
  let := B.structure₁ (L := L.sum Language.order) ρ₀
  have hS : ∀ x : M, x ∈ markSub (L := L) B (extAssignM B ρ₀) ↔ RelMap (oldGuard (L := L) B) ![x] :=
    fun _ => Iff.rfl
  have h1 := realize_relativizeTo (R := oldGuard (L := L) B)
    (markSub (L := L) B (extAssignM B ρ₀)) hS ((newBlockLHom B).onSentence σ)
    (default : Empty → (markSub (L := L) B (extAssignM B ρ₀)))
    (default : Fin 0 → (markSub (L := L) B (extAssignM B ρ₀)))
  have h2 := LHom.realize_onSentence (M := (markSub (L := L) B (extAssignM B ρ₀)))
    (newBlockLHom (L := L) B) σ
  have h3 := realize_sentence_of_equiv (markSubLEquiv B ρ₀) σ
  refine Iff.trans ?_ (h1.trans (h2.trans h3.symm))
  exact iff_of_eq (congrArg₂
    (fun v xs => @BoundedFormula.Realize _ M _ _ 0
      (relativizeTo (oldGuard (L := L) B) ((newBlockLHom B).onSentence σ)) v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

omit [LinearOrder M] in
/-- An extended assignment is supported: nothing but marked tuples. -/
theorem supported_extAssignM (ρ₀ : B.Assignment (MarkPart L M)) :
    ∀ (i : B.ι) (w : Fin (B.arity i) → M), extAssignM B ρ₀ i w →
      ∀ j, RelMap (oldNewSym L) ![w j] :=
  fun _ _ h j => h.1 j

omit [L.IsRelational] in
/-- **The support condition, read**: an assignment satisfies the support
sentence exactly when it never holds of an unmarked entry. -/
theorem realize_suppAt (ρ : B.Assignment M) (i : B.ι) :
    @Sentence.Realize _ M (B.structure₁ ρ) (suppAt L B i) ↔
      ∀ w : Fin (B.arity i) → M, ρ i w → ∀ j, RelMap (oldNewSym L) ![w j] := by
  let := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [suppAt]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel, Term.realize_var, Sum.elim_inr, realize_listInf,
    List.mem_map, List.mem_finRange, true_and, forall_exists_index]
  refine forall_congr' fun w => imp_congr Iff.rfl ?_
  constructor
  · intro h j
    have hj := h _ j rfl
    rw [Formula.realize_rel₁] at hj
    exact hj
  · rintro h ψ j rfl
    rw [Formula.realize_rel₁]
    exact h j

omit [L.IsRelational] in
theorem realize_suppSentence (ρ : B.Assignment M) :
    @Sentence.Realize _ M (B.structure₁ ρ) (suppSentence L B) ↔
      ∀ (i : B.ι) (w : Fin (B.arity i) → M), ρ i w → ∀ j, RelMap (oldNewSym L) ![w j] := by
  classical
  let := Fintype.ofFinite B.ι
  let := B.structure₁ (L := (newLang L).sum Language.order) ρ
  rw [suppSentence]
  simp only [Sentence.Realize, realize_listInf, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro h i w hw j
    exact ((realize_suppAt B ρ i).mp (h _ i rfl)) w hw j
  · rintro h ψ i rfl
    exact (realize_suppAt B ρ i).mpr fun w hw j => h i w hw j

end MarkPart

end Draw

end DescriptiveComplexity
