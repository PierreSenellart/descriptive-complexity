/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewPoint
import DescriptiveComplexity.SecondOrderNewMeansB
import DescriptiveComplexity.SecondOrderNewOrdered
import DescriptiveComplexity.SubstFormula

/-!
# The block a problem over an expansion is guessed in

`NEXPTIME ⊆ ∃SO[new, exp c d]` rewrites a `Σ₁` definition over an exponential
expansion as a `Σ₁` definition with value invention. Everything the rewritten
sentence guesses goes into **one** second-order block, and this file is where
that block is fixed and its symbols named:

* the **order** on the original elements, which the expansion's sentences need
  and the extended universe has none of – so the block is a
  `DescriptiveComplexity.SOBlock.withOrder` and
  `DescriptiveComplexity.extLinearGuard` is its guard;
* the **meanings**, one per variable of the expansion's block *and one per tag*
  – a tag is a nullary variable, so its meaning relation is unary, “this value
  carries this tag”;
* the source problem's own `Σ₁` block, whose variables range over the points of
  the expansion and are therefore guessed over the extended universe and read at
  the values that are points.

What the file proves is that an assignment of that block reads as the data the
translations of `DescriptiveComplexity.SecondOrderNewRead` and
`DescriptiveComplexity.SecondOrderNewPoint` ask for
(`DescriptiveComplexity.pullPointOn`), given only that its order part is a
linear order of the original elements.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure ExpExpansion

variable {L : Language.{0, 0}} [L.IsRelational] (X : ExpExpansion L) (C : SOBlock)

/-! ### The block -/

/-- The expansion's block with one nullary variable per tag: what an invented
value has to stand for is an assignment of *this*, the tag included. -/
abbrev taggedBlock : SOBlock :=
  SOBlock.cons X.B (tagBits X.Tag)

/-- Everything the sentence guesses besides the order: the meanings of the
tagged block, and the source problem's own block. -/
abbrev guessBlock : SOBlock :=
  SOBlock.cons (meanBlockB (taggedBlock X)) C

/-- **The block**: the order variable, the meanings, and the source problem's
block. -/
abbrev pullBlock : SOBlock :=
  (guessBlock X C).withOrder

/-- The vocabulary the guessed sentence is written in. -/
abbrev pullLang : Language.{0, 0} :=
  (newLang L).sum (pullBlock X C).lang

/-! ### The symbols -/

/-- The meaning relation of a variable of the expansion's block. -/
def pullMeanSym (i : X.B.ι) : (pullLang X C).Relations (X.B.arity i + 1) :=
  Sum.inr ⟨Sum.inr (Sum.inl (Sum.inl i)), rfl⟩

/-- The meaning relation of a tag: unary, the tag being a nullary variable. -/
def pullTagSym (t : X.Tag) : (pullLang X C).Relations 1 :=
  Sum.inr ⟨Sum.inr (Sum.inl (Sum.inr t)), rfl⟩

/-- A variable of the source problem's own block. -/
def pullCertSym (j : C.ι) : (pullLang X C).Relations (C.arity j) :=
  Sum.inr ⟨Sum.inr (Sum.inr j), rfl⟩

/-- The symbols the translations of a defining sentence use. -/
def pullReadSyms : ReadSyms L X.B (pullLang X C) where
  base r := Sum.inl (Sum.inl r)
  ord := ordVarSym (newLang L) (guessBlock X C)
  mean := pullMeanSym X C

/-- The symbols the point formulas use. -/
def pullPointSyms : PointSyms L X (pullLang X C) where
  read := pullReadSyms X C
  tag := pullTagSym X C
  old := extOldSym L (guessBlock X C)

/-! ### What an assignment of the block reads as -/

section Reading

variable {X C} {A : Type} [L.Structure A] {m : ℕ}
variable (ρ : (pullBlock X C).Assignment (A ⊕ Fin m))

/-- The assignment of the expansion's block that an invented value means. -/
def pullMeans (v : A ⊕ Fin m) : X.B.Assignment A :=
  fun i ts => ρ (Sum.inr (Sum.inl (Sum.inl i))) (Fin.cases v fun j => Sum.inl (ts j))

/-- The tags an invented value carries. -/
def pullTags (v : A ⊕ Fin m) (t : X.Tag) : Prop :=
  ρ (Sum.inr (Sum.inl (Sum.inr t))) fun _ => v

/-- The order the order variable carries, as a relation on the instance. -/
def pullLe (a b : A) : Prop :=
  ρ (Sum.inl ()) ![Sum.inl a, Sum.inl b]

/-- The linear order the guard's order variable carries. -/
@[instance_reducible]
noncomputable def pullLinearOrder (hrefl : ∀ a : A, pullLe ρ a a)
    (htrans : ∀ a b c : A, pullLe ρ a b → pullLe ρ b c → pullLe ρ a c)
    (hanti : ∀ a b : A, pullLe ρ a b → pullLe ρ b a → a = b)
    (htotal : ∀ a b : A, pullLe ρ a b ∨ pullLe ρ b a) : LinearOrder A :=
  linearOrderOfGuard (fun w => pullLe ρ (w 0) (w 1)) hrefl
    (fun a b c => htrans a b c) (fun a b => hanti a b) fun a b => htotal a b

private theorem vec_eta₂ {M : Type} (w : Fin 2 → M) : ![w 0, w 1] = w := by
  funext j
  fin_cases j <;> simp

/-- **An assignment of the block reads as the data the translations ask for**:
its meaning variables give each invented value an assignment of the expansion's
block, its tag variables the tags it carries, and its order variable the order
of the instance – the last being a hypothesis, since which linear order the
instance carries is the caller's to fix. -/
theorem pullPointOn [LinearOrder A] (hle : ∀ a b : A, a ≤ b ↔ pullLe ρ a b) :
    letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    PointOn (pullPointSyms X C) (Sum.inl : A → A ⊕ Fin m) (pullMeans ρ) (pullTags ρ) := by
  let := (pullBlock X C).structure₁ (L := newLang L) ρ
  refine ⟨⟨fun r ts => ?_, fun ts => ?_, fun v i ts => ?_⟩, fun x => ?_, fun v t => Iff.rfl⟩
  · exact relMap_ext_inl (m := m) r ts
  · refine Iff.trans (iff_of_eq (congrArg (ρ (Sum.inl ()))
      (vec_eta₂ fun i => Sum.inl (ts i)).symm)) (hle (ts 0) (ts 1)).symm
  · exact Iff.rfl
  · exact ⟨fun h => match x, h with | Sum.inl a, _ => ⟨a, rfl⟩,
      fun ⟨a, ha⟩ => ha ▸ isOld_inl (m := m) a⟩

end Reading

/-! ### The kernel -/

section Kernel

variable {X C} {A : Type} [L.Structure A] [LinearOrder A] {m : ℕ}
variable (X C) in
/-- The formulas interpreting the source problem's vocabulary – the expanded
one together with its own block – over the extended universe: an atom of the
expansion is `DescriptiveComplexity.pointRelF`, an atom of the block is the
block variable itself. -/
noncomputable def pullSubst : FormulaSubst (X.E.sum C.lang) (pullLang X C) where
  rel {_n} r :=
    match r with
    | Sum.inl s => pointRelF (pullPointSyms X C) s id
    | Sum.inr c =>
        Relations.formula (pullCertSym X C c.1) fun j => Term.var (Fin.cast c.2 j)

variable (X C) in
/-- The domain formula: the value is a point of the expanded universe. -/
noncomputable def pullDom : (pullLang X C).Formula (Fin 1) :=
  isPointF (pullPointSyms X C) 0

variable (ρ : (pullBlock X C).Assignment (A ⊕ Fin m))

/-- The assignment of the source problem's block that the guess carries, read
at the points. -/
def pullCert (e : X.Map A → A ⊕ Fin m) : C.Assignment (X.Map A) :=
  fun j ts => ρ (Sum.inr (Sum.inr j)) fun l => e (ts l)

/-- **What names the points**: an injection of the expanded universe into the
invented values, whose image is exactly the values that are points, sending a
point to a value that means its assignment and carries its tag and no other. -/
structure PointRep (e : X.Map A → A ⊕ Fin m) : Prop where
  /-- Distinct points are named by distinct values. -/
  inj : Function.Injective e
  /-- A point's value means its assignment. -/
  mean : ∀ p : X.Map A, pullMeans ρ (e p) = p.1.2
  /-- A point's value carries its tag and no other. -/
  tag : ∀ (p : X.Map A) (t : X.Tag), pullTags ρ (e p) t ↔ t = p.1.1
  /-- Every value that is a point is named. -/
  onto : ∀ v : A ⊕ Fin m, (∃ t : X.Tag, pullTags ρ v t ∧
    (∀ t' : X.Tag, pullTags ρ v t' → t' = t) ∧ DomHolds (X := X) (t, pullMeans ρ v)) →
      ∃ p : X.Map A, e p = v

variable (h : letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    PointOn (pullPointSyms X C) (Sum.inl : A → A ⊕ Fin m) (pullMeans ρ) (pullTags ρ))
variable {e : X.Map A → A ⊕ Fin m} (hr : PointRep ρ e)

include h hr in
/-- **The structure the kernel's formulas define on the points is the one the
source problem is read in**: the expansion's own structure, and the source
problem's block read at the values naming the points. -/
theorem pullSubst_rel {n : ℕ} (r : (X.E.sum C.lang).Relations n) (ts : Fin n → X.Map A) :
    letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    (@RelMap _ (X.Map A) ((pullSubst X C).strucOn e) n r ts ↔
      @RelMap _ (X.Map A) (C.structure₁ (L := X.E) (pullCert ρ e)) n r ts) := by
  let := (pullBlock X C).structure₁ (L := newLang L) ρ
  cases r with
  | inl s =>
    refine Iff.trans (realize_pointRelF Sum.inl_injective h s id fun i => e (ts i)) ?_
    change _ ↔ @Sentence.Realize _ A
      ((X.B.replicate n).structure₁ (L := L.sum Language.order)
        (X.B.replicateAssign fun j => (ts j).1.2)) (X.relSentence s fun j => (ts j).1.1)
    have hmean : (X.B.replicateAssign fun j => pullMeans ρ (e (ts j))) =
        X.B.replicateAssign fun j => (ts j).1.2 :=
      congrArg X.B.replicateAssign (funext fun j => hr.mean (ts j))
    have hstr : ∀ τ : Fin n → X.Tag,
        (@Sentence.Realize _ A ((X.B.replicate n).structure₁ (L := L.sum Language.order)
            (X.B.replicateAssign fun j => pullMeans ρ (e (ts j)))) (X.relSentence s τ) ↔
          @Sentence.Realize _ A ((X.B.replicate n).structure₁ (L := L.sum Language.order)
            (X.B.replicateAssign fun j => (ts j).1.2)) (X.relSentence s τ)) := fun τ =>
      iff_of_eq (congrArg (fun σ => @Sentence.Realize _ A
        ((X.B.replicate n).structure₁ (L := L.sum Language.order) σ) (X.relSentence s τ)) hmean)
    constructor
    · rintro ⟨τ, hτ, hφ⟩
      have hτ' : τ = fun j => (ts j).1.1 := funext fun j => (hr.tag (ts j) (τ j)).mp (hτ j)
      exact hτ' ▸ (hstr τ).mp hφ
    · intro hφ
      exact ⟨fun j => (ts j).1.1, fun j => (hr.tag (ts j) _).mpr rfl, (hstr _).mpr hφ⟩
  | inr c => exact Iff.rfl

include h hr in
/-- The structure identification of `DescriptiveComplexity.pullSubst_rel`, as an
isomorphism. -/
noncomputable def pullSubstEquiv :
    letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    @Language.Equiv (X.E.sum C.lang) (X.Map A) (X.Map A)
      ((pullSubst X C).strucOn e) (C.structure₁ (L := X.E) (pullCert ρ e)) :=
  letI := (pullBlock X C).structure₁ (L := newLang L) ρ
  @Language.Equiv.mk _ (X.Map A) (X.Map A) ((pullSubst X C).strucOn e)
    (C.structure₁ (L := X.E) (pullCert ρ e)) (Equiv.refl _)
    (fun {_} f _ => isEmptyElim f) fun {_} r x => (pullSubst_rel ρ h hr r x).symm

include h hr in
/-- **The kernel, translated**: the source problem's first-order kernel, with
`DescriptiveComplexity.pointRelF` for the atoms of the expanded vocabulary, its
own block variables for its own, and “is a point” as the domain formula, holds
in the extended universe exactly when the kernel holds over the expansion. -/
theorem realize_pullKernel (φ : (X.E.sum C.lang).Sentence) :
    letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    (((A ⊕ Fin m) ⊨ (pullSubst X C).substSentence (pullDom X C) φ) ↔
      @Sentence.Realize _ (X.Map A) (C.structure₁ (L := X.E) (pullCert ρ e)) φ) := by
  let := (pullBlock X C).structure₁ (L := newLang L) ρ
  have hD : ∀ x : A ⊕ Fin m, (pullDom X C).Realize ![x] ↔ ∃ p : X.Map A, e p = x := by
    intro x
    rw [pullDom, realize_isPointF Sum.inl_injective h 0 (![x])]
    refine ⟨fun hx => hr.onto x ?_, ?_⟩
    · simpa using hx
    · rintro ⟨p, rfl⟩
      refine ⟨p.1.1, (hr.tag p _).mpr rfl, fun t' ht' => (hr.tag p t').mp ht', ?_⟩
      simp only [Matrix.cons_val_zero]
      rw [hr.mean p]
      exact p.2
  refine Iff.trans (FormulaSubst.realize_substSentence hr.inj hD φ) ?_
  exact realize_sentence_of_equiv (pullSubstEquiv ρ h hr) φ

end Kernel

/-! ### Naming the points -/

section Naming

variable {X C} {A : Type} [L.Structure A] {m : ℕ}

variable (X C) in
/-- The meaning block sits inside the whole block. -/
def meanHom : (meanBlockB (taggedBlock X)).ι → (pullBlock X C).ι :=
  fun i => Sum.inr (Sum.inl i)

variable (X C) in
omit [L.IsRelational] in
theorem meanHom_arity (i : (meanBlockB (taggedBlock X)).ι) :
    (pullBlock X C).arity (meanHom X C i) = (meanBlockB (taggedBlock X)).arity i :=
  rfl

variable (X C) in
/-- The meaning guard, in the vocabulary of the whole block. -/
noncomputable def pullMeanGuard : (pullLang X C).Sentence :=
  (LHom.sumMap (LHom.id (newLang L))
      (SOBlock.homLHom (meanHom X C) (meanHom_arity X C))).onSentence
    (meanGuardB L (taggedBlock X))

variable (ρ : (pullBlock X C).Assignment (A ⊕ Fin m))

/-- The meaning part of an assignment of the whole block. -/
def pullMeanPart : (meanBlockB (taggedBlock X)).Assignment (A ⊕ Fin m) :=
  fun i => ρ (Sum.inr (Sum.inl i))

/-- **The meaning guard, read in the whole block**: it says of the meaning part
what `DescriptiveComplexity.meanGuardB` says. -/
theorem realize_pullMeanGuard :
    letI := (pullBlock X C).structure₁ (L := newLang L) ρ
    (((A ⊕ Fin m) ⊨ pullMeanGuard X C) ↔
      @Sentence.Realize _ (A ⊕ Fin m) (meanStrucB (L := L) (pullMeanPart ρ))
        (meanGuardB L (taggedBlock X))) :=
  SOBlock.realize_homSentence (meanHom X C) (meanHom_arity X C) ρ _

end Naming

section Rep

variable {X C} {A : Type} [L.Structure A] [LinearOrder A] [Finite A] {m : ℕ}
variable (ρ : (pullBlock X C).Assignment (A ⊕ Fin m))

omit [L.IsRelational] [L.Structure A] [LinearOrder A] [Finite A] in
private theorem fin1_cases {M : Type} (v : M) (w : Fin 0 → M) :
    (Fin.cases v w : Fin (0 + 1) → M) = fun _ => v := by
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ i => exact i.elim0

/-- The assignment of the tagged block a point stands for: its own assignment,
and the tag bit of its tag alone. -/
def pointAssign (p : X.Map A) : (taggedBlock X).Assignment A :=
  consAssign p.1.2 fun t _ => t = p.1.1

omit [L.IsRelational] [Finite A] in
/-- **Distinct points have distinct assignments**: the assignment holds the
point's own, and its tag in the tag bits. -/
theorem pointAssign_injective : Function.Injective (pointAssign (X := X) (A := A)) := by
  intro p q hα
  refine map_ext ?_ ?_
  · have h₂ : (p.1.1 = p.1.1) = (p.1.1 = q.1.1) :=
      congrFun (congrFun hα (Sum.inr p.1.1)) Fin.elim0
    exact h₂ ▸ rfl
  · funext i ts
    exact congrFun (congrFun hα (Sum.inl i)) ts

omit [L.IsRelational] [L.Structure A] [LinearOrder A] [Finite A] in
/-- A tag atom is the meaning relation of a nullary variable. -/
theorem pullTags_meaning (v : A ⊕ Fin m) (t : X.Tag)
    (ts : Fin ((taggedBlock X).arity (Sum.inr t)) → A ⊕ Fin m) :
    pullTags ρ v t ↔ meaningOfB (pullMeanPart ρ) (Sum.inr t) v ts :=
  iff_of_eq (congrArg (pullMeanPart ρ (Sum.inr t)) (fin1_cases v ts).symm)

omit [L.IsRelational] [L.Structure A] [LinearOrder A] [Finite A] in
theorem pullMeans_inr (k : Fin m) (i : X.B.ι) (ts : Fin (X.B.arity i) → A) :
    pullMeans ρ (Sum.inr k) i ts ↔ meanAtB (pullMeanPart ρ) k ⟨Sum.inl i, ts⟩ :=
  Iff.rfl

omit [L.IsRelational] [L.Structure A] [LinearOrder A] [Finite A] in
theorem pullTags_inr (k : Fin m) (t : X.Tag)
    (ts : Fin ((taggedBlock X).arity (Sum.inr t)) → A) :
    pullTags ρ (Sum.inr k) t ↔ meanAtB (pullMeanPart ρ) k ⟨Sum.inr t, ts⟩ :=
  pullTags_meaning ρ (Sum.inr k) t fun j => Sum.inl (ts j)

variable (hbij : Function.Bijective (meanAtB (pullMeanPart ρ)))

/-- **The value naming a point**: the one whose meaning is the point's
assignment, tag bit included. -/
noncomputable def pullName (p : X.Map A) : A ⊕ Fin m :=
  Sum.inr ((meanAssignEquiv (pullMeanPart ρ) hbij).symm (pointAssign p))

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
include hbij in
theorem meanAtB_symm (α : (taggedBlock X).Assignment A) (i : (taggedBlock X).ι)
    (ts : Fin ((taggedBlock X).arity i) → A) :
    meanAtB (pullMeanPart ρ) ((meanAssignEquiv (pullMeanPart ρ) hbij).symm α) ⟨i, ts⟩ ↔
      α i ts :=
  iff_of_eq (congrFun (congrFun ((meanAssignEquiv (pullMeanPart ρ) hbij).apply_symm_apply α) i) ts)

omit [L.IsRelational] in
include hbij in
/-- **The naming is a representation**: it is injective, a point's value means
its assignment and carries its tag alone, and – given that a meaning relates an
invented value to original elements only – every value that is a point is
named. -/
theorem pullPointRep
    (hshaped : ∀ (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
      (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m),
      meaningOfB (pullMeanPart ρ) i v w → ¬IsOld v ∧ ∀ j, IsOld (w j)) :
    PointRep ρ (pullName ρ hbij) := by
  have hmean : ∀ p : X.Map A, pullMeans ρ (pullName ρ hbij p) = p.1.2 := by
    intro p
    funext i ts
    exact propext ((pullMeans_inr ρ _ i ts).trans (meanAtB_symm ρ hbij _ (Sum.inl i) ts))
  have htag : ∀ (p : X.Map A) (t : X.Tag), pullTags ρ (pullName ρ hbij p) t ↔ t = p.1.1 :=
    fun p t => (pullTags_inr ρ _ t Fin.elim0).trans (meanAtB_symm ρ hbij _ (Sum.inr t) Fin.elim0)
  refine ⟨fun p q hpq => pointAssign_injective
    ((meanAssignEquiv (pullMeanPart ρ) hbij).symm.injective (Sum.inr_injective hpq)),
    hmean, htag, fun v hv => ?_⟩
  · obtain ⟨t, ht, huniq, hdom⟩ := hv
    obtain ⟨k, rfl⟩ : ∃ k : Fin m, Sum.inr k = v := by
      cases v with
      | inl a =>
        exact absurd (isOld_inl (m := m) a)
          (hshaped (Sum.inr t) _ Fin.elim0 ((pullTags_meaning ρ _ t Fin.elim0).mp ht)).1
      | inr k => exact ⟨k, rfl⟩
    have hpa : pointAssign (⟨(t, pullMeans ρ (Sum.inr k)), hdom⟩ : X.Map A) =
        meanAssignEquiv (pullMeanPart ρ) hbij k := by
      funext i
      cases i with
      | inl i => funext ts; rfl
      | inr t' =>
        funext ts
        refine propext (Iff.trans ?_ (pullTags_inr ρ k t' ts))
        exact ⟨fun h => h ▸ ht, fun h => huniq t' h⟩
    exact ⟨⟨(t, pullMeans ρ (Sum.inr k)), hdom⟩,
      congrArg Sum.inr (by rw [hpa, Equiv.symm_apply_apply])⟩

end Rep

/-! ### The sentence, and what an assignment satisfying it gives -/

section Back

/-- **The sentence**: the order guard, the meaning guard, and the translated
kernel. -/
noncomputable def pullSentence (φ : (X.E.sum C.lang).Sentence) : (pullLang X C).Sentence :=
  extLinearGuard L (guessBlock X C) ⊓ pullMeanGuard X C ⊓
    (pullSubst X C).substSentence (pullDom X C) φ

variable {X C} {A : Type} [L.Structure A] [Finite A] {m : ℕ}

/-- **From an assignment to the expansion**: an assignment satisfying the
sentence carries a linear order of the instance and an assignment of the source
problem's block over the expansion at that order, for which the source kernel
holds. -/
theorem pullSentence_back (φ : (X.E.sum C.lang).Sentence)
    (ρ : (pullBlock X C).Assignment (A ⊕ Fin m))
    (hψ : letI := (pullBlock X C).structure₁ (L := newLang L) ρ
      ((A ⊕ Fin m) ⊨ pullSentence X C φ)) :
    ∃ inst : LinearOrder A, ∃ σ : C.Assignment (@ExpExpansion.Map L X A _ inst),
      @Sentence.Realize _ (@ExpExpansion.Map L X A _ inst)
        (@SOBlock.structure₁ X.E C (@ExpExpansion.Map L X A _ inst)
          (@ExpExpansion.mapStructure L X A _ inst) σ) φ := by
  let := (pullBlock X C).structure₁ (L := newLang L) ρ
  obtain ⟨⟨hord, hmg⟩, hker⟩ :=
    (Sentence.realize_inf (A ⊕ Fin m)).mp hψ |>.imp
      (fun h' => (Sentence.realize_inf (A ⊕ Fin m)).mp h') id
  obtain ⟨-, hrefl, htrans, hanti, htotal⟩ := (realize_extLinearGuard A m ρ).mp hord
  let : LinearOrder A :=
    pullLinearOrder ρ (fun a => hrefl _ (isOld_inl (m := m) a))
      (fun a b c hab hbc => htrans _ _ _ hab hbc) (fun a b hab hba => Sum.inl_injective
        (hanti _ _ hab hba))
      fun a b => htotal _ _ (isOld_inl (m := m) a) (isOld_inl (m := m) b)
  have hpt := pullPointOn ρ fun a b => Iff.rfl
  have hmg' := (realize_pullMeanGuard ρ).mp hmg
  let := meanStrucB (L := L) (pullMeanPart ρ)
  have hbij := bijective_meanAtB_of_guard (pullMeanPart ρ) hmg'
  have hshaped : ∀ (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
      (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m),
      meaningOfB (pullMeanPart ρ) i v w → ¬IsOld v ∧ ∀ j, IsOld (w j) :=
    (realize_meanShapedB (pullMeanPart ρ)).mp
      ((Sentence.realize_inf (A ⊕ Fin m)).mp
        ((Sentence.realize_inf (A ⊕ Fin m)).mp
          ((Sentence.realize_inf (A ⊕ Fin m)).mp hmg').1).1).1
  have hrep := pullPointRep ρ hbij hshaped
  exact ⟨inferInstance, pullCert ρ (pullName ρ hbij),
    (realize_pullKernel ρ hpt hrep φ).mp hker⟩

end Back

end DescriptiveComplexity
