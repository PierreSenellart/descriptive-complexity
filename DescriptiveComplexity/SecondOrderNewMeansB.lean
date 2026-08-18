/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewMeans
import DescriptiveComplexity.SecondOrderMerge

/-!
# Meanings for a whole block

`DescriptiveComplexity.SecondOrderNewMeans` guesses what an invented value means
when a point is a *single* relation. A point of an exponential expansion is an
assignment of a whole **block**: one relation per variable, of that variable's
arity. So the guess is a family – one meaning relation per variable `i`, of
arity `B.arity i + 1` – and the conditions on it are the same four, taken
variable by variable:

* `DescriptiveComplexity.meanShapedB` – each relates an invented value to
  original elements and nothing else;
* `DescriptiveComplexity.meanInjB` – invented values agreeing on *every*
  variable are equal;
* `DescriptiveComplexity.meanEmptyB` – some invented value means the empty
  assignment;
* `DescriptiveComplexity.meanFlipB` – flipping one tuple of one variable, and
  leaving the other variables alone, lands on an invented value again.

An assignment of a block is a set of `Σ i, Fin (B.arity i) → A` – a tuple
tagged by the variable it belongs to – so the flips of that single sigma type
are exactly the flips of one tuple of one variable, and
`DescriptiveComplexity.bijective_meanAtB` reads the four guards as a bijection
between the invented values and *all* assignments of the block, through the
counting of `DescriptiveComplexity.SecondOrderNewCount`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The block of meanings and its atoms -/

/-- The block guessing the meanings of a whole block: one relation per variable,
of one more argument than that variable. -/
abbrev meanBlockB (B : SOBlock) : SOBlock where
  ι := B.ι
  arity := fun i => B.arity i + 1

/-- The meaning relation of one variable, as a symbol. -/
def meanSymB (B : SOBlock) (i : B.ι) : (meanBlockB B).lang.Relations (B.arity i + 1) :=
  ⟨i, rfl⟩

/-- The vocabulary a block-meaning guess is written in. -/
abbrev meanHostB (L : Language.{0, 0}) (B : SOBlock) : Language :=
  (newLang L).sum (meanBlockB B).lang

section Atoms

variable (L : Language.{0, 0}) (B : SOBlock)

/-- The atom `old x`, over the block-meaning vocabulary. -/
noncomputable def oldAtomB {α : Type} (x : α) : (meanHostB L B).Formula α :=
  Relations.formula
    (Sum.inl (Sum.inr Language.oldSym) : (meanHostB L B).Relations 1) fun _ => Term.var x

/-- The atom `Mᵢ v x⃗`. -/
noncomputable def meanAtomB (i : B.ι) {α : Type} (v : α) (w : Fin (B.arity i) → α) :
    (meanHostB L B).Formula α :=
  Relations.formula (Sum.inr (meanSymB B i) : (meanHostB L B).Relations (B.arity i + 1))
    (Fin.cases (Term.var v) fun j => Term.var (w j))

end Atoms

/-! ### The four guards -/

section Guards

variable (L : Language.{0, 0}) (B : SOBlock)

/-- **Each meaning relation is shaped**: it relates an invented value to
original elements, and nothing else. -/
noncomputable def meanShapedB : (meanHostB L B).Sentence :=
  Formula.iInf fun i : B.ι =>
    Formula.iAlls (Option (Fin (B.arity i)))
      (meanAtomB L B i (Sum.inr none) (fun j => Sum.inr (some j)) ⟹
        ((∼(oldAtomB L B (Sum.inr none))) ⊓
          Formula.iInf fun j : Fin (B.arity i) => oldAtomB L B (Sum.inr (some j))))

/-- **Some invented value means the empty assignment.** -/
noncomputable def meanEmptyB : (meanHostB L B).Sentence :=
  Formula.iExs (Fin 1)
    ((∼(oldAtomB L B (Sum.inr 0))) ⊓
      Formula.iInf fun i : B.ι =>
        Formula.iAlls (Fin (B.arity i))
          (∼(meanAtomB L B i (Sum.inl (Sum.inr 0)) fun j => Sum.inr j)))

/-- **Invented values agreeing on every variable are equal.** -/
noncomputable def meanInjB : (meanHostB L B).Sentence :=
  Formula.iAlls (Fin 2)
    ((∼(oldAtomB L B (Sum.inr 0))) ⊓ (∼(oldAtomB L B (Sum.inr 1))) ⊓
        (Formula.iInf fun i : B.ι =>
          Formula.iAlls (Fin (B.arity i))
            (meanAtomB L B i (Sum.inl (Sum.inr 0)) (fun j => Sum.inr j) ⇔
              meanAtomB L B i (Sum.inl (Sum.inr 1)) fun j => Sum.inr j)) ⟹
      Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

open Classical in
/-- **Flipping one tuple of one variable lands on an invented value again**, the
other variables unchanged. This is what makes the guess onto. -/
noncomputable def meanFlipB : (meanHostB L B).Sentence :=
  Formula.iInf fun i : B.ι =>
    Formula.iAlls (Option (Fin (B.arity i)))
      (((∼(oldAtomB L B (Sum.inr none))) ⊓
          Formula.iInf fun j : Fin (B.arity i) => oldAtomB L B (Sum.inr (some j))) ⟹
        Formula.iExs (Fin 1)
          ((∼(oldAtomB L B (Sum.inr 0))) ⊓
            ((Formula.iAlls (Fin (B.arity i))
                (meanAtomB L B i (Sum.inl (Sum.inr 0)) (fun j => Sum.inr j) ⇔
                  (meanAtomB L B i (Sum.inl (Sum.inl (Sum.inr none))) (fun j => Sum.inr j) ⇔
                    ∼(Formula.iInf fun j : Fin (B.arity i) =>
                      Term.equal (Term.var (Sum.inr j))
                        (Term.var (Sum.inl (Sum.inl (Sum.inr (some j))))))))) ⊓
              Formula.iInf fun i' : B.ι =>
                if i' = i then ⊤
                else Formula.iAlls (Fin (B.arity i'))
                  (meanAtomB L B i' (Sum.inl (Sum.inr 0)) (fun j => Sum.inr j) ⇔
                    meanAtomB L B i' (Sum.inl (Sum.inl (Sum.inr none)))
                      fun j => Sum.inr j))))

/-- **The whole guard**: the four conditions together. -/
noncomputable def meanGuardB : (meanHostB L B).Sentence :=
  meanShapedB L B ⊓ meanEmptyB L B ⊓ meanInjB L B ⊓ meanFlipB L B

end Guards

/-! ### Assignments, as sets of tagged tuples -/

section Assign

/-- **An assignment of a block is a set of tagged tuples**: one tuple of the
right arity per variable, tagged by the variable it belongs to. This is the
shape the flips of `DescriptiveComplexity.SecondOrderNewCount` are stated at,
and it is what makes flipping one tuple of one variable a flip of a single
element. -/
def SOBlock.assignEquivSigma (B : SOBlock) (A : Type) :
    B.Assignment A ≃ ((Σ i : B.ι, Fin (B.arity i) → A) → Prop) where
  toFun ρ p := ρ p.1 p.2
  invFun S i w := S ⟨i, w⟩
  left_inv _ := rfl
  right_inv S := funext fun p => by cases p; rfl

/-- **Splitting an assignment of a merged block.** -/
def consAssignEquiv (B C : SOBlock) (A : Type) :
    (SOBlock.cons B C).Assignment A ≃ B.Assignment A × C.Assignment A where
  toFun ρ := (fun i => ρ (Sum.inl i), fun j => ρ (Sum.inr j))
  invFun p := consAssign p.1 p.2
  left_inv ρ := consAssign_split ρ
  right_inv _ := rfl

/-- The block of tag bits: one nullary variable per tag, so that an assignment
of it is a set of tags. Adding it to a block is how an invented value carries a
tag without any machinery of its own – a nullary variable's meaning relation is
unary, `M v`, read as “the value `v` carries this tag”. -/
abbrev tagBits (T : Type) [Finite T] : SOBlock where
  ι := T
  arity := fun _ => 0

/-- An assignment of the tag bits is a set of tags. -/
def tagBitsEquiv (T : Type) [Finite T] (A : Type) :
    (tagBits T).Assignment A ≃ (T → Prop) where
  toFun ρ t := ρ t default
  invFun S t _ := S t
  left_inv ρ := funext fun _ => funext fun w => by
    have : w = default := Subsingleton.elim _ _
    rw [this]
  right_inv _ := rfl

/-- **With tag bits added, an assignment is a point's data**: the block's own
assignment paired with a set of tags. An invented value stands for a point of
the expansion exactly when its tag set is a singleton and its assignment
satisfies that tag's domain sentence – both conditions the kernel can state, so
neither needs a guard of its own. -/
def consTagAssignEquiv (B : SOBlock) (T : Type) [Finite T] (A : Type) :
    (SOBlock.cons B (tagBits T)).Assignment A ≃ B.Assignment A × (T → Prop) :=
  (consAssignEquiv B (tagBits T) A).trans
    (Equiv.prodCongr (Equiv.refl _) (tagBitsEquiv T A))

end Assign

/-! ### The guards, realized -/

section Realize

variable {L : Language.{0, 0}} [L.IsRelational] {B : SOBlock} {A : Type} [L.Structure A] {m : ℕ}
variable (ρ : (meanBlockB B).Assignment (A ⊕ Fin m))

/-- What an element means at one variable, read off the guess. -/
def meaningOfB (i : B.ι) (v : A ⊕ Fin m) (w : Fin (B.arity i) → A ⊕ Fin m) : Prop :=
  ρ i (Fin.cases v w)

/-- The assignment an invented value means, as a set of tuples tagged by the
variable they belong to. -/
def meanAtB (k : Fin m) : (Σ i : B.ι, Fin (B.arity i) → A) → Prop :=
  fun p => meaningOfB ρ p.1 (Sum.inr k) fun j => Sum.inl (p.2 j)

/-- The host structure: the extended structure expanded by the guess. -/
@[instance_reducible]
noncomputable def meanStrucB : (meanHostB L B).Structure (A ⊕ Fin m) :=
  @sumStructure (newLang L) (meanBlockB B).lang (A ⊕ Fin m) (extStructure L A m)
    ((meanBlockB B).structure ρ)

theorem realize_oldAtomB {α : Type} (x : α) (v : α → A ⊕ Fin m) :
    letI := meanStrucB (L := L) ρ
    (oldAtomB L B x).Realize v ↔ IsOld (v x) :=
  Iff.rfl

theorem realize_meanAtomB (i : B.ι) {α : Type} (x : α) (w : Fin (B.arity i) → α)
    (v : α → A ⊕ Fin m) :
    letI := meanStrucB (L := L) ρ
    (meanAtomB L B i x w).Realize v ↔ meaningOfB ρ i (v x) fun j => v (w j) := by
  letI := meanStrucB (L := L) ρ
  refine iff_of_eq (congrArg (ρ i) (funext fun j => ?_))
  induction j using Fin.cases <;> rfl

theorem realize_meanShapedB :
    letI := meanStrucB (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanShapedB L B) ↔
      ∀ (i : B.ι) (v : A ⊕ Fin m) (w : Fin (B.arity i) → A ⊕ Fin m),
        meaningOfB ρ i v w → ¬IsOld v ∧ ∀ j, IsOld (w j) := by
  letI := meanStrucB (L := L) ρ
  rw [meanShapedB, Sentence.Realize, Formula.realize_iInf]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, Formula.realize_iInf, realize_oldAtomB, realize_meanAtomB]
  exact ⟨fun h i v w hM => h i (fun o => o.elim v w) hM,
    fun h i u hM => h i (u none) (fun j => u (some j)) hM⟩

theorem realize_meanEmptyB :
    letI := meanStrucB (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanEmptyB L B) ↔
      ∃ v : A ⊕ Fin m, ¬IsOld v ∧
        ∀ (i : B.ι) (w : Fin (B.arity i) → A ⊕ Fin m), ¬meaningOfB ρ i v w := by
  letI := meanStrucB (L := L) ρ
  rw [meanEmptyB, Sentence.Realize, Formula.realize_iExs]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_iInf,
    Formula.realize_iAlls, realize_oldAtomB, realize_meanAtomB]
  exact ⟨fun ⟨u, hu⟩ => ⟨u 0, hu⟩, fun ⟨v, hv⟩ => ⟨fun _ => v, hv⟩⟩

theorem realize_meanInjB :
    letI := meanStrucB (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanInjB L B) ↔
      ∀ v u : A ⊕ Fin m, ¬IsOld v → ¬IsOld u →
        (∀ (i : B.ι) (w : Fin (B.arity i) → A ⊕ Fin m),
          meaningOfB ρ i v w ↔ meaningOfB ρ i u w) → v = u := by
  letI := meanStrucB (L := L) ρ
  rw [meanInjB, Sentence.Realize, Formula.realize_iAlls]
  simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iInf, Formula.realize_iAlls, Formula.realize_iff,
    Formula.realize_equal, realize_oldAtomB, realize_meanAtomB]
  exact ⟨fun h v u hv hu hM => h ![v, u] ⟨⟨hv, hu⟩, hM⟩,
    fun h i hg => h (i 0) (i 1) hg.1.1 hg.1.2 hg.2⟩

open Classical in
theorem realize_meanFlipB :
    letI := meanStrucB (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanFlipB L B) ↔
      ∀ (i : B.ι) (v : A ⊕ Fin m) (y : Fin (B.arity i) → A ⊕ Fin m),
        ¬IsOld v → (∀ j, IsOld (y j)) →
        ∃ u : A ⊕ Fin m, ¬IsOld u ∧
          (∀ w : Fin (B.arity i) → A ⊕ Fin m,
            meaningOfB ρ i u w ↔ (meaningOfB ρ i v w ↔ ¬∀ j, w j = y j)) ∧
          ∀ i' : B.ι, i' ≠ i → ∀ w : Fin (B.arity i') → A ⊕ Fin m,
            meaningOfB ρ i' u w ↔ meaningOfB ρ i' v w := by
  letI := meanStrucB (L := L) ρ
  classical
  rw [meanFlipB, Sentence.Realize, Formula.realize_iInf]
  refine forall_congr' fun i => ?_
  rw [Formula.realize_iAlls]
  simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iInf, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_iff, Formula.realize_equal, realize_oldAtomB, realize_meanAtomB]
  constructor
  · intro h v y hv hy
    obtain ⟨u, hu, h1, h2⟩ := h (fun o => o.elim v y) ⟨hv, hy⟩
    refine ⟨u 0, hu, h1, fun i' hii w => ?_⟩
    have := h2 i'
    rw [if_neg hii, Formula.realize_iAlls] at this
    simp only [Formula.realize_iff, realize_meanAtomB] at this
    exact this w
  · intro h u hg
    obtain ⟨v, hv, h1, h2⟩ := h (u none) (fun j => u (some j)) hg.1 hg.2
    refine ⟨fun _ => v, hv, h1, fun i' => ?_⟩
    by_cases hii : i' = i
    · rw [if_pos hii]
      exact Formula.realize_top.mpr trivial
    · rw [if_neg hii, Formula.realize_iAlls]
      simp only [Formula.realize_iff, realize_meanAtomB]
      exact h2 i' hii

/-- **The four guards make the meanings a bijection**: the invented values name
every assignment of the block, each exactly once. -/
theorem bijective_meanAtB [Finite A]
    (hshaped : ∀ (i : B.ι) (v : A ⊕ Fin m) (w : Fin (B.arity i) → A ⊕ Fin m),
      meaningOfB ρ i v w → ¬IsOld v ∧ ∀ j, IsOld (w j))
    (hempty : ∃ v : A ⊕ Fin m, ¬IsOld v ∧
      ∀ (i : B.ι) (w : Fin (B.arity i) → A ⊕ Fin m), ¬meaningOfB ρ i v w)
    (hinj : ∀ v u : A ⊕ Fin m, ¬IsOld v → ¬IsOld u →
      (∀ (i : B.ι) (w : Fin (B.arity i) → A ⊕ Fin m),
        meaningOfB ρ i v w ↔ meaningOfB ρ i u w) → v = u)
    (hflip : ∀ (i : B.ι) (v : A ⊕ Fin m) (y : Fin (B.arity i) → A ⊕ Fin m),
      ¬IsOld v → (∀ j, IsOld (y j)) →
      ∃ u : A ⊕ Fin m, ¬IsOld u ∧
        (∀ w : Fin (B.arity i) → A ⊕ Fin m,
          meaningOfB ρ i u w ↔ (meaningOfB ρ i v w ↔ ¬∀ j, w j = y j)) ∧
        ∀ i' : B.ι, i' ≠ i → ∀ w : Fin (B.arity i') → A ⊕ Fin m,
          meaningOfB ρ i' u w ↔ meaningOfB ρ i' v w) :
    Function.Bijective (meanAtB ρ) := by
  classical
  letI := Fintype.ofFinite B.ι
  letI := Fintype.ofFinite A
  haveI : Finite ((i : B.ι) × (Fin (B.arity i) → A)) := inferInstance
  have hnew : ∀ k : Fin m, ¬IsOld (Sum.inr k : A ⊕ Fin m) := fun _ h => h
  refine bijective_of_flipClosedP _ ?_ ?_ ?_
  · intro k l h
    have heq : (Sum.inr k : A ⊕ Fin m) = Sum.inr l := by
      refine hinj _ _ (hnew k) (hnew l) fun i w => ?_
      by_cases hw : ∀ t, ∃ x : A, w t = Sum.inl x
      · choose x hx using hw
        have hwx : w = fun t => Sum.inl (x t) := funext hx
        rw [hwx]
        exact iff_of_eq (congrFun h ⟨i, x⟩)
      · obtain ⟨t, ht⟩ := not_forall.mp hw
        refine iff_of_false (fun hc => ?_) (fun hc => ?_) <;>
          · obtain ⟨-, hold⟩ := hshaped _ _ _ hc
            match htt : w t with
            | Sum.inl b => exact ht ⟨b, htt⟩
            | Sum.inr b =>
              have := hold t
              rw [htt] at this
              exact this
    exact Sum.inr_injective heq
  · obtain ⟨v, hv, hw⟩ := hempty
    match hvv : v with
    | Sum.inl b => exact absurd trivial hv
    | Sum.inr k => exact ⟨k, fun p => hw p.1 fun t => Sum.inl (p.2 t)⟩
  · rintro k ⟨i, y⟩
    obtain ⟨u, hu, h1, h2⟩ :=
      hflip i (Sum.inr k) (fun t => Sum.inl (y t)) (hnew k) fun _ => trivial
    match huu : u with
    | Sum.inl b => exact absurd trivial hu
    | Sum.inr l =>
      refine ⟨l, ?_⟩
      rintro ⟨i', w⟩
      by_cases hii : i' = i
      · subst hii
        refine (h1 fun t => Sum.inl (w t)).trans
          ((iff_congr Iff.rfl ?_).trans (xor_iff_iff_not _ _).symm)
        refine not_congr ⟨fun hh => ?_, fun hh t => ?_⟩
        · have : w = y := funext fun t => Sum.inl_injective (hh t)
          simp [this]
        · have : w = y := by simpa [Sigma.mk.injEq] using hh
          rw [this]
      · have hne : (⟨i', w⟩ : Σ i : B.ι, Fin (B.arity i) → A) ≠ ⟨i, y⟩ :=
          fun hh => hii (congrArg Sigma.fst hh)
        refine (h2 i' hii fun t => Sum.inl (w t)).trans ⟨fun hp => Or.inl ⟨hp, hne⟩, ?_⟩
        rintro (⟨hp, -⟩ | ⟨hq, -⟩)
        · exact hp
        · exact absurd hq hne

/-- **The whole guard, and what it buys**: the invented values name every
assignment of the block, each exactly once. -/
theorem bijective_meanAtB_of_guard [Finite A] :
    letI := meanStrucB (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanGuardB L B) → Function.Bijective (meanAtB ρ) := by
  letI := meanStrucB (L := L) ρ
  intro h
  obtain ⟨⟨⟨hshaped, hempty⟩, hinj⟩, hflip⟩ :=
    (Sentence.realize_inf (A ⊕ Fin m)).mp h |>.imp
      (fun h' => (Sentence.realize_inf (A ⊕ Fin m)).mp h' |>.imp
        (fun h'' => (Sentence.realize_inf (A ⊕ Fin m)).mp h'') id) id
  exact bijective_meanAtB ρ ((realize_meanShapedB ρ).mp hshaped)
    ((realize_meanEmptyB ρ).mp hempty) ((realize_meanInjB ρ).mp hinj)
    ((realize_meanFlipB ρ).mp hflip)

/-- **The invented values enumerate the assignments of the block**: the guard's
bijection, read at assignments rather than at sets of tagged tuples. -/
noncomputable def meanAssignEquiv [Finite A] (hbij : Function.Bijective (meanAtB ρ)) :
    Fin m ≃ B.Assignment A :=
  (Equiv.ofBijective _ hbij).trans (SOBlock.assignEquivSigma B A).symm

end Realize

end DescriptiveComplexity
