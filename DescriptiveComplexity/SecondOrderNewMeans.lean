/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewCount
import DescriptiveComplexity.SecondOrderNew

/-!
# Guessing what the invented values mean

To read a problem over an exponential expansion as one with value invention, the
invented values have to *be* the expansion's points, and a point is an
assignment of a block: a relation over the instance. So the sentence guesses a
**meaning relation** `M`, one more argument than the relation it names: `M v x⃗`
says that the invented value `v` names a relation holding of `x⃗`.

Three of the four conditions on that guess are ordinary first-order statements
about the extended universe:

* `DescriptiveComplexity.meanShaped` – `M` relates an invented value to original
  elements and nothing else;
* `DescriptiveComplexity.meanInj` – distinct invented values name distinct
  relations;
* `DescriptiveComplexity.meanEmpty` – some invented value names the empty
  relation.

The fourth is what buys the one thing a sentence cannot say, that the guess is
**onto**:

* `DescriptiveComplexity.meanFlip` – for every invented value and every tuple,
  some invented value names the same relation with that tuple flipped.

With injectivity, those last two make the meanings enumerate *every* relation,
by `DescriptiveComplexity.bijective_of_flipClosedP` – a counting argument in
Lean, not a condition in the logic. That is where the bound of an
exponentially-bounded invention is spent.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The block and its atoms -/

/-- The block guessing the meanings: one relation of arity one more than the
relation being named. -/
abbrev meanBlock (a : ℕ) : SOBlock where
  ι := Unit
  arity := fun _ => a + 1

/-- The meaning relation, as a symbol. -/
def meanSym (a : ℕ) : (meanBlock a).lang.Relations (a + 1) :=
  ⟨(), rfl⟩

/-- The vocabulary a meaning guess is written in. -/
abbrev meanHost (L : Language.{0, 0}) (a : ℕ) : Language :=
  (newLang L).sum (meanBlock a).lang

section Atoms

variable (L : Language.{0, 0}) (a : ℕ)

/-- The atom `old x`. -/
noncomputable def oldAtomM {α : Type} (x : α) : (meanHost L a).Formula α :=
  Relations.formula
    (Sum.inl (Sum.inr Language.oldSym) : (meanHost L a).Relations 1) fun _ => Term.var x

/-- The atom `M v x⃗`: the invented value `v` names a relation holding of `x⃗`. -/
noncomputable def meanAtom {α : Type} (v : α) (w : Fin a → α) : (meanHost L a).Formula α :=
  Relations.formula (Sum.inr (meanSym a) : (meanHost L a).Relations (a + 1))
    (Fin.cases (Term.var v) fun i => Term.var (w i))

end Atoms

/-! ### The four guards -/

section Guards

variable (L : Language.{0, 0}) (a : ℕ)

/-- **The meaning relation is shaped**: it relates an invented value to original
elements, and nothing else. -/
noncomputable def meanShaped : (meanHost L a).Sentence :=
  Formula.iAlls (Option (Fin a))
    (meanAtom L a (Sum.inr none) (fun i => Sum.inr (some i)) ⟹
      ((∼(oldAtomM L a (Sum.inr none))) ⊓
        Formula.iInf fun i : Fin a => oldAtomM L a (Sum.inr (some i))))

/-- **Some invented value names the empty relation.** -/
noncomputable def meanEmpty : (meanHost L a).Sentence :=
  Formula.iExs (Fin 1)
    ((∼(oldAtomM L a (Sum.inr 0))) ⊓
      Formula.iAlls (Fin a)
        (∼(meanAtom L a (Sum.inl (Sum.inr 0)) fun i => Sum.inr i)))

/-- **Distinct invented values name distinct relations.** -/
noncomputable def meanInj : (meanHost L a).Sentence :=
  Formula.iAlls (Fin 2)
    ((∼(oldAtomM L a (Sum.inr 0))) ⊓ (∼(oldAtomM L a (Sum.inr 1))) ⊓
        Formula.iAlls (Fin a)
          (meanAtom L a (Sum.inl (Sum.inr 0)) (fun i => Sum.inr i) ⇔
            meanAtom L a (Sum.inl (Sum.inr 1)) fun i => Sum.inr i) ⟹
      Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))

/-- **The meanings are closed under flipping one tuple**: for every invented
value and every tuple of original elements, some invented value names the same
relation with that tuple flipped. This is what makes the guess onto. -/
noncomputable def meanFlip : (meanHost L a).Sentence :=
  Formula.iAlls (Option (Fin a))
    (((∼(oldAtomM L a (Sum.inr none))) ⊓
        Formula.iInf fun i : Fin a => oldAtomM L a (Sum.inr (some i))) ⟹
      Formula.iExs (Fin 1)
        ((∼(oldAtomM L a (Sum.inr 0))) ⊓
          Formula.iAlls (Fin a)
            (meanAtom L a (Sum.inl (Sum.inr 0)) (fun i => Sum.inr i) ⇔
              (meanAtom L a (Sum.inl (Sum.inl (Sum.inr none))) (fun i => Sum.inr i) ⇔
                ∼(Formula.iInf fun i : Fin a =>
                  Term.equal (Term.var (Sum.inr i))
                    (Term.var (Sum.inl (Sum.inl (Sum.inr (some i))))))))))

/-- **The whole guard**: the four conditions together. -/
noncomputable def meanGuard : (meanHost L a).Sentence :=
  meanShaped L a ⊓ meanEmpty L a ⊓ meanInj L a ⊓ meanFlip L a

end Guards

/-! ### The guards, realized -/

section Realize

variable {L : Language.{0, 0}} [L.IsRelational] {a : ℕ} {A : Type} [L.Structure A] {m : ℕ}
variable (ρ : (meanBlock a).Assignment (A ⊕ Fin m))

/-- The relation an element names, read off the guess. -/
def meaningOf : (A ⊕ Fin m) → (Fin a → A ⊕ Fin m) → Prop :=
  fun v w => ρ () (Fin.cases v w)

/-- The relation an invented value names, at original arguments. -/
def meanAt (i : Fin m) : (Fin a → A) → Prop :=
  fun w => meaningOf ρ (Sum.inr i) fun j => Sum.inl (w j)

/-- The host structure: the extended structure expanded by the guess. -/
@[instance_reducible]
noncomputable def meanStruc : (meanHost L a).Structure (A ⊕ Fin m) :=
  @sumStructure (newLang L) (meanBlock a).lang (A ⊕ Fin m) (extStructure L A m)
    ((meanBlock a).structure ρ)

theorem realize_oldAtomM {α : Type} (x : α) (v : α → A ⊕ Fin m) :
    letI := meanStruc (L := L) ρ
    (oldAtomM L a x).Realize v ↔ IsOld (v x) :=
  Iff.rfl

theorem realize_meanAtom {α : Type} (x : α) (w : Fin a → α) (v : α → A ⊕ Fin m) :
    letI := meanStruc (L := L) ρ
    (meanAtom L a x w).Realize v ↔ meaningOf ρ (v x) fun i => v (w i) := by
  let := meanStruc (L := L) ρ
  refine iff_of_eq (congrArg (ρ ()) (funext fun j => ?_))
  induction j using Fin.cases <;> rfl

theorem realize_meanShaped :
    letI := meanStruc (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanShaped L a) ↔
      ∀ (v : A ⊕ Fin m) (w : Fin a → A ⊕ Fin m),
        meaningOf ρ v w → ¬IsOld v ∧ ∀ i, IsOld (w i) := by
  let := meanStruc (L := L) ρ
  rw [meanShaped, Sentence.Realize, Formula.realize_iAlls]
  constructor
  · intro h v w hM
    have hu := h fun o => o.elim v w
    rw [Formula.realize_imp] at hu
    have h2 := hu ((realize_meanAtom ρ (Sum.inr none) (fun i => Sum.inr (some i)) _).mpr hM)
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_iInf] at h2
    exact ⟨fun hc => h2.1 ((realize_oldAtomM ρ (Sum.inr none) _).mpr hc),
      fun i => (realize_oldAtomM ρ (Sum.inr (some i)) _).mp (h2.2 i)⟩
  · intro h u
    rw [Formula.realize_imp]
    intro hM
    have h2 := h (u none) (fun i => u (some i))
      ((realize_meanAtom ρ (Sum.inr none) (fun i => Sum.inr (some i)) _).mp hM)
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_iInf]
    exact ⟨fun hc => h2.1 ((realize_oldAtomM ρ (Sum.inr none) _).mp hc),
      fun i => (realize_oldAtomM ρ (Sum.inr (some i)) _).mpr (h2.2 i)⟩

theorem realize_meanEmpty :
    letI := meanStruc (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanEmpty L a) ↔
      ∃ v : A ⊕ Fin m, ¬IsOld v ∧ ∀ w : Fin a → A ⊕ Fin m, ¬meaningOf ρ v w := by
  let := meanStruc (L := L) ρ
  rw [meanEmpty, Sentence.Realize, Formula.realize_iExs]
  constructor
  · rintro ⟨u, hu⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_iAlls] at hu
    refine ⟨u 0, fun hc => hu.1 ((realize_oldAtomM ρ (Sum.inr 0) _).mpr hc), fun w hc => ?_⟩
    have h2 := hu.2 w
    rw [Formula.realize_not] at h2
    exact h2 ((realize_meanAtom ρ (Sum.inl (Sum.inr 0)) (fun i => Sum.inr i) _).mpr hc)
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun _ => v, ?_⟩
    rw [Formula.realize_inf, Formula.realize_not, Formula.realize_iAlls]
    refine ⟨fun hc => hv ((realize_oldAtomM ρ (Sum.inr 0) _).mp hc), fun w => ?_⟩
    rw [Formula.realize_not]
    exact fun hc => hw w ((realize_meanAtom ρ (Sum.inl (Sum.inr 0)) (fun i => Sum.inr i) _).mp hc)

theorem realize_meanInj :
    letI := meanStruc (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanInj L a) ↔
      ∀ v u : A ⊕ Fin m, ¬IsOld v → ¬IsOld u →
        (∀ w : Fin a → A ⊕ Fin m, meaningOf ρ v w ↔ meaningOf ρ u w) → v = u := by
  let := meanStruc (L := L) ρ
  rw [meanInj, Sentence.Realize, Formula.realize_iAlls]
  simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iAlls, Formula.realize_iff, Formula.realize_equal,
    realize_oldAtomM, realize_meanAtom]
  constructor
  · intro h v u hv hu hM
    exact h ![v, u] ⟨⟨hv, hu⟩, hM⟩
  · intro h i hg
    exact h (i 0) (i 1) hg.1.1 hg.1.2 hg.2

theorem realize_meanFlip :
    letI := meanStruc (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanFlip L a) ↔
      ∀ (v : A ⊕ Fin m) (y : Fin a → A ⊕ Fin m), ¬IsOld v → (∀ i, IsOld (y i)) →
        ∃ u : A ⊕ Fin m, ¬IsOld u ∧
          ∀ w : Fin a → A ⊕ Fin m,
            meaningOf ρ u w ↔ (meaningOf ρ v w ↔ ¬∀ i, w i = y i) := by
  let := meanStruc (L := L) ρ
  rw [meanFlip, Sentence.Realize, Formula.realize_iAlls]
  simp only [Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_iff, Formula.realize_iInf,
    Formula.realize_equal, realize_oldAtomM, realize_meanAtom]
  constructor
  · intro h v y hv hy
    obtain ⟨u, hu⟩ := h (fun o => o.elim v y) ⟨hv, hy⟩
    exact ⟨u 0, hu.1, hu.2⟩
  · intro h i hg
    obtain ⟨u, hu, hw⟩ := h (i none) (fun j => i (some j)) hg.1 hg.2
    exact ⟨fun _ => u, hu, hw⟩

theorem xor_iff_iff_not (p q : Prop) : Xor p q ↔ (p ↔ ¬q) := by
  by_cases hq : q
  · simp [Xor, hq]
  · simp [Xor, hq]

/-- **The guard makes the meanings a bijection**: with the four conditions, the
invented values name every `a`-ary relation of the instance, each exactly once.
This is where the counting of
`DescriptiveComplexity.SecondOrderNewCount` is spent. -/
theorem bijective_meanAt [Finite A]
    (hshaped : ∀ (v : A ⊕ Fin m) (w : Fin a → A ⊕ Fin m),
      meaningOf ρ v w → ¬IsOld v ∧ ∀ i, IsOld (w i))
    (hempty : ∃ v : A ⊕ Fin m, ¬IsOld v ∧ ∀ w, ¬meaningOf ρ v w)
    (hinj : ∀ v u : A ⊕ Fin m, ¬IsOld v → ¬IsOld u →
      (∀ w, meaningOf ρ v w ↔ meaningOf ρ u w) → v = u)
    (hflip : ∀ (v : A ⊕ Fin m) (y : Fin a → A ⊕ Fin m), ¬IsOld v → (∀ i, IsOld (y i)) →
      ∃ u, ¬IsOld u ∧ ∀ w, meaningOf ρ u w ↔ (meaningOf ρ v w ↔ ¬∀ i, w i = y i)) :
    Function.Bijective (meanAt ρ) := by
  classical
  have hnew : ∀ i : Fin m, ¬IsOld (Sum.inr i : A ⊕ Fin m) := fun _ h => h
  refine bijective_of_flipClosedP _ ?_ ?_ ?_
  · intro i j h
    have : (Sum.inr i : A ⊕ Fin m) = Sum.inr j := by
      refine hinj _ _ (hnew i) (hnew j) fun w => ?_
      by_cases hw : ∀ k, ∃ x : A, w k = Sum.inl x
      · choose x hx using hw
        have hwx : w = fun k => Sum.inl (x k) := funext hx
        rw [hwx]
        exact iff_of_eq (congrFun h x)
      · obtain ⟨k, hk⟩ := not_forall.mp hw
        refine iff_of_false (fun hc => ?_) (fun hc => ?_)
        · obtain ⟨-, hold⟩ := hshaped _ _ hc
          match hkk : w k with
          | Sum.inl b => exact hk ⟨b, hkk⟩
          | Sum.inr b =>
            have := hold k
            rw [hkk] at this
            exact this
        · obtain ⟨-, hold⟩ := hshaped _ _ hc
          match hkk : w k with
          | Sum.inl b => exact hk ⟨b, hkk⟩
          | Sum.inr b =>
            have := hold k
            rw [hkk] at this
            exact this
    exact Sum.inr_injective this
  · obtain ⟨v, hv, hw⟩ := hempty
    match hvv : v with
    | Sum.inl b => exact absurd trivial hv
    | Sum.inr i => exact ⟨i, fun w => hw fun k => Sum.inl (w k)⟩
  · intro i y
    obtain ⟨u, hu, hw⟩ := hflip (Sum.inr i) (fun k => Sum.inl (y k)) (hnew i) fun _ => trivial
    match huu : u with
    | Sum.inl b => exact absurd trivial hu
    | Sum.inr j =>
      refine ⟨j, fun w => ?_⟩
      have := hw fun k => Sum.inl (w k)
      refine this.trans ((iff_congr Iff.rfl ?_).trans (xor_iff_iff_not _ _).symm)
      refine not_congr ⟨fun h => funext fun k => Sum.inl_injective (h k), fun h k => ?_⟩
      rw [h]

/-- **The whole guard, realized**, and what it buys: the invented values name
every `a`-ary relation of the instance, each exactly once. -/
theorem bijective_meanAt_of_guard [Finite A] :
    letI := meanStruc (L := L) ρ
    ((A ⊕ Fin m) ⊨ meanGuard L a) → Function.Bijective (meanAt ρ) := by
  let := meanStruc (L := L) ρ
  intro h
  obtain ⟨⟨⟨hshaped, hempty⟩, hinj⟩, hflip⟩ :=
    (Sentence.realize_inf (A ⊕ Fin m)).mp h |>.imp
      (fun h' => (Sentence.realize_inf (A ⊕ Fin m)).mp h' |>.imp
        (fun h'' => (Sentence.realize_inf (A ⊕ Fin m)).mp h'') id) id
  exact bijective_meanAt ρ ((realize_meanShaped ρ).mp hshaped)
    ((realize_meanEmpty ρ).mp hempty) ((realize_meanInj ρ).mp hinj)
    ((realize_meanFlip ρ).mp hflip)

end Realize

end DescriptiveComplexity
