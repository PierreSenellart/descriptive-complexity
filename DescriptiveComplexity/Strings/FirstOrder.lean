/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
import DescriptiveComplexity.Strings.Lax.FixedPointSemantics

/-!
# Translating first-order formulas into other syntaxes

A first-order formula of a relational Mathlib language has a finite syntax over
equality, atoms, implication, and universal quantification. Every syntax with
truth, equality, atoms, negation, conjunction, and existential quantification
receives it: such a syntax is a `DescriptiveComplexity.Strings.FOAlg`, and
`DescriptiveComplexity.Strings.FOAlg.tr` is the translation, proved correct once
(`DescriptiveComplexity.Strings.FOAlg.Sem.eval_tr`) for every semantics satisfying
the laws of `DescriptiveComplexity.Strings.FOAlg.Sem`.

Atoms are a parameter, and an atom may be translated to an arbitrary formula. So the
translation is also a substitution: the fixed-point developments use it to replace
a relation symbol by a fixed-point formula, or by a relation with more coordinates.

The source and the target disagree on which variable a quantifier binds: Mathlib's
binds the last, the archive's binds variable zero. The translation is parameterized
by where each source variable lives in the target's context, which makes that
disagreement a matter of one map (`DescriptiveComplexity.Strings.FOAlg.liftPos`).
-/

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure

/-- A syntax that can receive first-order formulas over the relation symbols of `K`:
formulas in a context of `m` variables, and the connectives. The last two fields say
where a quantifier puts its variable, and the others. -/
structure FOAlg (K : Language.{0, 0}) where
  /-- The formulas in a context of `m` variables. -/
  T : ℕ → Type
  /-- Truth. -/
  truth : ∀ {m}, T m
  /-- Equality. -/
  equal : ∀ {m}, Fin m → Fin m → T m
  /-- The translation of an atom. -/
  atom : ∀ {m n}, K.Relations n → (Fin n → Fin m) → T m
  /-- Negation. -/
  neg : ∀ {m}, T m → T m
  /-- Conjunction. -/
  conj : ∀ {m}, T m → T m → T m
  /-- Existential quantification. -/
  ex : ∀ {m}, T (m + 1) → T m
  /-- The position of the quantified variable. -/
  new : ∀ m, Fin (m + 1)
  /-- The positions of the other variables, under a quantifier. -/
  shift : ∀ m, Fin m → Fin (m + 1)

namespace FOAlg

variable {K : Language.{0, 0}} [K.IsRelational]

/-- The only variable of a term of a relational language. -/
def termPos {β : Type} : K.Term β → β
  | .var x => x
  | .func f _ => isEmptyElim f

theorem realize_term {A : Type} [K.Structure A] {β : Type} (v : β → A) (t : K.Term β) :
    t.realize v = v (termPos t) := by
  cases t with
  | var x => rfl
  | func f _ => exact isEmptyElim f

variable (G : FOAlg K)

/-- The positions of the source variables, under a quantifier: the new last variable
of the source is the quantified variable of the target. -/
def liftPos {α : Type} {n m : ℕ} (f : α ⊕ Fin n → Fin m) : α ⊕ Fin (n + 1) → Fin (m + 1)
  | .inl a => G.shift m (f (.inl a))
  | .inr i => Fin.lastCases (G.new m) (fun j => G.shift m (f (.inr j))) i

/-- The translation, the source variables living in the target's context at the
positions `f`. -/
def tr {α : Type} : ∀ {n : ℕ} (_ : K.BoundedFormula α n) {m : ℕ} (_ : α ⊕ Fin n → Fin m), G.T m
  | _, .falsum, _, _ => G.neg G.truth
  | _, .equal t₁ t₂, _, f => G.equal (f (termPos t₁)) (f (termPos t₂))
  | _, .rel R ts, _, f => G.atom R fun i => f (termPos (ts i))
  | _, .imp φ ψ, _, f => G.neg (G.conj (tr φ f) (G.neg (tr ψ f)))
  | _, .all φ, _, f => G.neg (G.ex (G.neg (tr φ (G.liftPos f))))

/-- A semantics of a syntax on the structure `A`, for which the translation is
correct. -/
structure Sem (A : Type) [K.Structure A] (ev : ∀ {m}, G.T m → (Fin m → A) → Prop) : Prop where
  truth : ∀ {m} (w : Fin m → A), ev G.truth w
  equal : ∀ {m} (x y : Fin m) (w : Fin m → A), ev (G.equal x y) w ↔ w x = w y
  atom : ∀ {m n} (R : K.Relations n) (a : Fin n → Fin m) (w : Fin m → A),
    ev (G.atom R a) w ↔ RelMap R (w ∘ a)
  neg : ∀ {m} (φ : G.T m) (w : Fin m → A), ev (G.neg φ) w ↔ ¬ ev φ w
  conj : ∀ {m} (φ ψ : G.T m) (w : Fin m → A), ev (G.conj φ ψ) w ↔ ev φ w ∧ ev ψ w
  ex : ∀ {m} (φ : G.T (m + 1)) (w : Fin m → A),
    ev (G.ex φ) w ↔ ∃ w' : Fin (m + 1) → A, w' ∘ G.shift m = w ∧ ev φ w'
  ext : ∀ {m} (a : A) (w : Fin m → A),
    ∃ w' : Fin (m + 1) → A, w' ∘ G.shift m = w ∧ w' (G.new m) = a

/-- **The translation is correct.** -/
theorem Sem.eval_tr {A : Type} [K.Structure A] {G : FOAlg K}
    {ev : ∀ {m}, G.T m → (Fin m → A) → Prop} (h : Sem G A ev) {α : Type} {n : ℕ}
    (φ : K.BoundedFormula α n) {m : ℕ} (f : α ⊕ Fin n → Fin m) (w : Fin m → A) :
    ev (G.tr φ f) w ↔ φ.Realize (fun a => w (f (.inl a))) (fun i => w (f (.inr i))) := by
  have helim : ∀ {n : ℕ} {m : ℕ} (f : α ⊕ Fin n → Fin m) (w : Fin m → A),
      Sum.elim (fun a => w (f (.inl a))) (fun i => w (f (.inr i))) = fun x => w (f x) := by
    intro n m f w
    funext x
    cases x <;> rfl
  induction φ generalizing m with
  | falsum =>
    simp only [tr, h.neg, h.truth, BoundedFormula.Realize]
    simp
  | equal t₁ t₂ =>
    rw [tr, h.equal, BoundedFormula.Realize, helim, realize_term, realize_term]
  | rel R ts =>
    rw [tr, h.atom, BoundedFormula.Realize, helim]
    refine iff_of_eq (congrArg _ (funext fun i => ?_))
    rw [realize_term]
    rfl
  | imp φ ψ ih₁ ih₂ =>
    have e₁ := ih₁ f w
    have e₂ := ih₂ f w
    rw [tr, h.neg, h.conj, h.neg, BoundedFormula.Realize]
    tauto
  | all φ ih =>
    rw [tr, h.neg, h.ex, BoundedFormula.Realize]
    have key : ∀ w' : Fin (m + 1) → A, w' ∘ G.shift m = w →
        (φ.Realize (fun a => w' (G.liftPos f (.inl a))) (fun i => w' (G.liftPos f (.inr i))) ↔
          φ.Realize (fun a => w (f (.inl a)))
            (Fin.snoc (fun i => w (f (.inr i))) (w' (G.new m)))) := by
      rintro w' rfl
      refine iff_of_eq (congrArg₂ _ rfl (funext fun i => ?_))
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftPos]
      · simp [liftPos]
    constructor
    · intro hn a
      obtain ⟨w', hw', ha⟩ := h.ext a w
      by_contra hc
      refine hn ⟨w', hw', ?_⟩
      rw [h.neg]
      intro hi
      exact hc (ha ▸ (key w' hw').mp ((ih (G.liftPos f) w').mp hi))
    · rintro hall ⟨w', hw', hc⟩
      rw [h.neg] at hc
      exact hc ((ih (G.liftPos f) w').mpr ((key w' hw').mpr (hall _)))

end FOAlg

/-! ### The syntaxes of the archive -/

section Instances

variable {K : Language.{0, 0}}

/-- The existential second-order matrices receive first-order formulas whose atoms
are given. -/
def esoAlg (σ τ : Lax.FiniteStructures.Vocabulary)
    (atom : ∀ {m n}, K.Relations n → (Fin n → Fin m) →
      Lax.ExistentialSecondOrder.FirstOrder σ τ m) : FOAlg K where
  T m := Lax.ExistentialSecondOrder.FirstOrder σ τ m
  truth := .truth
  equal := .equal
  atom := atom
  neg := .neg
  conj := .conj
  ex := .exists'
  new _ := 0
  shift _ := Fin.succ

/-- The formulas of FO(LFP) satisfying a property closed under the connectives receive
first-order formulas whose atoms are given and satisfy it. -/
def rawAlg (σ : Lax.OrderedStructures.Vocabulary) (ρ : List ℕ)
    (Good : ∀ {m}, Lax.FixedPointSyntax.RawFormula σ m ρ → Prop)
    (hT : ∀ {m}, Good (.truth : Lax.FixedPointSyntax.RawFormula σ m ρ))
    (hE : ∀ {m} (x y : Fin m), Good (.equal x y : Lax.FixedPointSyntax.RawFormula σ m ρ))
    (hN : ∀ {m} {φ : Lax.FixedPointSyntax.RawFormula σ m ρ}, Good φ → Good (.neg φ))
    (hC : ∀ {m} {φ ψ : Lax.FixedPointSyntax.RawFormula σ m ρ}, Good φ → Good ψ → Good (.conj φ ψ))
    (hX : ∀ {m} {φ : Lax.FixedPointSyntax.RawFormula σ (m + 1) ρ}, Good φ → Good (.exists' φ))
    (atom : ∀ {m n}, K.Relations n → (Fin n → Fin m) →
      {φ : Lax.FixedPointSyntax.RawFormula σ m ρ // Good φ}) : FOAlg K where
  T m := {φ : Lax.FixedPointSyntax.RawFormula σ m ρ // Good φ}
  truth := ⟨.truth, hT⟩
  equal x y := ⟨.equal x y, hE x y⟩
  atom := atom
  neg φ := ⟨.neg φ.1, hN φ.2⟩
  conj φ ψ := ⟨.conj φ.1 ψ.1, hC φ.2 ψ.2⟩
  ex φ := ⟨.exists' φ.1, hX φ.2⟩
  new _ := 0
  shift _ := Fin.succ

end Instances

end DescriptiveComplexity.Strings
