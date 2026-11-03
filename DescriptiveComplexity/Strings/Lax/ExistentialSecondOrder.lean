/-
Mirror of `Lax988886.ExistentialSecondOrder`: lax-988886, “Fagin's theorem”, formalized by Szymon
Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
module

public import DescriptiveComplexity.Strings.Lax.FiniteStructures

/-!
# Existential second-order logic

An existential second-order sentence has the form `∃ R₁ … ∃ Rₛ, φ`, where each
relation has a fixed arity and the matrix `φ` is first-order. Witness relations
range over all relations of their arities on the existing universe.

The first-order basis consists of truth, equality, input-relation and
witness-relation atoms, negation, conjunction, and existential element
quantification. There is no built-in order or fixed-point operator. Element
quantification binds variable zero. The witness vocabulary records the finite
second-order quantifier prefix.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder

open FiniteStructures

/-- First-order formulas over an input and a witness vocabulary. -/
inductive FirstOrder (σ τ : Vocabulary) : Nat → Type
  | truth {m} : FirstOrder σ τ m
  | equal {m} (x y : Fin m) : FirstOrder σ τ m
  | relation {m} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) : FirstOrder σ τ m
  | variable {m} (r : Symbol τ) (args : Fin (τ.get r) → Fin m) : FirstOrder σ τ m
  | neg {m} (φ : FirstOrder σ τ m) : FirstOrder σ τ m
  | conj {m} (φ ψ : FirstOrder σ τ m) : FirstOrder σ τ m
  | exists' {m} (φ : FirstOrder σ τ (m + 1)) : FirstOrder σ τ m

/-- The semantics of a first-order formula. -/
def FirstOrder.eval {σ τ : Vocabulary} {m : Nat} (φ : FirstOrder σ τ m)
    (A : Structure σ) (R : Interpretation τ A.size) (v : Fin m → Fin A.size) : Prop :=
  match φ with
  | .truth => True
  | .equal x y => v x = v y
  | .relation r args => A.relation r (v ∘ args) = true
  | .variable r args => R r (v ∘ args) = true
  | .neg ψ => ¬ ψ.eval A R v
  | .conj ψ χ => ψ.eval A R v ∧ χ.eval A R v
  | .exists' ψ => ∃ a : Fin A.size, ψ.eval A R (Fin.cons a v)

/-- An existential second-order sentence. -/
structure Sentence (σ : Vocabulary) where
  /-- The vocabulary of the quantified relations. -/
  witnesses : Vocabulary
  /-- The first-order matrix. -/
  matrix : FirstOrder σ witnesses 0

/-- A structure satisfies a sentence: some witness relations satisfy its matrix. -/
def Satisfies {σ : Vocabulary} (A : Structure σ) (φ : Sentence σ) : Prop :=
  ∃ R : Interpretation φ.witnesses A.size, φ.matrix.eval A R Fin.elim0

/-- A property defined by an existential second-order sentence. -/
def Definable {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∃ φ : Sentence σ, ∀ A : Structure σ, Q A ↔ Satisfies A φ

/-- Evaluation is transported along an isomorphism, with the witnesses conjugated. -/
private theorem eval_iso {σ τ : Vocabulary} {A B : Structure σ} (e : Isomorphism A B)
    (R : Interpretation τ A.size) {m : Nat} (φ : FirstOrder σ τ m) (v : Fin m → Fin A.size) :
    φ.eval B (fun r a => R r (e.equivalence.symm ∘ a)) (e.equivalence ∘ v) ↔ φ.eval A R v := by
  induction φ with
  | truth => exact Iff.rfl
  | equal x y => simp [FirstOrder.eval]
  | relation r args =>
    simp only [FirstOrder.eval]
    rw [← e.preserves r (v ∘ args)]
    rfl
  | «variable» r args =>
    simp only [FirstOrder.eval]
    have : e.equivalence.symm ∘ (e.equivalence ∘ v) ∘ args = v ∘ args := by
      funext i; simp
    rw [this]
  | neg ψ ih => exact not_congr (ih v)
  | conj ψ χ ih₁ ih₂ => exact and_congr (ih₁ v) (ih₂ v)
  | exists' ψ ih =>
    simp only [FirstOrder.eval]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨e.equivalence.symm b, (ih _).mp ?_⟩
      have : e.equivalence ∘ Fin.cons (e.equivalence.symm b) v =
          (Fin.cons b (e.equivalence ∘ v) : Fin _ → Fin B.size) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rwa [this]
    · rintro ⟨a, ha⟩
      refine ⟨e.equivalence a, ?_⟩
      have : e.equivalence ∘ Fin.cons a v =
          (Fin.cons (e.equivalence a) (e.equivalence ∘ v) : Fin _ → Fin B.size) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [← this]
      exact (ih _).mpr ha

theorem satisfiesInvariant {σ : Vocabulary} (φ : Sentence σ) :
    IsomorphismInvariant (fun A => Satisfies A φ) := by
  have key : ∀ A B : Structure σ, Isomorphism A B → Satisfies A φ → Satisfies B φ := by
    rintro A B e ⟨R, hR⟩
    refine ⟨fun r a => R r (e.equivalence.symm ∘ a), ?_⟩
    have := (eval_iso e R φ.matrix Fin.elim0).mpr hR
    rwa [show e.equivalence ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → Fin B.size) from
      funext fun i => i.elim0] at this
  rintro A B ⟨e⟩
  refine ⟨key A B e, key B A ⟨e.equivalence.symm, fun r a => ?_⟩⟩
  rw [← e.preserves r (e.equivalence.symm ∘ a)]
  congr 1
  funext i
  simp

end DescriptiveComplexity.Strings.Lax.ExistentialSecondOrder
