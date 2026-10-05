/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax485149Proofs.DescriptiveComplexity.Interpretation
import Mathlib.Logic.Equiv.Fin.Basic
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149Proofs.DescriptiveComplexity.DecisionProblem
end Lax485149Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax485149Proofs.DescriptiveComplexity.FOInterpretation
end Lax485149Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity.FOReduction
end Lax485149Proofs.DescriptiveComplexity.FOReduction

namespace Lax485149Proofs.Foreign.FirstOrder.Language.Term
end Lax485149Proofs.Foreign.FirstOrder.Language.Term

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax485149Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax485149Proofs.DescriptiveComplexity

namespace Lax485149Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation FOReduction)
end Lax485149Proofs.DescriptiveComplexity

/-!
# Composition of first-order reductions (transitivity)

The composite of two FO interpretations is an FO interpretation
(`DescriptiveComplexity.FOInterpretation.comp`), and hence FO reducibility is transitive
(`DescriptiveComplexity.FOReduction.trans`): from `P ≤ᶠᵒ Q` and `Q ≤ᶠᵒ R` one gets
`P ≤ᶠᵒ R`.

The composite of an interpretation `I : FOInterpretation L₁ L₂ Tag₁ d₁` with
`J : FOInterpretation L₂ L₃ Tag₂ d₂` has tags `Tag₂ × (Fin d₂ → Tag₁)` and
dimension `d₂ * d₁`: an element of the composite universe carries the outer
tag, one inner tag per outer coordinate, and a `d₂ × d₁` matrix of elements.
Its defining formulas are obtained by *pulling back* the defining `L₂`-formulas
of `J` through `I` (`DescriptiveComplexity.FOInterpretation.pull`): atoms become the
defining formulas of `I`, equality becomes componentwise equality (with tags
compared statically), and a quantifier over the universe of `I.Map A` becomes
a finite conjunction/disjunction over `Tag₁` of a block of `d₁` quantifiers
over `A`.

Two points deserve attention:

* the composite's universe `(Tag₂ × (Fin d₂ → Tag₁)) × A^(d₂·d₁)` is only
  *isomorphic* (`DescriptiveComplexity.FOInterpretation.compLEquiv`), not equal, to the
  twice-interpreted `J.Map (I.Map A)`; transitivity therefore uses the
  isomorphism-invariance of the target problem, which is part of the notion
  of `DecisionProblem`;
* pulling back quantifiers requires enumerating the (finitely many) inner
  tags, so composite formulas are noncomputable (they are built with
  `BoundedFormula.iInf`); this does not affect any of the theorems.
-/

/-! ### Terms of a relational language are variables

These extend Mathlib's `FirstOrder.Language.Term` and live in its namespace
(where Mathlib would want them, and where dot notation finds them). -/

namespace FirstOrder

open Language

variable {L₂ : Language.{0, 0}}

open Lax485149Proofs.Foreign.FirstOrder.Language.Term in
/-- In a relational language, every term is a variable. -/
def _root_.Lax485149Proofs.Foreign.FirstOrder.Language.Term.varOf [L₂.IsRelational] {γ : Type*} : L₂.Term γ → γ
  | .var x => x
  | .func f _ => isEmptyElim f

namespace Language.Term
export Lax485149Proofs.Foreign.FirstOrder.Language.Term (varOf)
end Language.Term

open Lax485149Proofs.Foreign.FirstOrder.Language.Term in
@[simp]
theorem _root_.Lax485149Proofs.Foreign.FirstOrder.Language.Term.varOf_var [L₂.IsRelational] {γ : Type*} (x : γ) :
    (Term.var x : L₂.Term γ).varOf = x :=
  rfl

namespace Language.Term
export Lax485149Proofs.Foreign.FirstOrder.Language.Term (varOf_var)
end Language.Term

open Lax485149Proofs.Foreign.FirstOrder.Language.Term in
@[simp]
theorem _root_.Lax485149Proofs.Foreign.FirstOrder.Language.Term.realize_varOf [L₂.IsRelational] {γ : Type*} {M : Type*} [L₂.Structure M]
    {v : γ → M} (t : L₂.Term γ) : t.realize v = v t.varOf := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

namespace Language.Term
export Lax485149Proofs.Foreign.FirstOrder.Language.Term (realize_varOf)
end Language.Term

end FirstOrder

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

/-! ### Pulling back a formula through an interpretation -/

section Pull

variable {Tag : Type} {d : ℕ} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {β : Type}

/-- The environment of the interpreted structure induced by tags `τ` and an
environment `v` for the individual coordinates. -/
def FOInterpretation.liftEnv (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {A : Type} {γ : Type}
    (τ : γ → Tag) (v : γ × Fin d → A) (b : γ) : I.Map A :=
  (τ b, fun j => v (b, j))

end Pull

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax485149Proofs.DescriptiveComplexity.FOInterpretation (liftEnv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Pull

variable {Tag : Type} {d : ℕ} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {β : Type}

/-- Relabeling that splits off the coordinates of the last bound variable. -/
private def splitLast {β : Type} {d n : ℕ} :
    (β ⊕ Fin (n + 1)) × Fin d → ((β ⊕ Fin n) × Fin d) ⊕ Fin d
  | (.inl b, j) => .inl (.inl b, j)
  | (.inr i, j) => Fin.lastCases (.inr j) (fun i' => .inl (.inr i', j)) i

/-- Extending a tag assignment to one more bound variable. -/
private def extendTag {β : Type} {n : ℕ} (τ : (β ⊕ Fin n) → Tag) (t : Tag) :
    (β ⊕ Fin (n + 1)) → Tag :=
  Sum.elim (fun b => τ (.inl b)) (Fin.snoc (fun i => τ (.inr i)) t)

open Classical in
/-- Pullback of an `L₂`-formula through the interpretation `I`, given a static
assignment of tags to its (free and bound) variables: an `L₁`-formula on the
coordinates which realizes in `A` exactly as the original formula realizes in
`I.Map A` (see `FOInterpretation.realize_pull`). Quantified variables are
expanded into a conjunction over the (finitely many) tags of a block of `d`
quantifiers. -/
noncomputable def FOInterpretation.pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    [L₂.IsRelational] [Finite Tag] :
    ∀ {n : ℕ}, L₂.BoundedFormula β n → ((β ⊕ Fin n) → Tag) → L₁.Formula ((β ⊕ Fin n) × Fin d)
  | _, .falsum, _ => ⊥
  | _, .equal t₁ t₂, τ =>
      if τ t₁.varOf = τ t₂.varOf then
        Formula.iInf fun j : Fin d =>
          Term.equal (Term.var (t₁.varOf, j)) (Term.var (t₂.varOf, j))
      else ⊥
  | _, .rel R ts, τ =>
      (I.relFormula R fun i => τ (ts i).varOf).relabel fun p => ((ts p.1).varOf, p.2)
  | _, .imp φ ψ, τ =>
      (FOInterpretation.pull I φ τ).imp (FOInterpretation.pull I ψ τ)
  | _, .all φ, τ =>
      Formula.iInf fun t : Tag =>
        ((FOInterpretation.pull I φ (extendTag τ t)).relabel splitLast).iAlls (Fin d)

end Pull

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax485149Proofs.DescriptiveComplexity.FOInterpretation (pull)

end Lax904597.Interpretations.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Pull

variable {Tag : Type} {d : ℕ} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {β : Type}

theorem FOInterpretation.realize_pull [L₂.IsRelational] [Finite Tag] {A : Type}
    [L₁.Structure A] {n : ℕ} (φ : L₂.BoundedFormula β n) (τ : (β ⊕ Fin n) → Tag)
    (v : ((β ⊕ Fin n) × Fin d) → A) :
    (I.pull φ τ).Realize v ↔
      φ.Realize (M := I.Map A) (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) := by
  induction φ with
  | falsum =>
    simp only [FOInterpretation.pull, Formula.realize_bot, false_iff]
    exact fun h => h
  | equal t₁ t₂ =>
    have hRHS : (BoundedFormula.equal t₁ t₂).Realize (M := I.Map A)
        (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
        I.liftEnv τ v t₁.varOf = I.liftEnv τ v t₂.varOf := by
      rw [show (BoundedFormula.equal t₁ t₂).Realize (M := I.Map A)
          (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
          t₁.realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) =
            t₂.realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) from
          Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS]
    simp only [FOInterpretation.pull]
    split_ifs with h
    · rw [Formula.realize_iInf]
      simp only [Formula.realize_equal, Term.realize_var]
      exact ⟨fun hj => Prod.ext_iff.mpr ⟨h, funext hj⟩,
        fun hpq j => congrFun (congrArg Prod.snd hpq) j⟩
    · simp only [Formula.realize_bot, false_iff]
      exact fun hpq => h (congrArg Prod.fst hpq)
  | rel R ts =>
    have hRHS : (BoundedFormula.rel R ts).Realize (M := I.Map A)
        (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
        RelMap (M := I.Map A) R fun i => I.liftEnv τ v (ts i).varOf := by
      rw [show (BoundedFormula.rel R ts).Realize (M := I.Map A)
          (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr) ↔
          RelMap (M := I.Map A) R fun i =>
            (ts i).realize (Sum.elim (I.liftEnv τ v ∘ Sum.inl) (I.liftEnv τ v ∘ Sum.inr)) from
          Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS, FOInterpretation.relMap_map]
    simp only [FOInterpretation.pull, Formula.realize_relabel]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    simp only [FOInterpretation.pull, Formula.realize_imp, BoundedFormula.realize_imp,
      ihφ, ihψ]
  | all φ ih =>
    simp only [FOInterpretation.pull, Formula.realize_iInf, Formula.realize_iAlls,
      Formula.realize_relabel, BoundedFormula.realize_all]
    have hE₁ : ∀ (t : Tag) (w : Fin d → A),
        I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) ∘ Sum.inl =
          I.liftEnv τ v ∘ Sum.inl := by
      intro t w
      funext b
      rfl
    -- `Fin.snoc` lemmas, instantiated at the interpreted universe with
    -- variable arguments (so that they elaborate without pair literals in
    -- `I.Map A`-typed positions, which `simp`/`rw` matching cannot handle)
    have hlast : ∀ {m : ℕ} (g : Fin m → I.Map A) (a : I.Map A),
        Fin.snoc (α := fun _ => I.Map A) g a (Fin.last m) = a := fun g a => by simp
    have hcs : ∀ {m : ℕ} (g : Fin m → I.Map A) (a : I.Map A) (i' : Fin m),
        Fin.snoc (α := fun _ => I.Map A) g a i'.castSucc = g i' := fun g a i' => by simp
    have hE₂ : ∀ (t : Tag) (w : Fin d → A),
        I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) ∘ Sum.inr =
          Fin.snoc (I.liftEnv τ v ∘ Sum.inr) (t, w) := by
      intro t w
      funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Eq.trans ?_ (hlast _ _).symm
        change I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) (Sum.inr (Fin.last _)) =
          (t, w)
        unfold FOInterpretation.liftEnv extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
      · refine Eq.trans ?_ (hcs _ _ _).symm
        change I.liftEnv (extendTag τ t) (Sum.elim v w ∘ splitLast) (Sum.inr i'.castSucc) =
          I.liftEnv τ v (Sum.inr i')
        unfold FOInterpretation.liftEnv extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
    constructor
    · rintro h ⟨t, w⟩
      have := (ih (extendTag τ t) (Sum.elim v w ∘ splitLast)).mp (h t w)
      rwa [hE₁, hE₂] at this
    · intro h t w
      refine (ih (extendTag τ t) (Sum.elim v w ∘ splitLast)).mpr ?_
      rw [hE₁, hE₂]
      exact h (t, w)

end Pull

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax485149Proofs.DescriptiveComplexity.FOInterpretation (realize_pull)

end Lax904597.Interpretations.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Pull

variable {Tag : Type} {d : ℕ} (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d) {β : Type}

end Pull

/-! ### Composition of interpretations -/

section Comp

variable {Tag₁ Tag₂ : Type} {d₁ d₂ : ℕ}

variable [L₂.IsRelational] [L₃.IsRelational] [Finite Tag₁]

variable (J : Lax904597.Interpretations.FOInterpretation L₂ L₃ Tag₂ d₂) (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag₁ d₁)

variable (A : Type) [L₁.Structure A]

end Comp

/-! ### Transitivity of FO reductions -/

section Trans

variable {Tag₁ Tag₂ : Type} {d₁ d₂ : ℕ}

variable [L₂.IsRelational] [L₃.IsRelational] [Finite Tag₁]

end Trans

/-! ### Reflexivity and the preorder structure -/

section Refl

variable (L : Language.{0, 0})

/-- The identity interpretation of a language in itself (one tag, dimension
one). -/
def FOInterpretation.refl : Lax904597.Interpretations.FOInterpretation L L Unit 1 where
  relFormula {_n} R := fun _ => R.formula fun i => Term.var (i, 0)

end Refl

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax485149Proofs.DescriptiveComplexity.FOInterpretation (refl)

end Lax904597.Interpretations.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Refl

variable (L : Language.{0, 0})

variable [L.IsRelational] (A : Type) [L.Structure A]

/-- The identity interpretation of a structure is isomorphic to the structure
itself. -/
def FOInterpretation.reflLEquiv : (FOInterpretation.refl L).Map A ≃[L] A where
  toFun x := x.2 0
  invFun a := ((), fun _ => a)
  left_inv := fun x =>
    Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
  right_inv := fun _ => rfl
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun _ _ => Iff.rfl

end Refl

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax485149Proofs.DescriptiveComplexity.FOInterpretation (reflLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Refl

variable (L : Language.{0, 0})

variable [L.IsRelational] (A : Type) [L.Structure A]

variable {L} {A}

/-- **Reflexivity of FO reductions**: every decision problem (over a
relational language) reduces to itself, via the identity interpretation. -/
def FOReduction.refl (P : Lax904597.Problems.DecisionProblem L) : P ≤ᶠᵒ P where
  Tag := Unit
  dim := 1
  toInterpretation := FOInterpretation.refl L
  correct A _ _ _ := (P.iso_invariant (FOInterpretation.reflLEquiv L A)).symm

end Refl

end Lax485149Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax485149Proofs.DescriptiveComplexity.FOReduction (refl)

end Lax904597.Interpretations.FOReduction

namespace Lax485149Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Refl

variable (L : Language.{0, 0})

variable [L.IsRelational] (A : Type) [L.Structure A]

variable {L} {A}

end Refl

end Lax485149Proofs.DescriptiveComplexity


