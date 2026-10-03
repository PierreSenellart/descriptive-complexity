/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Interpretation
import Mathlib.Logic.Equiv.Fin.Basic
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099Proofs.DescriptiveComplexity.DecisionProblem
end Lax624099Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax624099Proofs.DescriptiveComplexity.FOInterpretation
end Lax624099Proofs.DescriptiveComplexity.FOInterpretation

namespace Lax624099Proofs.DescriptiveComplexity.FOReduction
end Lax624099Proofs.DescriptiveComplexity.FOReduction

namespace Lax624099Proofs.Foreign.FirstOrder.Language.Term
end Lax624099Proofs.Foreign.FirstOrder.Language.Term

/-!
# Composition of first-order reductions (transitivity)

The composite of two FO interpretations is an FO interpretation
(`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.comp`), and hence FO reducibility is transitive
(`Lax624099Proofs.DescriptiveComplexity.FOReduction.trans`): from `P ≤ᶠᵒ Q` and `Q ≤ᶠᵒ R` one gets
`P ≤ᶠᵒ R`.

The composite of an interpretation `I : FOInterpretation L₁ L₂ Tag₁ d₁` with
`J : FOInterpretation L₂ L₃ Tag₂ d₂` has tags `Tag₂ × (Fin d₂ → Tag₁)` and
dimension `d₂ * d₁`: an element of the composite universe carries the outer
tag, one inner tag per outer coordinate, and a `d₂ × d₁` matrix of elements.
Its defining formulas are obtained by *pulling back* the defining `L₂`-formulas
of `J` through `I` (`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.pull`): atoms become the
defining formulas of `I`, equality becomes componentwise equality (with tags
compared statically), and a quantifier over the universe of `I.Map A` becomes
a finite conjunction/disjunction over `Tag₁` of a block of `d₁` quantifiers
over `A`.

Two points deserve attention:

* the composite's universe `(Tag₂ × (Fin d₂ → Tag₁)) × A^(d₂·d₁)` is only
  *isomorphic* (`Lax624099Proofs.DescriptiveComplexity.FOInterpretation.compLEquiv`), not equal, to the
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

/-- In a relational language, every term is a variable. -/
def _root_.Lax624099Proofs.Foreign.FirstOrder.Language.Term.varOf [L₂.IsRelational] {γ : Type*} : L₂.Term γ → γ
  | .var x => x
  | .func f _ => isEmptyElim f

namespace Language.Term
export Lax624099Proofs.Foreign.FirstOrder.Language.Term (varOf)
end Language.Term

@[simp]
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.Term.varOf_var [L₂.IsRelational] {γ : Type*} (x : γ) :
    (Term.var x : L₂.Term γ).varOf = x :=
  rfl

namespace Language.Term
export Lax624099Proofs.Foreign.FirstOrder.Language.Term (varOf_var)
end Language.Term

@[simp]
theorem _root_.Lax624099Proofs.Foreign.FirstOrder.Language.Term.realize_varOf [L₂.IsRelational] {γ : Type*} {M : Type*} [L₂.Structure M]
    {v : γ → M} (t : L₂.Term γ) : t.realize v = v t.varOf := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

namespace Language.Term
export Lax624099Proofs.Foreign.FirstOrder.Language.Term (realize_varOf)
end Language.Term

end FirstOrder

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

/-! ### Pulling back a formula through an interpretation -/

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

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax624099Proofs.DescriptiveComplexity.FOInterpretation (refl)

end Lax904597.Interpretations.FOInterpretation

namespace Lax624099Proofs.DescriptiveComplexity

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

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax624099Proofs.DescriptiveComplexity.FOInterpretation (reflLEquiv)

end Lax904597.Interpretations.FOInterpretation

namespace Lax624099Proofs.DescriptiveComplexity

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

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax624099Proofs.DescriptiveComplexity.FOReduction (refl)

end Lax904597.Interpretations.FOReduction

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

section Refl

variable (L : Language.{0, 0})

variable [L.IsRelational] (A : Type) [L.Structure A]

variable {L} {A}

end Refl

end Lax624099Proofs.DescriptiveComplexity


