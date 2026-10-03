/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Interpretation
import Mathlib.Logic.Equiv.Fin.Basic
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Composition of first-order reductions (transitivity)

The composite of two FO interpretations is an FO interpretation
(`Lax799700Proofs.DescriptiveComplexity.FOInterpretation.comp`), and hence FO reducibility is transitive
(`Lax799700Proofs.DescriptiveComplexity.FOReduction.trans`): from `P ≤ᶠᵒ Q` and `Q ≤ᶠᵒ R` one gets
`P ≤ᶠᵒ R`.

The composite of an interpretation `I : FOInterpretation L₁ L₂ Tag₁ d₁` with
`J : FOInterpretation L₂ L₃ Tag₂ d₂` has tags `Tag₂ × (Fin d₂ → Tag₁)` and
dimension `d₂ * d₁`: an element of the composite universe carries the outer
tag, one inner tag per outer coordinate, and a `d₂ × d₁` matrix of elements.
Its defining formulas are obtained by *pulling back* the defining `L₂`-formulas
of `J` through `I` (`Lax799700Proofs.DescriptiveComplexity.FOInterpretation.pull`): atoms become the
defining formulas of `I`, equality becomes componentwise equality (with tags
compared statically), and a quantifier over the universe of `I.Map A` becomes
a finite conjunction/disjunction over `Tag₁` of a block of `d₁` quantifiers
over `A`.

Two points deserve attention:

* the composite's universe `(Tag₂ × (Fin d₂ → Tag₁)) × A^(d₂·d₁)` is only
  *isomorphic* (`Lax799700Proofs.DescriptiveComplexity.FOInterpretation.compLEquiv`), not equal, to the
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
def _root_.Lax799700Proofs.Foreign.FirstOrder.Language.Term.varOf [L₂.IsRelational] {γ : Type*} : L₂.Term γ → γ
  | .var x => x
  | .func f _ => isEmptyElim f

namespace Language.Term
export Lax799700Proofs.Foreign.FirstOrder.Language.Term (varOf)
end Language.Term

@[simp]
theorem _root_.Lax799700Proofs.Foreign.FirstOrder.Language.Term.varOf_var [L₂.IsRelational] {γ : Type*} (x : γ) :
    (Term.var x : L₂.Term γ).varOf = x :=
  rfl

namespace Language.Term
export Lax799700Proofs.Foreign.FirstOrder.Language.Term (varOf_var)
end Language.Term

@[simp]
theorem _root_.Lax799700Proofs.Foreign.FirstOrder.Language.Term.realize_varOf [L₂.IsRelational] {γ : Type*} {M : Type*} [L₂.Structure M]
    {v : γ → M} (t : L₂.Term γ) : t.realize v = v t.varOf := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

namespace Language.Term
export Lax799700Proofs.Foreign.FirstOrder.Language.Term (realize_varOf)
end Language.Term

end FirstOrder

namespace Lax799700Proofs.DescriptiveComplexity

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

variable [L.IsRelational] (A : Type) [L.Structure A]

variable {L} {A}

end Refl

end Lax799700Proofs.DescriptiveComplexity


