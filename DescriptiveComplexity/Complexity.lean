/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered

/-!
# Abstract complexity classes, the polynomial hierarchy, and NP-completeness

Complexity classes are introduced *abstractly*: a `ComplexityClass` assigns to
decision problems (over arbitrary vocabularies) a membership predicate and a
hardness predicate, and is required to be closed under (ordered) first-order
reductions — membership downward (`P ≤ᶠᵒ Q` and `Q ∈ 𝒞` give `P ∈ 𝒞`),
hardness upward (`P ≤ᶠᵒ Q` and `P` `𝒞`-hard give `Q` `𝒞`-hard). Since FO
reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, every class from
LOGSPACE up is closed in this sense, so this is a mild requirement. Note that
closure must be part of the *definition* of a complexity class rather than an
axiom quantified over all classes: arbitrary collections of problems need not
be closed, and the quantified axiom would be inconsistent.

This file also defines the complement of a decision problem
(`DecisionProblem.compl`, notation `Pᶜ`).

The polynomial hierarchy itself — `DescriptiveComplexity.SigmaP`/`DescriptiveComplexity.PiP`, with
levels `k ≥ 1` *defined* by second-order quantifier alternation and level 0
left as an empty placeholder — lives in `DescriptiveComplexity.Hierarchy`; the Cook–Levin
theorem lives with the problem SAT in `DescriptiveComplexity.Problems.Sat`, and
completeness theorems for other problems in their files under
`DescriptiveComplexity/Problems/` (e.g. `DescriptiveComplexity.threeCol_NP_complete` in
`DescriptiveComplexity.Problems.ThreeColorability`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- An abstract complexity class: a collection of decision problems (its
`Mem`bership predicate) together with a `Hard`ness predicate, closed under
(ordered) first-order reductions. Both predicates are left completely
abstract; the closure requirements are sound for every class containing
LOGSPACE, since (ordered) FO reductions are computable in AC⁰. -/
structure ComplexityClass where
  /-- The problems belonging to the class. Use the notation `P ∈ 𝒞`. -/
  Mem : ∀ {L : Language.{0, 0}}, DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to ("`𝒞`-hard"). -/
  Hard : ∀ {L : Language.{0, 0}}, DecisionProblem L → Prop
  /-- Membership travels backward along FO reductions. -/
  mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Mem Q → Mem P
  /-- Hardness travels forward along FO reductions. -/
  hard_of_foReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Hard P → Hard Q
  /-- Membership travels backward along ordered FO reductions. -/
  mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P
  /-- Hardness travels forward along ordered FO reductions. -/
  hard_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Complexity classes speak about *finite* instances only: membership does
  not depend on the behavior of a problem on infinite structures. -/
  mem_congr_finite : ∀ {L : Language.{0, 0}} {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)
  /-- Hardness, too, only depends on the finite instances of a problem. -/
  hard_congr_finite : ∀ {L : Language.{0, 0}} {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Hard P ↔ Hard Q)

/-- `P ∈ 𝒞`: the problem `P` belongs to the complexity class `𝒞`. (This
overloads the `∈` notation; the `Membership` class cannot be used here since
the element type `DecisionProblem L` is not determined by `ComplexityClass`.) -/
scoped notation:50 P:51 " ∈ " C:51 => ComplexityClass.Mem C P

namespace ComplexityClass

/-- The empty complexity class: no members, and every problem vacuously hard
(there is nothing that would have to reduce to it). It is a placeholder for
levels of a hierarchy that are not (yet) characterized logically. -/
def empty : ComplexityClass where
  Mem _ := False
  Hard _ := True
  mem_of_foReduction _ h := h
  hard_of_foReduction _ _ := trivial
  mem_of_orderedReduction _ h := h
  hard_of_orderedReduction _ _ := trivial
  mem_congr_finite _ := Iff.rfl
  hard_congr_finite _ := Iff.rfl

/-- Inclusion of complexity classes. -/
instance : HasSubset ComplexityClass :=
  ⟨fun C D => ∀ ⦃L : Language.{0, 0}⦄ ⦃P : DecisionProblem L⦄, C.Mem P → D.Mem P⟩

variable (C : ComplexityClass) {L : Language.{0, 0}}

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def Complete (P : DecisionProblem L) : Prop :=
  P ∈ C ∧ C.Hard P

theorem Complete.mem {P : DecisionProblem L} (h : C.Complete P) : P ∈ C := h.1

theorem Complete.hard {P : DecisionProblem L} (h : C.Complete P) : C.Hard P := h.2

end ComplexityClass

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
protected def DecisionProblem.compl {L : Language.{0, 0}} (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

instance {L : Language.{0, 0}} : Compl (DecisionProblem L) :=
  ⟨DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} (P : DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

end DescriptiveComplexity
