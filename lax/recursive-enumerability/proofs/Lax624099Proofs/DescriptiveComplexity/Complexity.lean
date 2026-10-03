/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Relativized
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

namespace Lax624099.ClassRE.DecisionProblem
end Lax624099.ClassRE.DecisionProblem

namespace Lax624099Proofs.DescriptiveComplexity.DecisionProblem
end Lax624099Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax624099Proofs.DescriptiveComplexity.FOReduction
end Lax624099Proofs.DescriptiveComplexity.FOReduction

namespace Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax904597.Problems.DecisionProblem
export Lax624099.ClassRE.DecisionProblem (compl)
end Lax904597.Problems.DecisionProblem

/-!
# Abstract complexity classes, the polynomial hierarchy, and NP-completeness

Complexity classes are introduced *abstractly*: a `ComplexityClass` assigns to
decision problems (over arbitrary vocabularies) a membership predicate and a
hardness predicate, and is required to be closed under (ordered) first-order
reductions – membership downward (`P ≤ᶠᵒ Q` and `Q ∈ 𝒞` give `P ∈ 𝒞`),
hardness upward (`P ≤ᶠᵒ Q` and `P` `𝒞`-hard give `Q` `𝒞`-hard). Since FO
reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, every class from
LOGSPACE up is closed in this sense, so this is a mild requirement. Note that
closure must be part of the *definition* of a complexity class rather than an
axiom quantified over all classes: arbitrary collections of problems need not
be closed, and the quantified axiom would be inconsistent.

This file also defines the complement of a decision problem
(`DecisionProblem.compl`, notation `Pᶜ`), and the observation that a reduction
complements: the same interpretation reduces `Pᶜ` to `Qᶜ`
(`Lax624099Proofs.DescriptiveComplexity.FOReduction.compl`).

The polynomial hierarchy itself – `Lax624099Proofs.DescriptiveComplexity.SigmaP`/`Lax624099Proofs.DescriptiveComplexity.PiP`, with
levels `k ≥ 1` *defined* by second-order quantifier alternation and level 0
polynomial time – lives in `Lax624099Proofs.DescriptiveComplexity.Hierarchy`; the Cook–Levin
theorem ([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]) lives
with the problem SAT in `Lax624099Proofs.DescriptiveComplexity.Problems.Sat`, and
completeness theorems for other problems in their files under
`Lax624099Proofs.DescriptiveComplexity/Problems/` (e.g., `Lax624099Proofs.DescriptiveComplexity.threeCol_NP_complete` in
`Lax624099Proofs.DescriptiveComplexity.Problems.ThreeColorability`).
-/

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- An abstract complexity class: a collection of decision problems (its
`Mem`bership predicate) together with a `Hard`ness predicate, closed under
(ordered) first-order reductions. Both predicates are left completely
abstract; the closure requirements are sound for every class containing
LOGSPACE, since (ordered) FO reductions are computable in AC⁰.

Hardness is a field of its own rather than a function of `Mem`: the naive
“every member reduces to `P`” cannot even be stated here, since a reduction
has a *relational* target while `Hard` ranges over arbitrary vocabularies. The
classes of this library take it to be cofinal hardness for their own members
and are built by `Lax624099Proofs.DescriptiveComplexity.ComplexityClass.ofMem`, which supplies both
that reading of `Hard` and the three closure proofs it needs; keeping the field
abstract leaves room for the two that read hardness differently
(`Lax624099Proofs.DescriptiveComplexity.ComplexityClass.empty`, `Lax624099Proofs.DescriptiveComplexity.PH`). -/
structure ComplexityClass where
  /-- The problems belonging to the class. Use the notation `P ∈ 𝒞`. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], Lax904597.Problems.DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to (“`𝒞`-hard”). -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], Lax904597.Problems.DecisionProblem L → Prop
  /-- Membership travels backward along FO reductions. -/
  mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}, (P ≤ᶠᵒ Q) → Mem Q → Mem P
  /-- Hardness travels forward along FO reductions. -/
  hard_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}, (P ≤ᶠᵒ Q) → Hard P → Hard Q
  /-- Membership travels backward along ordered FO reductions. -/
  mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P
  /-- Hardness travels forward along ordered FO reductions. -/
  hard_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Hardness travels forward along relativized ordered FO reductions – the
  reductions with a definable target universe, needed for spanning problems. -/
  hard_of_relOrderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'}, (P ≤ʳᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Complexity classes speak about *finite* instances only: membership does
  not depend on the behavior of a problem on infinite structures. -/
  mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)
  /-- Hardness, too, only depends on the finite instances of a problem. -/
  hard_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Hard P ↔ Hard Q)

/-- `P ∈ 𝒞`: the problem `P` belongs to the complexity class `𝒞`. (This
overloads the `∈` notation; the `Membership` class cannot be used here since
the element type `DecisionProblem L` is not determined by `ComplexityClass`.) -/
scoped notation:50 P:51 " ∈ " C:51 => ComplexityClass.Mem C P

namespace ComplexityClass

/-- Inclusion of complexity classes. -/
instance : HasSubset ComplexityClass :=
  ⟨fun C D => ∀ ⦃L : Language.{0, 0}⦄ [L.IsRelational] ⦃P : Lax904597.Problems.DecisionProblem L⦄,
    C.Mem P → D.Mem P⟩

variable (C : ComplexityClass) {L : Language.{0, 0}} [L.IsRelational]

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def Complete (P : Lax904597.Problems.DecisionProblem L) : Prop :=
  P ∈ C ∧ C.Hard P

theorem Complete.hard {P : Lax904597.Problems.DecisionProblem L} (h : C.Complete P) : C.Hard P := h.2

end ComplexityClass

instance {L : Language.{0, 0}} [L.IsRelational] : Compl (Lax904597.Problems.DecisionProblem L) :=
  ⟨Lax624099.ClassRE.DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax624099Proofs.DescriptiveComplexity.DecisionProblem (compl_compl)

end Lax904597.Problems.DecisionProblem

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **Reductions complement**: the very same interpretation reduces `Pᶜ` to
`Qᶜ`, since the correctness of a reduction is an equivalence. This is what
turns a hardness discharge for a `Σ`-level into one for the dual `Π`-level;
see `Lax624099Proofs.DescriptiveComplexity.taut_hard_of_piSODefinable`. -/
def FOReduction.compl {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'} (f : P ≤ᶠᵒ Q) : Pᶜ ≤ᶠᵒ Qᶜ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => not_congr (f.correct A) }

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax624099Proofs.DescriptiveComplexity.FOReduction (compl)

end Lax904597.Interpretations.FOReduction

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

@[inherit_doc FOReduction.compl]
def OrderedFOReduction.compl {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'} (f : P ≤ᶠᵒ[≤] Q) : Pᶜ ≤ᶠᵒ[≤] Qᶜ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => not_congr (f.correct A) }

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.OrderedFOReduction

export Lax624099Proofs.DescriptiveComplexity.OrderedFOReduction (compl)

end Lax904597.Interpretations.OrderedFOReduction

namespace Lax624099Proofs.DescriptiveComplexity

open FirstOrder

open Language

end Lax624099Proofs.DescriptiveComplexity


