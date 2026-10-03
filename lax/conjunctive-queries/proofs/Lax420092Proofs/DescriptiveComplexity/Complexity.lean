/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax420092Proofs.DescriptiveComplexity.Relativized
import Lax420092.Evaluation
import Lax420092.PackagedInstances
import Lax420092.QueryDatabases
import Lax420092.QueryPairs
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

namespace Lax420092Proofs.DescriptiveComplexity.DecisionProblem
end Lax420092Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity.FOReduction
end Lax420092Proofs.DescriptiveComplexity.FOReduction

namespace Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction

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
(`Lax420092Proofs.DescriptiveComplexity.FOReduction.compl`).

The polynomial hierarchy itself – `Lax420092Proofs.DescriptiveComplexity.SigmaP`/`Lax420092Proofs.DescriptiveComplexity.PiP`, with
levels `k ≥ 1` *defined* by second-order quantifier alternation and level 0
polynomial time – lives in `Lax420092Proofs.DescriptiveComplexity.Hierarchy`; the Cook–Levin
theorem ([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]) lives
with the problem SAT in `Lax420092Proofs.DescriptiveComplexity.Problems.Sat`, and
completeness theorems for other problems in their files under
`Lax420092Proofs.DescriptiveComplexity/Problems/` (e.g., `Lax420092Proofs.DescriptiveComplexity.threeCol_NP_complete` in
`Lax420092Proofs.DescriptiveComplexity.Problems.ThreeColorability`).
-/

namespace Lax420092Proofs.DescriptiveComplexity

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
and are built by `Lax420092Proofs.DescriptiveComplexity.ComplexityClass.ofMem`, which supplies both
that reading of `Hard` and the three closure proofs it needs; keeping the field
abstract leaves room for the two that read hardness differently
(`Lax420092Proofs.DescriptiveComplexity.ComplexityClass.empty`, `Lax420092Proofs.DescriptiveComplexity.PH`). -/
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

end ComplexityClass

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
protected def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L) :
    Lax904597.Problems.DecisionProblem L where
  Holds := fun A inst => ¬@Lax904597.Problems.DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (compl)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language

instance {L : Language.{0, 0}} [L.IsRelational] : Compl (Lax904597.Problems.DecisionProblem L) :=
  ⟨DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax420092Proofs.DescriptiveComplexity.DecisionProblem (compl_compl)

end Lax904597.Problems.DecisionProblem

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language

end Lax420092Proofs.DescriptiveComplexity


