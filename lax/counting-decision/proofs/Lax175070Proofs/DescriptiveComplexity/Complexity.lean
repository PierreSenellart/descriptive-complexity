/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Relativized
import Lax175070.CountDefinability
import Lax175070.SelectedSat
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity.DecisionProblem
end Lax175070Proofs.DescriptiveComplexity.DecisionProblem

namespace Lax175070Proofs.DescriptiveComplexity.FOReduction
end Lax175070Proofs.DescriptiveComplexity.FOReduction

namespace Lax175070Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax175070Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem
export Lax485149.Complement.DecisionProblem (compl)
end Lax904597.Problems.DecisionProblem

/-!
# Abstract complexity classes, the polynomial hierarchy, and NP-completeness

Complexity classes are introduced *abstractly*: a `ComplexityClass` assigns to
decision problems (over any relational vocabulary) a membership predicate and a
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
(`DescriptiveComplexity.FOReduction.compl`).

The polynomial hierarchy itself – `DescriptiveComplexity.SigmaP`/`DescriptiveComplexity.PiP`, with
levels `k ≥ 1` *defined* by second-order quantifier alternation and level 0
polynomial time – lives in `DescriptiveComplexity.Hierarchy`; the Cook–Levin
theorem ([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]) lives
with the problem SAT in `DescriptiveComplexity.Problems.Sat`, and
completeness theorems for other problems in their files under
`DescriptiveComplexity/Problems/` (e.g., `DescriptiveComplexity.threeCol_NP_complete` in
`DescriptiveComplexity.Problems.ThreeColorability`).
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- An abstract complexity class: a collection of decision problems (its
`Mem`bership predicate) together with a `Hard`ness predicate, closed under
(ordered) first-order reductions. Both predicates are left completely
abstract; the closure requirements are sound for every class containing
LOGSPACE, since (ordered) FO reductions are computable in AC⁰.

Hardness is a field of its own rather than a function of `Mem`. The classes of
this library take it to be cofinal hardness for their own members – equivalent
to “every member reduces to `P`” (`DescriptiveComplexity.cofinalHard_iff`) – and
are built by `DescriptiveComplexity.ComplexityClass.ofMem`, which supplies both
that reading of `Hard` and the three closure proofs it needs; keeping the field
abstract leaves room for the two that read hardness differently
(`DescriptiveComplexity.ComplexityClass.empty`, `DescriptiveComplexity.PH`). -/
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

end ComplexityClass

instance {L : Language.{0, 0}} [L.IsRelational] : Compl (Lax904597.Problems.DecisionProblem L) :=
  ⟨Lax485149.Complement.DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : Lax904597.Problems.DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax175070Proofs.DescriptiveComplexity.DecisionProblem (compl_compl)

end Lax904597.Problems.DecisionProblem

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-- **Reductions complement**: the very same interpretation reduces `Pᶜ` to
`Qᶜ`, since the correctness of a reduction is an equivalence. This is what
turns a hardness discharge for a `Σ`-level into one for the dual `Π`-level;
see `DescriptiveComplexity.taut_hard_of_piSODefinable`. -/
def FOReduction.compl {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L} {Q : Lax904597.Problems.DecisionProblem L'} (f : P ≤ᶠᵒ Q) : Pᶜ ≤ᶠᵒ Qᶜ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => not_congr (f.correct A) }

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOReduction

export Lax175070Proofs.DescriptiveComplexity.FOReduction (compl)

end Lax904597.Interpretations.FOReduction

namespace Lax175070Proofs.DescriptiveComplexity

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

end Lax175070Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.OrderedFOReduction

export Lax175070Proofs.DescriptiveComplexity.OrderedFOReduction (compl)

end Lax904597.Interpretations.OrderedFOReduction

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language

end Lax175070Proofs.DescriptiveComplexity


