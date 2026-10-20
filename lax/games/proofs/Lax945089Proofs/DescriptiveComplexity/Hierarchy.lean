/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.SecondOrderLift
import Lax945089Proofs.DescriptiveComplexity.SecondOrderPull
import Mathlib.Tactic.FinCases
import Lax945089Proofs.DescriptiveComplexity.OrderedComposition
import Lax945089Proofs.DescriptiveComplexity.Ordered
import Lax945089Proofs.DescriptiveComplexity.SecondOrder
import Lax945089Proofs.DescriptiveComplexity.RelComposition
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089Proofs.DescriptiveComplexity.CofinalHard
end Lax945089Proofs.DescriptiveComplexity.CofinalHard

namespace Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax945089Proofs.DescriptiveComplexity.OrderedFOReduction

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SigmaSODefinable)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Classes (CofinalHard)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax535992.HornFragment (SigmaSOHornDefinable)
end Lax945089Proofs.DescriptiveComplexity

/-!
# The polynomial hierarchy, defined by second-order alternation

The levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy for `k ≥ 1` – in
particular `NP = Σ₁ᵖ` and `coNP = Π₁ᵖ` – are *defined* here as
`ComplexityClass`es, via Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: membership is
second-order definability with `k` alternating quantifier blocks
(`DescriptiveComplexity.SigmaSODefinable` / `DescriptiveComplexity.PiSODefinable`), and the closure
of membership under (ordered) FO reductions is provided by the pullback
theorems of `DescriptiveComplexity.SecondOrderPull` and
`DescriptiveComplexity.SecondOrderOrdered`.

Hardness is defined *cofinally*: `P` is hard when every problem of the class
reduces (by an ordered FO reduction) to every relational problem that `P`
itself reduces to. For a problem over a relational vocabulary this is
equivalent to the usual “everything in the class reduces to `P`”
(`DescriptiveComplexity.cofinalHard_iff`, with per-class specializations
`DescriptiveComplexity.hard_sigmaP_succ_iff`, `DescriptiveComplexity.hard_piP_succ_iff` and
`DescriptiveComplexity.hard_PTIME_iff`), and the formulation makes hardness travel
forward along reductions even through non-relational vocabularies.

Level 0 is `DescriptiveComplexity.PTIME`, polynomial time, *defined* here as
definability in the Horn fragment SO-Horn of existential second-order logic
([Grädel 1992][gradel1992capturing]) – the same move as defining NP by
`Σ₁`-definability, and equally a definition rather than an axiom: the library
declares **no axioms**, every theorem depending on nothing beyond Lean's
standard `propext`, `Classical.choice` and `Quot.sound` (check with
`#print axioms`). The order-free characterization of PTIME is the
Chandra–Harel/Gurevich problem and is not needed here: SO-Horn definability,
like ordered FO reductions, is stated over ordered structures.

**What level 0 does and does not give.** It is a genuine class, closed under
(ordered) FO reductions by the shape-preserving pullback of
`DescriptiveComplexity.SecondOrderHornPull`, and `Πₖᵖ` is the complements of `Σₖᵖ` at
*every* level (`DescriptiveComplexity.mem_piP_iff`) – at level 0 by definition, above
it by the quantifier duality.

All four inclusions of level 0 into level 1 are proved – `PTIME ⊆ NP`,
`PTIME ⊆ coNP` and their complements (`DescriptiveComplexity.PTIME_subset_NP`,
`DescriptiveComplexity.PTIME_subset_coNP`, `DescriptiveComplexity.coPTIME_subset_NP`,
`DescriptiveComplexity.coPTIME_subset_coNP`); they live downstream with HORN-SAT, since
they go through the Horn discharge and, for the two crossing ones, through the
certificate of Horn *un*satisfiability of
`DescriptiveComplexity.Problems.HornSat.Unsat`.

That the two zeroth levels *coincide* – `PiP 0 = SigmaP 0`, polynomial time
closed under complement – is proved downstream, as
`DescriptiveComplexity.piP_zero_eq`: it is Grädel's capture theorem at level 0, and
its route is the logic-to-logic equivalence of SO-Horn with FO(LFP)
(`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`, in
`DescriptiveComplexity.FixedPointHorn`), a full logic being closed under negation by
construction; no machine model is involved.

The level inclusions above 0, the duality `Πₖᵖ = co-Σₖᵖ` and the class `PH` are
all proved (`DescriptiveComplexity.sigmaP_subset_sigmaP_succ`,
`DescriptiveComplexity.mem_piP_iff`…).
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### Congruence of definability in the problem -/

/-! ### Cofinal hardness -/

theorem CofinalHard.of_foReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}
    (f : P ≤ᶠᵒ Q) (hP : Lax904597.Classes.CofinalHard Mem P) : Lax904597.Classes.CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.toOrdered.toRel.trans g) R hR

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax945089Proofs.DescriptiveComplexity.CofinalHard (of_foReduction)

end Lax904597.Classes.CofinalHard

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

theorem CofinalHard.of_orderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}
    (f : P ≤ᶠᵒ[≤] Q) (hP : Lax904597.Classes.CofinalHard Mem P) : Lax904597.Classes.CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.toRel.trans g) R hR

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax945089Proofs.DescriptiveComplexity.CofinalHard (of_orderedReduction)

end Lax904597.Classes.CofinalHard

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

theorem CofinalHard.of_relOrderedReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}
    (f : P ≤ʳᶠᵒ[≤] Q) (hP : Lax904597.Classes.CofinalHard Mem P) : Lax904597.Classes.CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.trans g) R hR

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax945089Proofs.DescriptiveComplexity.CofinalHard (of_relOrderedReduction)

end Lax904597.Classes.CofinalHard

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

theorem CofinalHard.congr
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    {L₁ : Language.{0, 0}} [L₁.IsRelational] {P P' : Lax904597.Problems.DecisionProblem L₁}
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ P' A)
    (hP : Lax904597.Classes.CofinalHard Mem P) : Lax904597.Classes.CofinalHard Mem P' := by
  intro L' _ S hS L'' _ R hR
  exact hP S (hS.map fun g => g.congrSource fun A _ _ => (h A).symm) R hR

end Lax945089Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax945089Proofs.DescriptiveComplexity.CofinalHard (congr)

end Lax904597.Classes.CofinalHard

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### Classes defined by their members -/

/-- The complexity class with a given membership predicate, hardness being
cofinal hardness for it (`DescriptiveComplexity.CofinalHard`) – the shape of every
logically-defined class of this library. Only the three *membership*
obligations have to be supplied: the hardness half of the closure requirements
is discharged uniformly, by `DescriptiveComplexity.CofinalHard.of_foReduction` and
its siblings.

A class whose hardness is not cofinal hardness for its own members is built by
hand instead: `DescriptiveComplexity.ComplexityClass.empty`, where hardness is
outright trivial, and `DescriptiveComplexity.PH`, whose hardness is stated level by
level (an equivalent statement, since membership is the union of the levels,
but not a definitional one). -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop)
    (mem_of_foReduction : ∀ {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}, (P ≤ᶠᵒ Q) → Mem Q → Mem P)
    (mem_of_orderedReduction : ∀ {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P)
    (mem_congr_finite : ∀ {L₁ : Language.{0, 0}} [L₁.IsRelational] {P Q : Lax904597.Problems.DecisionProblem L₁},
      (∀ (A : Type) [L₁.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := Lax904597.Classes.CofinalHard Mem P
  mem_of_foReduction f h := mem_of_foReduction f h
  hard_of_foReduction f hP := CofinalHard.of_foReduction f hP
  mem_of_orderedReduction f h := mem_of_orderedReduction f h
  hard_of_orderedReduction f hP := CofinalHard.of_orderedReduction f hP
  hard_of_relOrderedReduction f hP := CofinalHard.of_relOrderedReduction f hP
  mem_congr_finite h := mem_congr_finite h
  hard_congr_finite h :=
    ⟨fun hP => CofinalHard.congr h hP,
      fun hP' => CofinalHard.congr (fun A _ _ => (h A).symm) hP'⟩

/-! ### The complement of a class -/

/-! ### The levels of the hierarchy -/

/-! ### Polynomial time, by the Horn fragment -/

/-! ### The hierarchy -/

/-! ### Hardness over relational vocabularies -/

end Lax945089Proofs.DescriptiveComplexity


