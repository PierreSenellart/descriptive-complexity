/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax420092Proofs.DescriptiveComplexity.SecondOrderLift
import Lax420092Proofs.DescriptiveComplexity.SecondOrderPull
import Lax420092Proofs.DescriptiveComplexity.SecondOrderOrdered
import Lax420092Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax420092Proofs.DescriptiveComplexity.RelComposition
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

namespace Lax420092Proofs.DescriptiveComplexity.CofinalHard
end Lax420092Proofs.DescriptiveComplexity.CofinalHard

namespace Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction
end Lax420092Proofs.DescriptiveComplexity.OrderedFOReduction

/-!
# The polynomial hierarchy, defined by second-order alternation

The levels `Σₖᵖ`/`Πₖᵖ` of the polynomial hierarchy for `k ≥ 1` – in
particular `NP = Σ₁ᵖ` and `coNP = Π₁ᵖ` – are *defined* here as
`ComplexityClass`es, via Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: membership is
second-order definability with `k` alternating quantifier blocks
(`Lax420092Proofs.DescriptiveComplexity.SigmaSODefinable` / `Lax420092Proofs.DescriptiveComplexity.PiSODefinable`), and the closure
of membership under (ordered) FO reductions is provided by the pullback
theorems of `Lax420092Proofs.DescriptiveComplexity.SecondOrderPull` and
`Lax420092Proofs.DescriptiveComplexity.SecondOrderOrdered`.

Hardness is defined *cofinally*: `P` is hard when every problem of the class
reduces (by an ordered FO reduction) to every relational problem that `P`
itself reduces to. For a problem over a relational vocabulary this is
equivalent to the usual “everything in the class reduces to `P`”
(`Lax420092Proofs.DescriptiveComplexity.cofinalHard_iff`, with per-class specializations
`Lax420092Proofs.DescriptiveComplexity.hard_sigmaP_succ_iff`, `Lax420092Proofs.DescriptiveComplexity.hard_piP_succ_iff` and
`Lax420092Proofs.DescriptiveComplexity.hard_PTIME_iff`), and the formulation makes hardness travel
forward along reductions even through non-relational vocabularies.

Level 0 is `Lax420092Proofs.DescriptiveComplexity.PTIME`, polynomial time, *defined* here as
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
`Lax420092Proofs.DescriptiveComplexity.SecondOrderHornPull`, and `Πₖᵖ` is the complements of `Σₖᵖ` at
*every* level (`Lax420092Proofs.DescriptiveComplexity.mem_piP_iff`) – at level 0 by definition, above
it by the quantifier duality.

All four inclusions of level 0 into level 1 are proved – `PTIME ⊆ NP`,
`PTIME ⊆ coNP` and their complements (`Lax420092Proofs.DescriptiveComplexity.PTIME_subset_NP`,
`Lax420092Proofs.DescriptiveComplexity.PTIME_subset_coNP`, `Lax420092Proofs.DescriptiveComplexity.coPTIME_subset_NP`,
`Lax420092Proofs.DescriptiveComplexity.coPTIME_subset_coNP`); they live downstream with HORN-SAT, since
they go through the Horn discharge and, for the two crossing ones, through the
certificate of Horn *un*satisfiability of
`Lax420092Proofs.DescriptiveComplexity.Problems.HornSat.Unsat`.

That the two zeroth levels *coincide* – `PiP 0 = SigmaP 0`, polynomial time
closed under complement – is proved downstream, as
`Lax420092Proofs.DescriptiveComplexity.piP_zero_eq`: it is Grädel's capture theorem at level 0, and
its route is the logic-to-logic equivalence of SO-Horn with FO(LFP)
(`Lax420092Proofs.DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`, in
`Lax420092Proofs.DescriptiveComplexity.FixedPointHorn`), a full logic being closed under negation by
construction; no machine model is involved.

The level inclusions above 0, the duality `Πₖᵖ = co-Σₖᵖ` and the class `PH` are
all proved (`Lax420092Proofs.DescriptiveComplexity.sigmaP_subset_sigmaP_succ`,
`Lax420092Proofs.DescriptiveComplexity.mem_piP_iff`…).
-/

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### Congruence of definability in the problem -/

/-- `Σₖ`-definability only depends on the finite instances of a problem. -/
theorem sigmaSODefinable_congr {P Q : Lax904597.Problems.DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) (k : ℕ) :
    Lax904597.SecondOrder.SigmaSODefinable k P ↔ Lax904597.SecondOrder.SigmaSODefinable k Q := by
  constructor <;> rintro ⟨Bs, hk, φ, hφ⟩ <;> refine ⟨Bs, hk, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

/-! ### Cofinal hardness -/

theorem CofinalHard.of_foReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], Lax904597.Problems.DecisionProblem L₀ → Prop}
    {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
    {P : Lax904597.Problems.DecisionProblem L₁} {Q : Lax904597.Problems.DecisionProblem L₂}
    (f : P ≤ᶠᵒ Q) (hP : Lax904597.Classes.CofinalHard Mem P) : Lax904597.Classes.CofinalHard Mem Q := by
  intro L' _ S hQS L'' _ R hR
  exact hP S (hQS.map fun g => f.toOrdered.toRel.trans g) R hR

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax420092Proofs.DescriptiveComplexity.CofinalHard (of_foReduction)

end Lax904597.Classes.CofinalHard

namespace Lax420092Proofs.DescriptiveComplexity

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

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax420092Proofs.DescriptiveComplexity.CofinalHard (of_orderedReduction)

end Lax904597.Classes.CofinalHard

namespace Lax420092Proofs.DescriptiveComplexity

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

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax420092Proofs.DescriptiveComplexity.CofinalHard (of_relOrderedReduction)

end Lax904597.Classes.CofinalHard

namespace Lax420092Proofs.DescriptiveComplexity

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

end Lax420092Proofs.DescriptiveComplexity

namespace Lax904597.Classes.CofinalHard

export Lax420092Proofs.DescriptiveComplexity.CofinalHard (congr)

end Lax904597.Classes.CofinalHard

namespace Lax420092Proofs.DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### Classes defined by their members -/

/-- The complexity class with a given membership predicate, hardness being
cofinal hardness for it (`Lax420092Proofs.DescriptiveComplexity.CofinalHard`) – the shape of every
logically-defined class of this library. Only the three *membership*
obligations have to be supplied: the hardness half of the closure requirements
is discharged uniformly, by `Lax420092Proofs.DescriptiveComplexity.CofinalHard.of_foReduction` and
its siblings.

A class whose hardness is not cofinal hardness for its own members is built by
hand instead: `Lax420092Proofs.DescriptiveComplexity.ComplexityClass.empty`, where hardness is
outright trivial, and `Lax420092Proofs.DescriptiveComplexity.PH`, whose hardness is stated level by
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

/-- The class `Σₖ₊₁ᵖ`, defined by second-order definability with `k + 1`
alternating blocks starting existentially. -/
noncomputable def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem (fun P => Lax904597.SecondOrder.SigmaSODefinable (k + 1) P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSODefinable_congr h _)

/-! ### Polynomial time, by the Horn fragment -/

/-- **The class PTIME**: the problems definable in the Horn fragment SO-Horn of
existential second-order logic ([Grädel 1992][gradel1992capturing]), which
captures polynomial time on ordered structures. It is a bona fide
`Lax420092Proofs.DescriptiveComplexity.ComplexityClass` because SO-Horn definability is closed under
(ordered) first-order reductions – the Horn shape survives the pullback, see
`Lax420092Proofs.DescriptiveComplexity.SecondOrderHornPull`.

This is level 0 of the hierarchy below (`Lax420092Proofs.DescriptiveComplexity.SigmaP`,
`Lax420092Proofs.DescriptiveComplexity.PiP`), and it has a complete problem, HORN-SAT
(`Lax420092Proofs.DescriptiveComplexity.HORNSAT_PTIME_complete`). That the class is closed under
complement – `PiP 0 = SigmaP 0` – is `Lax420092Proofs.DescriptiveComplexity.piP_zero_eq`, through the
equivalence with FO(LFP). -/
noncomputable def PTIME : ComplexityClass :=
  .ofMem (fun P => SigmaSOHornDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sigmaSOHornDefinable_congr h)

/-! ### The hierarchy -/

/-- The `Σₖᵖ` levels of the polynomial hierarchy: polynomial time at level 0
(`Lax420092Proofs.DescriptiveComplexity.PTIME`, defined by the Horn fragment SO-Horn), second-order
definability with `k` alternations above. -/
noncomputable def SigmaP : ℕ → ComplexityClass
  | 0 => PTIME
  | k + 1 => sigmaLevel k

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
noncomputable abbrev NP : ComplexityClass := SigmaP 1

/-! ### Hardness over relational vocabularies -/

end Lax420092Proofs.DescriptiveComplexity


