/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
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

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Sat (SAT Satisfiable)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# TAUT: propositional tautology

The problem TAUT – is a formula in disjunctive normal form a tautology? – the
archetypical coNP-complete problem. Its instances are the structures of the
SAT vocabulary `FirstOrder.Language.sat`, *read disjunctively*: a CNF formula
and a DNF formula are the same data, a set of clauses (here: terms) with the
positive and negative occurrences of the variables in each. The reading is in
`DescriptiveComplexity.Tautology`: every truth assignment satisfies all the literals of
some term.

Both halves of the coNP-completeness come from SAT by the *same* interpretation
`DescriptiveComplexity.swapSignInterp`, which keeps the universe and the terms and
exchanges positive with negative occurrences. It witnesses De Morgan's law: a
DNF is a tautology exactly when the CNF obtained by negating every literal is
unsatisfiable (`DescriptiveComplexity.tautology_iff_not_satisfiable`). Hence

* `DescriptiveComplexity.taut_mem_coNP`: `TAUTᶜ` FO-reduces to SAT, so it is in NP, so
  TAUT is in coNP;
* `DescriptiveComplexity.taut_hard_of_piSODefinable`: a `Π₁`-definable problem has a
  `Σ₁`-definable complement, which reduces to SAT by the Cook–Levin discharge
  `DescriptiveComplexity.sat_hard_of_sigmaSODefinable`; complementing that reduction
  (`DescriptiveComplexity.OrderedFOReduction.compl`) and composing with `SATᶜ ≤ᶠᵒ TAUT`
  discharges coNP-hardness.

No new second-order argument is needed: TAUT is coNP-complete
(`DescriptiveComplexity.TAUT_coNP_complete`) purely by the complement machinery of
`DescriptiveComplexity.Complexity` and the duality
`DescriptiveComplexity.piSODefinable_iff_compl`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-! ### The disjunctive reading -/

section Taut

end Taut

/-! ### De Morgan: tautology is unsatisfiability of the sign swap -/

section DeMorgan

end DeMorgan

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

end Iso

/-! ### The sign-swapping interpretation -/

/-- The sign-swapping interpretation: same universe, same terms, positive and
negative occurrences exchanged. One-dimensional, single-tagged and
quantifier-free. -/
def swapSignInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Sat.sat Lax904597.Sat.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => FirstOrder.Language.Relations.formula₁ Lax904597.Sat.satIsClause (FirstOrder.Language.Term.var (0, 0))
    | _, .posIn => fun _ => FirstOrder.Language.Relations.formula₂ Lax904597.Sat.satNegIn (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0))
    | _, .negIn => fun _ => FirstOrder.Language.Relations.formula₂ Lax904597.Sat.satPosIn (FirstOrder.Language.Term.var (0, 0))
                                (FirstOrder.Language.Term.var (1, 0))

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A]

@[simp]
theorem swapSign_isClause (w : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satIsClause ![((), w)] ↔ RelMap Lax904597.Sat.satIsClause ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₁]

@[simp]
theorem swapSign_posIn (w₁ w₂ : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satPosIn ![((), w₁), ((), w₂)] ↔
      RelMap Lax904597.Sat.satNegIn ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₂]

@[simp]
theorem swapSign_negIn (w₁ w₂ : Fin 1 → A) :
    RelMap (M := swapSignInterp.Map A) Lax904597.Sat.satNegIn ![((), w₁), ((), w₂)] ↔
      RelMap Lax904597.Sat.satPosIn ![w₁ 0, w₂ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [swapSignInterp, Formula.realize_rel₂]

end Characterizations

/-! ### Correctness of the swap, in both directions -/

section Correctness

end Correctness

/-! ### The reductions -/

/-! ### coNP-completeness -/

end Lax859101Proofs.DescriptiveComplexity


