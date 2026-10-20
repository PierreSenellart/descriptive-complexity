/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
import Lax794877Proofs.DescriptiveComplexity.Counting
import Lax794877Proofs.DescriptiveComplexity.Interpretation
import Lax794877Proofs.DescriptiveComplexity.Vocabulary
import Lax794877Proofs.DescriptiveComplexity.Problems.Cvp.Membership
import Lax794877Proofs.DescriptiveComplexity.Counting.FP
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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

namespace Lax366625.NumberedCircuits
end Lax366625.NumberedCircuits

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax794877Proofs.DescriptiveComplexity.HornClause
end Lax794877Proofs.DescriptiveComplexity.HornClause

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives lfpAssign)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.CircuitValue (GateVal)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (FPDefinable QLFPDef QTerm)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax366625.NumberedCircuits (LowerOut OutBit OutOrder circuitNumber circuitOfNum outRank)
end Lax794877Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.NumberedCircuits (ncBelow ncOut numCircuit)
end FirstOrder.Language

/-!
# The number written by a circuit is in FP

`DescriptiveComplexity.circuitNumber_mem_FP`: a definition in QFO(LFP)
(`DescriptiveComplexity.QLFPDef`) of `DescriptiveComplexity.CircuitNumber`.

* The fixed point is the one of the circuit value problem: the ten gate rules
  `DescriptiveComplexity.Cvp.cvpRules`, read in the larger vocabulary
  (`DescriptiveComplexity.HornClause.onLang`), whose least model is the
  evaluation of the gates (`DescriptiveComplexity.CircNum.lfpAssign_numRules_iff`).
* The output is the quantitative term
  `Σg. [out(g) ∧ T(g)] · Πh. ([out(h) ∧ h ≠ g ∧ below(h, g)] + 1)`
  (`DescriptiveComplexity.CircNum.numOut`): the inner product is two to the
  number of outputs strictly below `g`, a factor being `2` for each of them and
  `1` for every other element. This is the shape of the normal form in the
  proof that QFO(LFP) captures FP
  ([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4), a
  number being written digit by digit.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Rules read in a larger vocabulary -/

section OnLang

end OnLang

/-- **A product of factors `1` and `2`** is two to the number of factors `2`:
the place value of a digit, as a product over the universe. -/
theorem finprod_boole_add_one {A : Type} [Finite A] (P : A → Prop) [DecidablePred P] :
    ∏ᶠ h : A, ((if P h then 1 else 0) + 1) = 2 ^ Nat.card {h : A // P h} := by
  let := Fintype.ofFinite A
  have h2 : ∀ h : A, ((if P h then 1 else 0) + 1 : ℕ) = if P h then 2 else 1 := fun h => by
    split_ifs <;> rfl
  rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

namespace CircNum

/-! ### The fixed point: the gate rules -/

/-! ### The output term -/

section Value

end Value

end CircNum

end Lax794877Proofs.DescriptiveComplexity


