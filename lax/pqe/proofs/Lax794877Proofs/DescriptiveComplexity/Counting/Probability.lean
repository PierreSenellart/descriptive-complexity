/-
Copyright (c) 2025 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
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

namespace Lax794877.WeightedWorlds
end Lax794877.WeightedWorlds

namespace Lax794877Proofs.DescriptiveComplexity.ProbAssignment
end Lax794877Proofs.DescriptiveComplexity.ProbAssignment

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.WeightedWorlds (ProbAssignment)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Independent Boolean variables: probabilities, and weighted counts

The concrete side of probabilistic query evaluation, with no logic in it: a
finite set `X` of independent Boolean variables – the uncertain facts of a
tuple-independent database – each true with its own rational probability.

The first part is taken from the library
[provenance-lean](https://github.com/PierreSenellart/provenance-lean)
(`Provenance.Probability`), where it underlies the probabilistic semantics of
ProvSQL: `DescriptiveComplexity.ProbAssignment`, the probability
`DescriptiveComplexity.ProbAssignment.valProb` of a valuation (a possible
world), the fact that these form a distribution
(`DescriptiveComplexity.ProbAssignment.sum_valProb_eq_one`), and the
probability `DescriptiveComplexity.ProbAssignment.funcProb` of an event.

The second part is what the counting side needs. A probability `a / (a + c)`
is a pair of natural **weights**, `a` for “true” and `c` for “false”
(`DescriptiveComplexity.ProbAssignment.ofWeights`). The **weighted count** of
an event (`DescriptiveComplexity.weightedCount`) is the sum, over the
valuations in it, of the product of the weights each variable takes. Then

`Pr(f) = weightedCount f / weightedCount ⊤`

(`DescriptiveComplexity.ProbAssignment.funcProb_ofWeights`): a probability is
a ratio of two weighted counts, and those are natural numbers.
-/

namespace Lax794877Proofs.DescriptiveComplexity

variable {X : Type} [Fintype X] [DecidableEq X]

namespace ProbAssignment

variable (P : Lax794877.WeightedWorlds.ProbAssignment X)

end ProbAssignment

/-! ### Weights -/

section Weights

variable (a c : X → ℕ)

/-- The weight of a valuation: the product, over the variables, of the weight
`a` of those it makes true and the weight `c` of those it makes false. -/
def valWeight (v : X → Bool) : ℕ :=
  ∏ x, if v x then a x else c x

/-- The **weighted count** of an event: the sum of the weights of the
valuations in it. -/
def weightedCount (f : (X → Bool) → Bool) : ℕ :=
  ∑ v : X → Bool, if f v then valWeight a c v else 0

/-- The weighted count of the sure event is the product of the total weights
of the variables. -/
theorem weightedCount_true :
    weightedCount a c (fun _ => true) = ∏ x, (a x + c x) := by
  have hps : (∏ x : X, ∑ b : Bool, (if b then a x else c x)) =
      ∑ v : X → Bool, ∏ x : X, (if v x then a x else c x) :=
    Fintype.prod_sum fun (x : X) (b : Bool) => if b then a x else c x
  simp only [weightedCount, valWeight, ite_true]
  rw [← hps]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp

variable {a c} (h : ∀ x, 0 < a x + c x)

omit [DecidableEq X] in
/-- The probability of a valuation is its weight, over the product of the
total weights. -/
theorem ProbAssignment.valProb_ofWeights (v : X → Bool) :
    (Lax794877.WeightedWorlds.ProbAssignment.ofWeights a c h).valProb v =
      (valWeight a c v : ℚ) / ((∏ x, (a x + c x) : ℕ) : ℚ) := by
  simp only [Lax794877.WeightedWorlds.ProbAssignment.valProb, valWeight, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hpos : (0 : ℚ) < (a x : ℚ) + c x := by exact_mod_cast h x
  by_cases hv : v x
  · simp [hv, Lax794877.WeightedWorlds.ProbAssignment.ofWeights]
  · simp only [hv, Bool.false_eq_true, ite_false, Lax794877.WeightedWorlds.ProbAssignment.ofWeights, Nat.cast_add]
    field_simp
    ring

end Weights

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.WeightedWorlds.ProbAssignment

export Lax794877Proofs.DescriptiveComplexity.ProbAssignment (valProb_ofWeights)

end Lax794877.WeightedWorlds.ProbAssignment

namespace Lax794877Proofs.DescriptiveComplexity

variable {X : Type} [Fintype X] [DecidableEq X]

section Weights

variable (a c : X → ℕ)

variable {a c} (h : ∀ x, 0 < a x + c x)

/-- **A probability is a ratio of two weighted counts**: the probability of an
event is its weighted count, divided by the weighted count of the sure
event. -/
theorem ProbAssignment.funcProb_ofWeights (f : (X → Bool) → Bool) :
    (Lax794877.WeightedWorlds.ProbAssignment.ofWeights a c h).funcProb f =
      (weightedCount a c f : ℚ) / (weightedCount a c fun _ => true) := by
  rw [weightedCount_true]
  simp only [Lax794877.WeightedWorlds.ProbAssignment.funcProb, weightedCount, Nat.cast_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hf : f v
  · simp only [hf, ite_true]
    exact ProbAssignment.valProb_ofWeights h v
  · simp [hf]

end Weights

end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877.WeightedWorlds.ProbAssignment

export Lax794877Proofs.DescriptiveComplexity.ProbAssignment (funcProb_ofWeights)

end Lax794877.WeightedWorlds.ProbAssignment

namespace Lax794877Proofs.DescriptiveComplexity

variable {X : Type} [Fintype X] [DecidableEq X]

section Weights

variable (a c : X → ℕ)

variable {a c} (h : ∀ x, 0 < a x + c x)

end Weights

end Lax794877Proofs.DescriptiveComplexity


