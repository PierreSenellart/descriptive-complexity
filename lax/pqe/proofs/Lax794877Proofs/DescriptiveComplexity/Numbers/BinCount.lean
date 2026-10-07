/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Numbers.BinRel
import Mathlib.SetTheory.Cardinal.Finite
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

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Counting the binary numbers below a bound

A number written in binary on the positions of a linear order is a set of
positions (`DescriptiveComplexity.binNum`). This file counts those sets: over
`n` positions the decoding is a bijection onto the numbers below `2 ^ n`
(`DescriptiveComplexity.binCode_bijective`), so the sets of bits whose value is
below that of a given set `w` are exactly as many as the value of `w`
(`DescriptiveComplexity.card_binNum_lt`).

That is what lets a number in the instance act as a *weight* in a count: a
witness that carries, beside a solution, a number below the weight of that
solution is counted once per unit of weight, and “below” is first-order
(`DescriptiveComplexity.binNum_lt_iff`).
-/

namespace Lax794877Proofs.DescriptiveComplexity

variable {A : Type} [Finite A] {Le : A → A → Prop}

/-- The decoding of a set of bits, over all the elements as positions, as a
number below `2 ^ n`. -/
noncomputable def binCode (hlin : Lax904597.Machines.IsLinOrd Le) (b : A → Prop) : Fin (2 ^ Nat.card A) :=
  ⟨Lax799700.Common.binNum Le (fun _ => True) b,
    binNum_lt_two_pow hlin (Nat.card A) (fun _ => True)
      (by
        rw [← Nat.card_coe_set_eq]
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial))
      b⟩

/-- **Binary decoding is a bijection** from the sets of positions onto the
numbers below `2 ^ n`. -/
theorem binCode_bijective (hlin : Lax904597.Machines.IsLinOrd Le) : Function.Bijective (binCode (A := A) hlin) := by
  classical
  let := Fintype.ofFinite (A → Prop)
  have hcard : ({p : A | True} : Set A).ncard = Nat.card A := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun b b' h => ?_, ?_⟩
  · exact funext fun p => propext
      (binNum_inj_on hlin (Nat.card A) (fun _ => True) hcard b b' (congrArg Fin.val h) p trivial)
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card,
      Fintype.card_prop]

/-- **The sets of bits below a weight are as many as the weight.** -/
theorem card_binNum_lt (hlin : Lax904597.Machines.IsLinOrd Le) (w : A → Prop) :
    Nat.card {b : A → Prop // Lax799700.Common.binNum Le (fun _ => True) b < Lax799700.Common.binNum Le (fun _ => True) w} =
      Lax799700.Common.binNum Le (fun _ => True) w := by
  have hw := (binCode hlin w).2
  have e1 : {b : A → Prop // Lax799700.Common.binNum Le (fun _ => True) b < Lax799700.Common.binNum Le (fun _ => True) w} ≃
      {k : Fin (2 ^ Nat.card A) // k.1 < Lax799700.Common.binNum Le (fun _ => True) w} :=
    Equiv.subtypeEquiv (Equiv.ofBijective _ (binCode_bijective hlin)) fun _ => Iff.rfl
  have e2 : {k : Fin (2 ^ Nat.card A) // k.1 < Lax799700.Common.binNum Le (fun _ => True) w} ≃
      Fin (Lax799700.Common.binNum Le (fun _ => True) w) :=
    { toFun := fun k => ⟨k.1.1, k.2⟩
      invFun := fun i => ⟨⟨i.1, lt_trans i.2 hw⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card, Fintype.card_fin]

end Lax794877Proofs.DescriptiveComplexity


