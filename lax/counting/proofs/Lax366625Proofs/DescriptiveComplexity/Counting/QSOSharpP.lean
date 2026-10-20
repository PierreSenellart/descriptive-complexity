/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Counting.QSOQuantifiers
import Lax366625Proofs.DescriptiveComplexity.Counting.Class
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.SecondOrderCounting
end Lax366625.SecondOrderCounting

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax366625Proofs.DescriptiveComplexity.SQTerm
end Lax366625Proofs.DescriptiveComplexity.SQTerm

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.SecondOrderCounting (SQDefinable SQTerm)
end Lax366625Proofs.DescriptiveComplexity

/-!
# ΣQSO(FO) is the logic of `#P`

`#P` is defined in the library by witness counts
(`DescriptiveComplexity.SharpPDefinable`): the number of assignments of a
block of relation variables satisfying a first-order sentence over the
ordered expansion. [Arenas, Muñoz, Riveros 2020][arenas2020descriptive] read
`#P` as the logic ΣQSO(FO) instead, whose terms add and multiply, sum and
take products over elements, and sum over relations
(`DescriptiveComplexity.SQTerm`). The two readings coincide
(`DescriptiveComplexity.mem_sharpP_iff_sqDefinable`):

* a witness count is the term `ΣX̄. [φ]`;
* every term is a witness count with free variables
  (`DescriptiveComplexity.SQTerm.wcount`), by induction on the term, each
  construction of the logic being a closure property of witness counts
  (`DescriptiveComplexity.Counting.QSOWitness`,
  `DescriptiveComplexity.Counting.QSOQuantifiers`).

So a problem stated as a ΣQSO(FO) term – the permanent as
`ΣS. [S is a permutation] · Πx. (∃y. S(x, y) ∧ M(x, y))`, a probability of a
query as a weighted count – is in `#P` without writing its kernel.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-- **Every ΣQSO(FO) term is a witness count**, with its free variables. -/
theorem SQTerm.wcount : ∀ {M : Language.{0, 0}} {α : Type} (t : Lax366625.SecondOrderCounting.SQTerm M α),
    WCount M α fun A _ v => t.eval A v
  | _, _, .ind φ => WCount.ind φ
  | _, _, .const s => WCount.const s
  | _, _, .add s t => WCount.add (wcount s) (wcount t)
  | _, _, .mul s t => WCount.mul (wcount s) (wcount t)
  | _, _, .sum n t => WCount.sum n (wcount t)
  | _, _, .prod n t => WCount.prod n (wcount t)
  | _, _, .sosum B t => WCount.sosum B (wcount t)

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.SecondOrderCounting.SQTerm

export Lax366625Proofs.DescriptiveComplexity.SQTerm (wcount)

end Lax366625.SecondOrderCounting.SQTerm

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **ΣQSO(FO) captures `#P`**: a counting problem is in `#P` iff it is
ΣQSO(FO)-definable. -/
theorem mem_sharpP_iff_sqDefinable (C : Lax366625.CountingProblems.CountingProblem L) : C ∈ SharpP ↔ Lax366625.SecondOrderCounting.SQDefinable C := by
  constructor
  · rintro ⟨B, φ, h⟩
    refine ⟨.sosum B (.ind φ), fun A _ _ _ _ => (h A).trans ?_⟩
    classical
    have := Fintype.ofFinite (B.Assignment A)
    rw [Lax366625.SecondOrderCounting.SQTerm.value, Lax366625.SecondOrderCounting.SQTerm.eval, finsum_eq_sum_of_fintype, Lax366625.WitnessCounting.witnessCount]
    simp only [Lax366625.SecondOrderCounting.SQTerm.eval]
    rw [Finset.sum_boole, Nat.cast_id, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  · rintro ⟨t, h⟩
    obtain ⟨B, φ, hφ⟩ := t.wcount
    exact ⟨B, φ, fun A _ _ _ _ => (h A).trans (hφ A default)⟩

end Lax366625Proofs.DescriptiveComplexity


