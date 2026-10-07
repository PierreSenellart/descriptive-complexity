/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.MachinesAltSpace
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.AltDefs
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241.AlternatingSpace.ATMData
end Lax480241.AlternatingSpace.ATMData

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (atmData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData
export Lax480241.AlternatingSpace.ATMData (AltAcceptsSpace BlocksSplit)
end Lax564036.AlternatingMachines.ATMData

namespace FirstOrder.Language
export Lax564036.AlternatingMachines (turingAlt)
end FirstOrder.Language

/-!
# Alternating machine acceptance in bounded space, as a decision problem

EXPTIME's complete problem: an alternating Turing machine is *data in an
instance*, and

> does this machine accept its input, with the tape indexed by the positions and
> no bound whatever on the length of a play?

is `DescriptiveComplexity.ATMAcceptSpace`, an ordinary iso-invariant problem of
the catalog. It stands to `DescriptiveComplexity.ATMAccept` exactly as
`DescriptiveComplexity.DTMAcceptSpace` stands to
`DescriptiveComplexity.DTMAccept`: the step bound is dropped and the space stays
bounded by construction.

Two differences from the polynomial-hierarchy problem, both of them
*relaxations*:

* the vocabulary is `FirstOrder.Language.turingAlt 2` – two marks, one per
  player – and the promise folded into the yes-instances is only that they
  **split** the states (`DescriptiveComplexity.ATMData.BlocksSplit`), not
  `DescriptiveComplexity.ATMData.BlocksWellFormed`, whose ordering clause is
  what bounds the number of alternations. Here the alternation is unbounded,
  which is the whole point;
* acceptance is `DescriptiveComplexity.ATMData.AltAcceptsSpace`, the least fixed
  point of the game operator rather than a budgeted recursion.

Isomorphism-invariance is proved from the *two* agreements an isomorphism
supplies – one per direction – so that only the forward transport lemmas of
`DescriptiveComplexity.MachinesAltSpace` are needed and no finiteness is
assumed.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Problem

variable {A B : Type} [(Lax564036.AlternatingMachines.turingAlt 2).Structure A] [(Lax564036.AlternatingMachines.turingAlt 2).Structure B]

/-- The agreement an isomorphism supplies in the other direction. -/
private theorem altAgree_of_equiv' (e : A ≃[Lax564036.AlternatingMachines.turingAlt 2] B) :
    (Lax564036.AlternatingMachines.atmData 2 A).AltAgree e.toEquiv (Lax564036.AlternatingMachines.atmData 2 B) := by
  have h := altAgree_of_equiv (k := 2) e.symm
  exact h

end Problem

/-- **Alternating acceptance in bounded space**: the machine is well formed,
its two marks split the states, and the existential player wins the game on the
configuration graph from some initial configuration. -/
def ATMAcceptSpace : Lax904597.Problems.DecisionProblem (Lax564036.AlternatingMachines.turingAlt 2) where
  Holds := fun A inst => @Lax904597.Machines.TMData.WellFormed A (Lax564036.AlternatingMachines.atmData 2 A).toTMData ∧
    @Lax480241.AlternatingSpace.ATMData.BlocksSplit A (Lax564036.AlternatingMachines.atmData 2 A) ∧
    @Lax480241.AlternatingSpace.ATMData.AltAcceptsSpace A (Lax564036.AlternatingMachines.atmData 2 A) true
  iso_invariant := fun {A B} _ _ e => by
    have h := altAgree_of_equiv (k := 2) e
    have h' := altAgree_of_equiv' e
    constructor
    · rintro ⟨hwf, hsp, hacc⟩
      exact ⟨h'.base.wellFormed.mp hwf, h'.blocksSplit_mp hsp, h'.altAcceptsSpace_mp true hacc⟩
    · rintro ⟨hwf, hsp, hacc⟩
      exact ⟨h.base.wellFormed.mp hwf, h.blocksSplit_mp hsp, h.altAcceptsSpace_mp true hacc⟩

@[simp]
theorem atmAcceptSpace_holds_iff (A : Type) [(Lax564036.AlternatingMachines.turingAlt 2).Structure A] :
    ATMAcceptSpace A ↔ (Lax564036.AlternatingMachines.atmData 2 A).toTMData.WellFormed ∧ (Lax564036.AlternatingMachines.atmData 2 A).BlocksSplit ∧
      (Lax564036.AlternatingMachines.atmData 2 A).AltAcceptsSpace true :=
  Iff.rfl

end Lax480241Proofs.DescriptiveComplexity


