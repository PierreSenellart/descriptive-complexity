/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine.Walk
import Lax535992Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax535992Proofs.DescriptiveComplexity.SecondOrder
import Lax535992Proofs.DescriptiveComplexity.Hierarchy
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock SigmaSODefinable)
end Lax535992Proofs.DescriptiveComplexity

namespace Lax535992Proofs.DescriptiveComplexity
export Lax904597.Machines (MinPos SuccPos TMAcc TMBlank TMDst TMInp TMLe TMPosn TMRead TMRight TMSrc TMStart TMTr TMWrite tmData)
end Lax535992Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

/-!
# Machine acceptance is existential second-order definable

The membership half of the machine bridge: `NTMAccept` is `Σ₁`-definable, hence
in NP. This is Fagin's tableau argument, and – unlike the certificate of a
weighted problem – it needs no arithmetic at all: one existential block guesses
the run, and a first-order kernel checks it clause by clause.

## What is guessed

Three relation variables, indexed by the *positions*, which are simultaneously
the tape cells and the time steps:

* `Q t q` – at time `t` the machine is in state `q`;
* `H t p` – at time `t` the head is on the cell `p`;
* `T t p a` – at time `t` the cell `p` holds the symbol `a`.

That the guess is a run is exactly `DescriptiveComplexity.TMData.RelWalk`, and
`DescriptiveComplexity.TMData.exists_relWalk_iff_exists_walk` together with
`DescriptiveComplexity.TMData.accepts_iff_exists_walk` is what connects it back to
acceptance. So this file is a transcription: every clause below mirrors one
field of `RelWalk` or one conjunct of `DescriptiveComplexity.TMData.WellFormed`, and each
has its own realization lemma. Nothing here does mathematics; the mathematics is
in `DescriptiveComplexity.Problems.Machine.Walk`.

## The clauses

Seventeen of them, conjoined into `DescriptiveComplexity.tqKernel`: four saying the
order is linear, four more for the remaining promises of `WellFormed`, six for
the functionality of the guess, then the initial clause, the step clause and
the accepting clause. The step clause is the largest formula in the library –
an existential over a transition element with seven conjuncts, against a
stutter alternative – and is kept manageable by parameterizing its body
(`DescriptiveComplexity.tqStepBodyF`) over the three variables it reads, so that no
`Sum` nesting goes deeper than two levels.

## The order predicates

`MinPos`, `MaxPos` and `SuccPos` are relativized to the positions, so they are
not the ordered-structure guards of `DescriptiveComplexity.OrderWalk` but formulas over
the instance's own `le` and `posn` symbols, defined here as
`DescriptiveComplexity.tqMinPosF` and friends.
-/

namespace Lax535992Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### The block -/

/-- The relation variables of the certificate: the state, the head and the tape
of the configuration at each time. -/
inductive TMIdx : Type
  /-- The state at a time. -/
  | state
  /-- The head cell at a time. -/
  | head
  /-- The tape contents at a time. -/
  | tape
  deriving DecidableEq

instance : Fintype TMIdx where
  elems := {TMIdx.state, TMIdx.head, TMIdx.tape}
  complete := fun i => by cases i <;> decide

/-- The single existential block: the run, guessed as a state, a head position
and a tape contents for each time. -/
def tmGuessBlock : Lax904597.SecondOrder.SOBlock where
  ι := TMIdx
  arity := fun i => match i with
    | .state => 2
    | .head => 2
    | .tape => 3

/-! ### Formula builders -/

section Builders

end Builders

/-! ### Realization of the builders -/

section Realize

variable {A : Type} [Lax904597.Machines.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

/-- The structure the kernel is read in: the instance expanded by the guess. -/
local notation "SOStruc" => @sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

end Realize

/-! ### The clauses of the kernel

Each mirrors one field of `DescriptiveComplexity.TMData.RelWalk`. -/

section Clauses

end Clauses

section RealizeClauses

variable {A : Type} [Lax904597.Machines.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

local notation "SOStruc" => @sumStructure Lax904597.Machines.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

end RealizeClauses

/-! ### The definability theorems -/

end Lax535992Proofs.DescriptiveComplexity


