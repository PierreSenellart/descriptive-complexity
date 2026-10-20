/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Machines
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

namespace Lax480241Proofs.DescriptiveComplexity.ATMData
end Lax480241Proofs.DescriptiveComplexity.ATMData

namespace Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree
end Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config TMData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMData blockPol guardQ)
end Lax480241Proofs.DescriptiveComplexity

/-!
# Alternating Turing machines over a universe, without a vocabulary

The semantics half of the machine bridge for the polynomial hierarchy: what it
means for an *alternating* Turing machine, presented as relations on a
universe, to accept. As in `DescriptiveComplexity.Machines` no vocabulary
appears, so the reductions – which build machines rather than read them – can
reason about acceptance without unfolding any `RelMap`.

## The model

`DescriptiveComplexity.ATMData` is `DescriptiveComplexity.TMData` together with
one further family of marks, `Blk j q`: the state `q` belongs to the `j`-th
quantifier block. Two conventions fix the game the marks describe.

* **Which player owns a state.** Block `j` is existential when
  `DescriptiveComplexity.blockPol start j` is `true`, that is, when `j` is even
  and `start` is `true` or `j` is odd and `start` is `false`: the polarities
  alternate outwards-in from `start`, exactly as
  `DescriptiveComplexity.altQuant` alternates the quantifiers of a quantified
  Boolean formula. A state marked by a block of the other polarity is
  *universal* (`DescriptiveComplexity.ATMData.IsUniv`).
* **Blocks mark states, not times.** A variant marking the *time* – the phases
  of the run scheduled in advance – makes the round structure independent of
  the run, and is rejected for exactly that: it clocks the alternation, which
  is half of what the model is supposed to say.
* **A stuck universal state rejects.** A universal configuration accepts when
  every successor accepts *and there is one*
  (`DescriptiveComplexity.ATMData.AltAcc`). The other convention – vacuous
  universal quantification, so that a stuck universal configuration accepts –
  is equally standard, and this one is chosen because it makes “the machine
  stops without accepting” mean *reject* in every block, which is what a
  reduction needs: a checking phase that fails may then simply run out of
  transitions, whatever the polarity of the block it runs in.

With one block the model is the nondeterministic one: `AltAcc start n c`
unfolds to “some run of at most `n` steps from `c` reaches an accepting
state”, so `DescriptiveComplexity.ATMData.AltAccepts` at `k = 1` is
`DescriptiveComplexity.TMData.Accepts`.

## The alternation bound

Nothing above bounds the number of alternations; the bound is
`DescriptiveComplexity.ATMData.BlocksWellFormed`, folded into the yes-instances
of the decision problem exactly as linearity of the order is: every state
carries exactly one of the `k` marks, a transition raises the block index by
`0` or `1`, and a start state is in block `0`. All three are first-order for a
fixed `k` – the second because it is a condition on a single transition, which
is what makes “at most `k - 1` alternations” checkable by the kernel of a `Σₖ`
definition rather than by an inspection of runs. The last two together make a
run pass through the blocks in succession, starting at the first, which is what
lets it be read as `k` rounds of a game with the right player in each.

## Transport

`DescriptiveComplexity.ATMData.AltAgree` records that two alternating machines
over different universes correspond along an equivalence, and the lemmas below
transport acceptance along it – all the isomorphism-invariance proof of the
decision problem needs.
-/

namespace Lax480241Proofs.DescriptiveComplexity

@[simp]
theorem blockPol_zero (start : Bool) : Lax564036.AlternatingMachines.blockPol start 0 = start := rfl

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

/-! ### The players -/

/-! ### Alternating acceptance -/

/-! ### Elementary properties -/

section Basic

end Basic

/-! ### Transport along an equivalence of universes -/

section Transport

variable {B : Type} {M}

/-- Two alternating machines over different universes **agree** along an
equivalence when their underlying machines do and their block marks
correspond. -/
structure AltAgree (u : B ≃ A) (N : Lax564036.AlternatingMachines.ATMData B) (M : Lax564036.AlternatingMachines.ATMData A) : Prop where
  /-- The underlying machines agree. -/
  base : TMData.Agree u N.toTMData M.toTMData
  /-- The block marks correspond. -/
  blk : ∀ j b, N.Blk j b ↔ M.Blk j (u b)

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData

export Lax480241Proofs.DescriptiveComplexity.ATMData (AltAgree)

end Lax564036.AlternatingMachines.ATMData

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

section Transport

variable {B : Type} {M}

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.AltAgree

export Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree (base blk)

end Lax564036.AlternatingMachines.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

section Transport

variable {B : Type} {M}

variable {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

/-- Universality of a state transports along an equivalence. -/
theorem AltAgree.isUniv (h : AltAgree u N M) (start : Bool) (b : B) :
    N.IsUniv start b ↔ M.IsUniv start (u b) :=
  exists_congr fun j => and_congr_left' (h.blk j b)

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity

namespace Lax564036.AlternatingMachines.ATMData.AltAgree

export Lax480241Proofs.DescriptiveComplexity.ATMData.AltAgree (isUniv)

end Lax564036.AlternatingMachines.ATMData.AltAgree

namespace Lax480241Proofs.DescriptiveComplexity

namespace ATMData

variable {A : Type} (M : Lax564036.AlternatingMachines.ATMData A)

section Transport

variable {B : Type} {M}

variable {u : B ≃ A} {N : Lax564036.AlternatingMachines.ATMData B}

end Transport

end ATMData

end Lax480241Proofs.DescriptiveComplexity


