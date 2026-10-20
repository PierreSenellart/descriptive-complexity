/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.MachinesAlt
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Defs
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

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax564036.AlternatingMachines (ATMAcc ATMBlank ATMBlk ATMData ATMDst ATMInp ATMLe ATMPosn ATMRead ATMRight ATMSrc ATMStart ATMTr ATMWrite atmData)
end Lax480241Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Machines (turingRel)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax564036.AlternatingMachines (atmAcc atmBlank atmBlk atmDst atmInp atmLe atmPosn atmRead atmRight atmSrc atmStart atmTr atmWrite instIsRelationalTuringAlt turingAlt turingAltRel)
end FirstOrder.Language

/-!
# Alternating machine acceptance as a decision problem

The vocabulary of the machine bridge for the polynomial hierarchy, and the
problem the bridge is about: an alternating Turing machine with `k` quantifier
blocks is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.ATMAccept k start`, an ordinary iso-invariant problem
of the catalog. The semantics it reads is
`DescriptiveComplexity.ATMData`, defined without a vocabulary in
`DescriptiveComplexity.MachinesAlt`.

## The vocabulary

`FirstOrder.Language.turingAlt k` is `FirstOrder.Language.turing` – every
symbol of which it carries verbatim, under the constructor `base` – together
with `k` unary marks `blk i` splitting the states into quantifier blocks,
exactly as `FirstOrder.Language.qbf k` extends the vocabulary of SAT by `k`
marks on the propositional variables. The two families of marks meet in the
hardness proof, which turns the block of a variable into the block of the state
guessing it.

Making the marks a *family* indexed by `Fin k`, rather than a fixed pair of
marks “existential”/“universal”, is what lets the alternation *bound* be
first-order: a transition may not decrease the block index, and may raise it by
at most one, so a run passes through the blocks in order and alternates at most
`k - 1` times. That promise – `DescriptiveComplexity.ATMData.BlocksWellFormed` –
is folded into the yes-instances alongside
`DescriptiveComplexity.TMData.WellFormed`, in the style of
`DescriptiveComplexity.IsLinOrd` for Knapsack.

## The two families

`ATMAccept k true` starts with an existential block and is the `Σₖᵖ` candidate;
`ATMAccept k false` starts with a universal one and is the `Πₖᵖ` candidate. The
two are the *same* problem up to the polarity parameter, so the `Πₖᵖ` half of
the bridge costs nothing beyond swapping the marks – the machine-side reading
of `DescriptiveComplexity.QBF` and `DescriptiveComplexity.QBFPi` sharing a
single reduction.
-/

namespace FirstOrder

namespace Language

variable {k : ℕ}

end Language

end FirstOrder

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {k : ℕ} {A : Type} [(Lax564036.AlternatingMachines.turingAlt k).Structure A]

end Shorthands

/-! ### The problem -/

section Problem

variable {k : ℕ} {A B : Type}
  [(Lax564036.AlternatingMachines.turingAlt k).Structure A] [(Lax564036.AlternatingMachines.turingAlt k).Structure B]

/-- **An isomorphism makes the two machines agree.** Every symbol of the
vocabulary transports, which is all `DescriptiveComplexity.ATMData.AltAgree`
asks for. -/
theorem altAgree_of_equiv (e : A ≃[Lax564036.AlternatingMachines.turingAlt k] B) :
    (Lax564036.AlternatingMachines.atmData k B).AltAgree e.symm.toEquiv (Lax564036.AlternatingMachines.atmData k A) := by
  have h1 : ∀ (r : (Lax564036.AlternatingMachines.turingAlt k).Relations 1) (b : B),
      (RelMap r ![b] : Prop) ↔ RelMap r ![(e.symm b : A)] := fun r b => by
    have h := relMap_equiv₁ e r (e.symm b)
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h
    exact h.symm
  have h2 : ∀ (r : (Lax564036.AlternatingMachines.turingAlt k).Relations 2) (b b' : B),
      (RelMap r ![b, b'] : Prop) ↔ RelMap r ![(e.symm b : A), (e.symm b' : A)] := fun r b b' => by
    have h := relMap_equiv₂ e r (e.symm b) (e.symm b')
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b,
      show (e (e.symm b') : B) = b' from e.toEquiv.apply_symm_apply b'] at h
    exact h.symm
  exact ⟨⟨fun b => h1 Lax564036.AlternatingMachines.atmPosn b, fun b b' => h2 Lax564036.AlternatingMachines.atmLe b b', fun b => h1 Lax564036.AlternatingMachines.atmTr b,
      fun b => h1 Lax564036.AlternatingMachines.atmStart b, fun b => h1 Lax564036.AlternatingMachines.atmAcc b, fun b => h1 Lax564036.AlternatingMachines.atmBlank b,
      fun b => h1 Lax564036.AlternatingMachines.atmRight b, fun b b' => h2 Lax564036.AlternatingMachines.atmSrc b b', fun b b' => h2 Lax564036.AlternatingMachines.atmRead b b',
      fun b b' => h2 Lax564036.AlternatingMachines.atmDst b b', fun b b' => h2 Lax564036.AlternatingMachines.atmWrite b b', fun b b' => h2 Lax564036.AlternatingMachines.atmInp b b'⟩,
    fun j b => exists_congr fun h => h1 (Lax564036.AlternatingMachines.atmBlk ⟨j, h⟩) b⟩

end Problem

/-! ### Reading the block marks

The marks of the vocabulary are indexed by `Fin k`, so
`DescriptiveComplexity.ATMBlk` is `False` beyond `k` by construction; the two
lemmas below are the only unfolding the rest of the development needs. -/

section Marks

end Marks

/-! ### The one-block instances

At `k = 1` the vocabulary has a single mark, the only block is `0` and its
polarity is that of `start`; so for `start = true` no state is universal, and
the alternating model is the nondeterministic one
(`DescriptiveComplexity.ATMData.altAccepts_true_iff_accepts`). -/

section OneBlock

end OneBlock

end Lax480241Proofs.DescriptiveComplexity


