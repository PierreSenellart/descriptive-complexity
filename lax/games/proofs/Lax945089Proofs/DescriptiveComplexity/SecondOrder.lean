/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Lax945089Proofs.DescriptiveComplexity.Complexity
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax945089Proofs.DescriptiveComplexity.SOAtom
end Lax945089Proofs.DescriptiveComplexity.SOAtom

namespace Lax945089Proofs.DescriptiveComplexity.SOBlock
end Lax945089Proofs.DescriptiveComplexity.SOBlock

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (PiSODefinable SOBlock SORealize SigmaSODefinable instIsRelationalLang soLang)
end Lax945089Proofs.DescriptiveComplexity

namespace Lax945089Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax945089Proofs.DescriptiveComplexity

/-!
# Second-order definability with bounded alternation

Foundation for *defining* the levels `Σₖ`/`Πₖ` (`k ≥ 1`) of the polynomial
hierarchy logically, by Fagin's ([Fagin 1974][fagin1974generalized]) and
Stockmeyer's ([Stockmeyer 1976][stockmeyer1976polynomial]) theorems: `Σₖᵖ`
consists of
the problems definable by a second-order sentence with `k` alternating blocks
of second-order quantifiers starting existentially – on unordered finite
structures (the first existential block can guess a linear order, so the
order-free definition is equivalent to the classical ordered one).

No object-level second-order syntax is needed: a second-order quantifier
block (`DescriptiveComplexity.SOBlock`) is a finite family of relation variables with
given arities, its instantiations are Lean-level (`SOBlock.structure` turns
an assignment of relations into a structure over the block's vocabulary
`SOBlock.lang`), and only the first-order kernel is object-level – a sentence
over the base language expanded by all blocks (`DescriptiveComplexity.soLang`).
`DescriptiveComplexity.SORealize` evaluates the alternating quantification, and
`DescriptiveComplexity.SigmaSODefinable` / `DescriptiveComplexity.PiSODefinable` state that a
decision problem is defined by such a sentence *on nonempty finite
structures*.

This file proves the two structural facts about these notions that do not
involve reductions:

* isomorphism-invariance (`DescriptiveComplexity.sorealize_iso`) – so second-order
  definable properties are bona fide decision problems;
* the duality `Πₖ = co-Σₖ` (`DescriptiveComplexity.piSODefinable_iff_compl`), by
  negating the kernel and flipping the quantifiers.

The rest of the definitional theory lives in dedicated files: functoriality
and padding in `DescriptiveComplexity.SecondOrderLift`, closure under FO reductions in
`DescriptiveComplexity.SecondOrderPull`, closure under ordered FO reductions in
`DescriptiveComplexity.SecondOrderOrdered`, and the resulting definition of the levels
`Σₖᵖ`/`Πₖᵖ` for `k ≥ 1` in `DescriptiveComplexity.Hierarchy`.
-/

namespace Lax945089Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Second-order quantifier blocks -/

attribute [instance] Lax904597.SecondOrder.SOBlock.ιFinite

/-! ### Isomorphism-invariance -/

section Iso

end Iso

/-! ### Duality: `Πₖ` is co-`Σₖ` -/

section Duality

end Duality

/-! ### Atoms in the relation variables of a block

The clausal fragments of existential second-order logic – SO-Horn
(`DescriptiveComplexity.SecondOrderHorn`) and SO-Krom
(`DescriptiveComplexity.SecondOrderKrom`) – represent their first-order kernel as
data: a list of clauses built from *atoms* in the quantified relation
variables, over a shared list of universally quantified first-order variables.
The atom type and its semantics are common to both fragments, so they live
here. -/

section Atoms

end Atoms

end Lax945089Proofs.DescriptiveComplexity


