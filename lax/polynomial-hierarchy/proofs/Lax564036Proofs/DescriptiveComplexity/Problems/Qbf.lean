/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf.Defs
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf.Membership
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf.Transfer
import Lax564036Proofs.DescriptiveComplexity.Problems.Qbf.Hardness
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

/-!
# QBF: quantified Boolean formulas with bounded alternation

Umbrella file for the problems `DescriptiveComplexity.QBF k` – quantified Boolean
formulas with `k` alternating blocks of propositional quantifiers – the
canonical complete problems for the levels of the polynomial hierarchy
([Stockmeyer 1976][stockmeyer1976polynomial]; [Wrathall
1976][wrathall1976complete]).

* `DescriptiveComplexity.Problems.Qbf.Defs`: the vocabulary
  `FirstOrder.Language.qbf k` (that of SAT, plus `k` unary block marks), the
  alternating semantics `DescriptiveComplexity.altQuant`, the two shapes of matrix
  (`DescriptiveComplexity.CnfSat`, `DescriptiveComplexity.DnfSat`) and their propositional
  duality, and the bundled problems `DescriptiveComplexity.QBF` /
  `DescriptiveComplexity.QBFPi`.
* `DescriptiveComplexity.Problems.Qbf.Membership`: the membership half,
  `DescriptiveComplexity.qbfProblem_sigmaSODefinable` and
  `DescriptiveComplexity.qbfProblem_piSODefinable`.
* `DescriptiveComplexity.Problems.Qbf.Transfer`: the block-by-block transfer between
  alternation over truth assignments and alternation over second-order block
  assignments.
* `DescriptiveComplexity.Problems.Qbf.Hardness`: the Tseitin interpretation with block
  marks, and its correctness at a fixed truth assignment.

## The parity of `k`

The matrix of `DescriptiveComplexity.QBF k` is conjunctive for odd `k` and disjunctive
for even `k`. This is forced, and is the standard form of the `Σₖᵖ`-complete
quantified Boolean formula problems. The hardness proof encodes the
first-order kernel of a second-order definition by the Tseitin translation
([Tseitin 1968][tseitin1968complexity]) of
`DescriptiveComplexity.Problems.Sat.Tseitin`, which introduces auxiliary *gate*
variables. Those are functionally determined by the block variables, so
`∃ gates, CNF(atoms, gates) ↔ φ(atoms)`, and the gate quantifier can be
absorbed into the innermost quantifier of the prefix **only when that
quantifier is existential** – otherwise the universal player falsifies a gate
clause and the instance collapses. For a prefix starting existentially the
innermost quantifier is existential exactly when `k` is odd; at even `k` one
uses the dual, disjunctive matrix, for which
`DescriptiveComplexity.dnfSat_iff_not_cnfSatWith_true` turns the innermost universal
quantifier back into an existential one over the gates.

Both halves are complete, for both families: `DescriptiveComplexity.QBF_complete` states
that `QBF (k + 1)` is `Σₖ₊₁ᵖ`-complete and `DescriptiveComplexity.QBFPi_complete` that
`QBFPi (k + 1)` is `Πₖ₊₁ᵖ`-complete, for every `k`. The two use the *same*
reduction, `DescriptiveComplexity.qbfReduction`, which is parameterized by the starting
polarity; only the parity of the matrix flips with it. At `k = 0` they
specialize to NP- and coNP-completeness
(`DescriptiveComplexity.QBF_one_NP_complete`, `DescriptiveComplexity.QBFPi_one_coNP_complete`).
Like the rest of the library the development is axiom-free: `#print axioms`
reports only `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Lax564036Proofs.DescriptiveComplexity

/-- **QBF with `k + 1` blocks is in `Σₖ₊₁ᵖ`**: the `k + 1` truth assignments
are guessed as monadic second-order relations, and the matrix is evaluated by
a first-order kernel. -/
theorem qbf_mem_sigmaP (k : ℕ) : QBF (k + 1) ∈ SigmaP (k + 1) :=
  qbfProblem_sigmaSODefinable (k + 1) _

/-- **QBF with a universal outermost block and `k + 1` blocks is in
`Πₖ₊₁ᵖ`.** -/
theorem qbfPi_mem_piP (k : ℕ) : QBFPi (k + 1) ∈ PiP (k + 1) :=
  qbfProblem_piSODefinable (k + 1) _

/-- **QBF with `k + 1` alternating blocks is `Σₖ₊₁ᵖ`-complete.** Membership is
`DescriptiveComplexity.qbf_mem_sigmaP` – guess the `k + 1` truth assignments as monadic
second-order relations and evaluate the matrix first-order. Hardness is
`DescriptiveComplexity.qbf_hard_of_sigmaSODefinable`, the marked Tseitin discharge. -/
theorem QBF_complete (k : ℕ) : (SigmaP (k + 1)).Complete (QBF (k + 1)) :=
  ⟨qbf_mem_sigmaP k,
    (hard_sigmaP_succ_iff k (QBF (k + 1))).mpr fun Q hQ =>
      (qbf_hard_of_sigmaSODefinable k Q hQ).map OrderedFOReduction.toRel⟩

/-- QBF is `Σₖ₊₁ᵖ`-hard. -/
theorem qbf_hard (k : ℕ) : (SigmaP (k + 1)).Hard (QBF (k + 1)) :=
  (QBF_complete k).hard

/-- **The dual family is `Πₖ₊₁ᵖ`-complete**: `QBFPi (k + 1)`, with a universal
outermost block, is complete for `Πₖ₊₁ᵖ`. Membership is
`DescriptiveComplexity.qbfPi_mem_piP`; hardness is
`DescriptiveComplexity.qbfPi_hard_of_piSODefinable`, the same marked Tseitin discharge at
the other starting polarity. -/
theorem QBFPi_complete (k : ℕ) : (PiP (k + 1)).Complete (QBFPi (k + 1)) :=
  ⟨qbfPi_mem_piP k,
    (hard_piP_succ_iff k (QBFPi (k + 1))).mpr fun Q hQ =>
      (qbfPi_hard_of_piSODefinable k Q hQ).map OrderedFOReduction.toRel⟩

/-- `QBFPi` is `Πₖ₊₁ᵖ`-hard. -/
theorem qbfPi_hard (k : ℕ) : (PiP (k + 1)).Hard (QBFPi (k + 1)) :=
  (QBFPi_complete k).hard

/-- QBF with one universal block is coNP-complete. -/
theorem QBFPi_one_coNP_complete : coNP.Complete (QBFPi 1) :=
  QBFPi_complete 0

/-- QBF with one block and a conjunctive matrix is NP-complete – it is
essentially SAT with all variables marked. -/
theorem QBF_one_NP_complete : NP.Complete (QBF 1) :=
  QBF_complete 0

end Lax564036Proofs.DescriptiveComplexity


