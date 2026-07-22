/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qbf.Defs
import DescriptiveComplexity.Problems.Qbf.Membership
import DescriptiveComplexity.Problems.Qbf.Transfer
import DescriptiveComplexity.Problems.Qbf.Hardness

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

Both halves are complete: `DescriptiveComplexity.QBF_complete` states that `QBF (k + 1)`
is `Σₖ₊₁ᵖ`-complete for every `k`, and at `k = 0` it specializes to a second
proof of NP-completeness of a SAT-like problem
(`DescriptiveComplexity.QBF_one_NP_complete`). Like the rest of the library the
development is axiom-free: `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace DescriptiveComplexity

/-- **QBF with `k + 1` blocks is in `Σₖ₊₁ᵖ`**: the `k + 1` truth assignments
are guessed as monadic second-order relations, and the matrix is evaluated by
a first-order kernel. -/
theorem qbf_mem_sigmaP (k : ℕ) : QBF (k + 1) ∈ SigmaP (k + 1) :=
  qbfProblem_sigmaSODefinable (k + 1) _

/-- **QBF with a universal outermost block and `k + 1` blocks is in
`Πₖ₊₁ᵖ`.** -/
theorem qbfPi_mem_piP (k : ℕ) : QBFPi (k + 1) ∈ PiP (k + 1) :=
  qbfProblem_piSODefinable (k + 1) _

/-- Both matrix shapes stay inside the level: the shape only matters for
hardness. -/
theorem qbfProblem_mem_sigmaP (k : ℕ) (cnf : Bool) :
    QbfProblem (k + 1) true cnf ∈ SigmaP (k + 1) :=
  qbfProblem_sigmaSODefinable (k + 1) cnf

/-- Dually for a universal outermost block. -/
theorem qbfProblem_mem_piP (k : ℕ) (cnf : Bool) :
    QbfProblem (k + 1) false cnf ∈ PiP (k + 1) :=
  qbfProblem_piSODefinable (k + 1) cnf

/-- **QBF with `k + 1` alternating blocks is `Σₖ₊₁ᵖ`-complete.** Membership is
`DescriptiveComplexity.qbf_mem_sigmaP` – guess the `k + 1` truth assignments as monadic
second-order relations and evaluate the matrix first-order. Hardness is
`DescriptiveComplexity.qbf_hard_of_sigmaSODefinable`, the marked Tseitin discharge. -/
theorem QBF_complete (k : ℕ) : (SigmaP (k + 1)).Complete (QBF (k + 1)) :=
  ⟨qbf_mem_sigmaP k,
    (hard_sigmaP_succ_iff k (QBF (k + 1))).mpr fun Q hQ =>
      qbf_hard_of_sigmaSODefinable k Q hQ⟩

/-- QBF is `Σₖ₊₁ᵖ`-hard. -/
theorem qbf_hard (k : ℕ) : (SigmaP (k + 1)).Hard (QBF (k + 1)) :=
  (QBF_complete k).hard

/-- QBF with one block and a conjunctive matrix is NP-complete – it is
essentially SAT with all variables marked. -/
theorem QBF_one_NP_complete : NP.Complete (QBF 1) :=
  QBF_complete 0

/-- QBF with one block is in NP. -/
theorem qbf_one_mem_NP : QBF 1 ∈ NP :=
  qbf_mem_sigmaP 0

end DescriptiveComplexity
