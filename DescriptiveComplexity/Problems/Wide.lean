/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Wide.Expansion
import DescriptiveComplexity.Problems.Wide.WellFormed
import DescriptiveComplexity.Problems.Wide.Membership

/-!
# The wide machine: a machine model for NEXPTIME and EXPSPACE

Umbrella file for the **wide machine** – a Turing machine whose control is an
ordinary part of its instance and whose tape is addressed by the *subsets* of
that instance. An instance of size `n` therefore describes a machine with `2^n`
cells and `2^n` time steps, and the two resource variants of the model live one
exponential above `DescriptiveComplexity.NTMAccept` and
`DescriptiveComplexity.NTMAcceptSpace`:

| problem | resource | class |
|---|---|---|
| `DescriptiveComplexity.WideAccept` | `2^n` steps, nondeterministic | NEXPTIME |
| `DescriptiveComplexity.WideAcceptSpace` | `2^n` cells, no step bound | EXPSPACE |
| `DescriptiveComplexity.DWideAcceptSpace` | the same, deterministic | EXPSPACE |

## Why this is the right shape

`DescriptiveComplexity.ATMAcceptSpace` reaches EXPTIME because *alternation*
supplies an exponential for free: the machine has polynomially many cells and it
is its configuration space that is exponential. That ceiling is hard – with
polynomially many cells an ordinary machine problem tops out at PSPACE and an
alternating one at EXPTIME, whatever the play length – so NEXPTIME and EXPSPACE
need the exponentially large index set to appear in **the target problem's own
semantics**, which is exactly what this model does: its universe
(`DescriptiveComplexity.WPoint`) is the power set of the instance plus the
instance itself.

Read that way the model is not new. It *is* an ordinary machine, over the
universe of an exponential expansion, and that is how the memberships are
proved: `DescriptiveComplexity.Problems.Wide.Expansion` writes the expansion of
`FirstOrder.Language.wide`-structures whose expanded vocabulary is
`FirstOrder.Language.turing`, `DescriptiveComplexity.Problems.Wide.Membership`
identifies its points with the machine's universe, and the memberships are then
`DescriptiveComplexity.ExpDefinable` applied to
`DescriptiveComplexity.ntmAccept_mem_NP` and
`DescriptiveComplexity.ntmAcceptSpace_mem_PSPACE`. No resource argument occurs
anywhere; the composition used is an expansion *after* a problem, which is the
composition that exists.

## What is proved here, and what is not

**Proved**: the three problems are iso-invariant problems of the catalog, their
promises reduce to three first-order conditions on the instance
(`DescriptiveComplexity.wideData_wellFormed_iff`), and all three are *members*
of their class – the first natural members NEXPTIME and EXPSPACE have.

**Not proved**: hardness. Completeness for these two classes needs the machine
written in logic, as `DescriptiveComplexity.ATMAcceptSpace` needed for EXPTIME:
a reduction cannot be routed through the outer composition of an interpretation
with an expansion, which does not exist in general. The plan is `EXPONENTIAL.md`
§6.4.4: a shared evaluator for a fixed first-order kernel whose quantifiers range
over addresses, then a nondeterministic sweep for NEXPTIME and a partial-fixpoint
loop for EXPSPACE.
-/
