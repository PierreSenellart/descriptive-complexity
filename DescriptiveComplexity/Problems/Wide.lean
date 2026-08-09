/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Wide.Expansion
import DescriptiveComplexity.Problems.Wide.WellFormed
import DescriptiveComplexity.Problems.Wide.Increment
import DescriptiveComplexity.Problems.Wide.Blocks
import DescriptiveComplexity.Problems.Wide.Sweep
import DescriptiveComplexity.Problems.Wide.Fold
import DescriptiveComplexity.Problems.Wide.Step
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
(`DescriptiveComplexity.wideData_wellFormed_iff`), all three are *members* of
their class – the first natural members NEXPTIME and EXPSPACE have – and the
machine's three head primitives are identified
(`DescriptiveComplexity.Problems.Wide.Increment`): the head starts on the empty
address, the last cell is the full one, and one step is the **binary
increment**. That last one is what a hardness reduction will build on, since a
head cannot read the digits of its own address and must instead maintain a mirror
of it by incrementing. `DescriptiveComplexity.Problems.Wide.Blocks` then reads an
address **block by block**, which is how a reduction will lay one out – one block
per variable of the kernel, one for scratch – and proves the two facts the layout
turns on: the address order is lexicographic on the blocks
(`DescriptiveComplexity.wmSetLt_lexRel_iff`), so addresses sharing a prefix of
blocks are consecutive, and the increment carries block by block
(`DescriptiveComplexity.wmIncr_lexRel_iff`), which is the roll-over information a
sweep folds by. `DescriptiveComplexity.Problems.Wide.Sweep` closes the layer with
the primitive a program cites instead of reasoning about runs: **a machine that
steps at every increment of its address runs from the empty address to any
address, within its clock**
(`DescriptiveComplexity.stepsIn_of_wideSweep`,
`DescriptiveComplexity.accepts_of_wideSweep`), together with the initial
configuration a reduction starts from – a start state, the head on the empty
address, every cell blank (`DescriptiveComplexity.isInit_wide`). Both promises a
reduction owes are reduced to first-order conditions on the instance –
well-formedness by `DescriptiveComplexity.wideData_wellFormed_iff` and determinism
by `DescriptiveComplexity.wideData_deterministic_iff`, the latter being what lets
the deterministic side of EXPSPACE be proved hard and the nondeterministic one
inherit it. Finally `DescriptiveComplexity.Problems.Wide.Fold` supplies the
machine-free half of a sweep, and the reason a *nondeterministic* machine can
evaluate a first-order kernel at all: an alternating quantifier prefix
(`DescriptiveComplexity.altQuantFrom`) is the **fold of its matrix along the
lexicographic enumeration of its valuations**, so `k` accumulator bits in the
control and one matrix evaluation per step suffice
(`DescriptiveComplexity.foldFrom_bot`, `DescriptiveComplexity.foldFrom_top`,
`DescriptiveComplexity.foldFrom_above`, `DescriptiveComplexity.foldFrom_carry`,
`DescriptiveComplexity.foldFrom_below`), and
`DescriptiveComplexity.Problems.Wide.Step` packages the eight obligations of a
single machine step into one right-moving (or left-moving) move and, on top of
them, the shape a one-pass program has:
`DescriptiveComplexity.accepts_of_rightSweep` – give a state and a tape per
address, check one transition per increment, start blank on the empty address,
end accepting.

**Not proved**: hardness. Completeness for these two classes needs the machine
written in logic, as `DescriptiveComplexity.ATMAcceptSpace` needed for EXPTIME:
a reduction cannot be routed through the outer composition of an interpretation
with an expansion, which does not exist in general. The plan is `EXPONENTIAL.md`
§6.4.4: one monotone sweep of the tape that folds a fixed prenex kernel, the
valuation being the head position with a mirror kept in scratch, then a
partial-fixpoint loop on top of it for EXPSPACE.
-/
