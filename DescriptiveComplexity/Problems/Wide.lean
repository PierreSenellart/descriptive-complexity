/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Wide.Expansion
import DescriptiveComplexity.Problems.Wide.Tiling
import DescriptiveComplexity.Problems.Wide.TilingExp
import DescriptiveComplexity.Problems.Wide.TilingHard
import DescriptiveComplexity.Problems.Wide.CorridorHard
import DescriptiveComplexity.Problems.Wide.WellFormed
import DescriptiveComplexity.Problems.Wide.Increment
import DescriptiveComplexity.Problems.Wide.Blocks
import DescriptiveComplexity.Problems.Wide.Sweep
import DescriptiveComplexity.Problems.Wide.Fold
import DescriptiveComplexity.Problems.Wide.Step
import DescriptiveComplexity.Problems.Wide.Roam
import DescriptiveComplexity.Problems.Wide.Marks
import DescriptiveComplexity.Problems.Wide.Tape
import DescriptiveComplexity.Problems.Wide.RegFile
import DescriptiveComplexity.Problems.Wide.LowFile
import DescriptiveComplexity.Problems.Wide.IxAddr
import DescriptiveComplexity.Problems.Wide.BlkFile
import DescriptiveComplexity.Problems.Wide.BlkLayout
import DescriptiveComplexity.Problems.Wide.NexSpec
import DescriptiveComplexity.Problems.Wide.NexBuild
import DescriptiveComplexity.Problems.Wide.NexGuess
import DescriptiveComplexity.Problems.Wide.NexEval
import DescriptiveComplexity.Problems.Wide.NexSpine
import DescriptiveComplexity.Problems.Wide.NexDef
import DescriptiveComplexity.Problems.Wide.NexInterp
import DescriptiveComplexity.Problems.Wide.NexRun
import DescriptiveComplexity.Problems.Wide.Walk
import DescriptiveComplexity.Problems.Wide.Mirror
import DescriptiveComplexity.Problems.Wide.Det
import DescriptiveComplexity.Problems.Wide.Test
import DescriptiveComplexity.Problems.Wide.DrawTags
import DescriptiveComplexity.Problems.Wide.DrawMatrix
import DescriptiveComplexity.Problems.Wide.DrawGeom
import DescriptiveComplexity.Problems.Wide.DrawShape
import DescriptiveComplexity.Problems.Wide.DrawTable
import DescriptiveComplexity.Problems.Wide.DrawRegion
import DescriptiveComplexity.Problems.Wide.DrawTracks
import DescriptiveComplexity.Problems.Wide.DrawRules
import DescriptiveComplexity.Problems.Wide.DrawPass
import DescriptiveComplexity.Problems.Wide.DrawScan
import DescriptiveComplexity.Problems.Wide.DrawRel
import DescriptiveComplexity.Problems.Wide.DrawEnc
import DescriptiveComplexity.Problems.Wide.DrawInner
import DescriptiveComplexity.Problems.Wide.DrawLoop
import DescriptiveComplexity.Problems.Wide.DrawSpec
import DescriptiveComplexity.Problems.Wide.DrawAddr
import DescriptiveComplexity.Problems.Wide.DrawOrd
import DescriptiveComplexity.Problems.Wide.DrawGate
import DescriptiveComplexity.Problems.Wide.DrawSlots
import DescriptiveComplexity.Problems.Wide.DrawSub
import DescriptiveComplexity.Problems.Wide.DrawInit
import DescriptiveComplexity.Problems.Wide.DrawAdv
import DescriptiveComplexity.Problems.Wide.DrawSweep
import DescriptiveComplexity.Problems.Wide.DrawTrip
import DescriptiveComplexity.Problems.Wide.DrawSeek
import DescriptiveComplexity.Problems.Wide.DrawRead
import DescriptiveComplexity.Problems.Wide.DrawAcc
import DescriptiveComplexity.Problems.Wide.DrawAtoms
import DescriptiveComplexity.Problems.Wide.DrawData
import DescriptiveComplexity.Problems.Wide.NexPack
import DescriptiveComplexity.Problems.Wide.DrawKit
import DescriptiveComplexity.Problems.Wide.DrawFactor
import DescriptiveComplexity.Problems.Wide.DrawDefKit
import DescriptiveComplexity.Problems.Wide.DrawDefTower
import DescriptiveComplexity.Problems.Wide.DrawDefStage
import DescriptiveComplexity.Problems.Wide.DrawDefKind
import DescriptiveComplexity.Problems.Wide.DrawDefVar
import DescriptiveComplexity.Problems.Wide.DrawDefProg
import DescriptiveComplexity.Problems.Wide.DrawDefAsm
import DescriptiveComplexity.Problems.Wide.DrawDefLoop
import DescriptiveComplexity.Problems.Wide.DrawDefCtl
import DescriptiveComplexity.Problems.Wide.DrawDefAcc
import DescriptiveComplexity.Problems.Wide.DrawDefTags
import DescriptiveComplexity.Problems.Wide.DrawDefName
import DescriptiveComplexity.Problems.Wide.DrawDefGate
import DescriptiveComplexity.Problems.Wide.DrawDefExp
import DescriptiveComplexity.Problems.Wide.DrawInterp
import DescriptiveComplexity.Problems.Wide.DrawPack
import DescriptiveComplexity.Problems.Wide.Double
import DescriptiveComplexity.Problems.Wide.RelExp
import DescriptiveComplexity.Problems.Wide.RelExpansion
import DescriptiveComplexity.Problems.Wide.RelExpMap
import DescriptiveComplexity.Problems.Wide.ShFinite
import DescriptiveComplexity.Problems.Wide.Reduce
import DescriptiveComplexity.Problems.Wide.DrawAsm
import DescriptiveComplexity.Problems.Wide.DrawTripKits
import DescriptiveComplexity.Problems.Wide.DrawIncrKit
import DescriptiveComplexity.Problems.Wide.DrawSweepKit
import DescriptiveComplexity.Problems.Wide.DrawAdvKit
import DescriptiveComplexity.Problems.Wide.DrawSeekKit
import DescriptiveComplexity.Problems.Wide.DrawReset
import DescriptiveComplexity.Problems.Wide.DrawSites
import DescriptiveComplexity.Problems.Wide.DrawBack
import DescriptiveComplexity.Problems.Wide.DrawBuild
import DescriptiveComplexity.Problems.Wide.DrawOuter
import DescriptiveComplexity.Problems.Wide.NexOuter
import DescriptiveComplexity.Problems.Wide.NexDet
import DescriptiveComplexity.Problems.Wide.DrawEval
import DescriptiveComplexity.Problems.Wide.DrawVar
import DescriptiveComplexity.Problems.Wide.DrawChain
import DescriptiveComplexity.Problems.Wide.DrawTuple
import DescriptiveComplexity.Problems.Wide.DrawStageAtom
import DescriptiveComplexity.Problems.Wide.DrawElem
import DescriptiveComplexity.Problems.Wide.DrawTagged
import DescriptiveComplexity.Problems.Wide.DrawSeq
import DescriptiveComplexity.Problems.Wide.DrawRepAtoms
import DescriptiveComplexity.Problems.Wide.DrawRound
import DescriptiveComplexity.Problems.Wide.DrawTower
import DescriptiveComplexity.Problems.Wide.DrawKindRule
import DescriptiveComplexity.Problems.Wide.DrawVarRule
import DescriptiveComplexity.Problems.Wide.DrawCtl
import DescriptiveComplexity.Problems.Wide.DrawName
import DescriptiveComplexity.Problems.Wide.DrawPad
import DescriptiveComplexity.Problems.Wide.DrawLeaf
import DescriptiveComplexity.Problems.Wide.DrawExp
import DescriptiveComplexity.Problems.Wide.DrawCmp
import DescriptiveComplexity.Problems.Wide.DrawAccCtl
import DescriptiveComplexity.Problems.Wide.DrawArgs
import DescriptiveComplexity.Problems.Wide.DrawProg
import DescriptiveComplexity.Problems.Wide.DrawRun
import DescriptiveComplexity.Problems.Wide.DrawRunElem
import DescriptiveComplexity.Problems.Wide.DrawRunTagged
import DescriptiveComplexity.Problems.Wide.DrawRunTuple
import DescriptiveComplexity.Problems.Wide.DrawRunVar
import DescriptiveComplexity.Problems.Wide.DrawRunEval
import DescriptiveComplexity.Problems.Wide.DrawRunSeq
import DescriptiveComplexity.Problems.Wide.DrawRunStage
import DescriptiveComplexity.Problems.Wide.DrawRunIter
import DescriptiveComplexity.Problems.Wide.DrawInstCmp
import DescriptiveComplexity.Problems.Wide.DrawInstStage
import DescriptiveComplexity.Problems.Wide.DrawIxStage
import DescriptiveComplexity.Problems.Wide.DrawIxExp
import DescriptiveComplexity.Problems.Wide.DrawIxGate
import DescriptiveComplexity.Problems.Wide.DrawIxIGate
import DescriptiveComplexity.Problems.Wide.DrawIxMat
import DescriptiveComplexity.Problems.Wide.DrawIxSeq
import DescriptiveComplexity.Problems.Wide.DrawIxRound
import DescriptiveComplexity.Problems.Wide.DrawIxVar
import DescriptiveComplexity.Problems.Wide.DrawIxEval
import DescriptiveComplexity.Problems.Wide.DrawIxWidth
import DescriptiveComplexity.Problems.Wide.DrawIxBridge
import DescriptiveComplexity.Problems.Wide.DrawIxPack
import DescriptiveComplexity.Problems.Wide.Limits
import DescriptiveComplexity.Problems.Wide.PadRules
import DescriptiveComplexity.Problems.Wide.RegChannelPad
import DescriptiveComplexity.Problems.Wide.RegChannelJoin
import DescriptiveComplexity.Problems.Wide.TrackWrites
import DescriptiveComplexity.Problems.Wide.RegChannelBack
import DescriptiveComplexity.Problems.Wide.RegChannel
import DescriptiveComplexity.Problems.Wide.RegChannelTape
import DescriptiveComplexity.Problems.Wide.RegChannelInit
import DescriptiveComplexity.Problems.Wide.RegChannelExpansion
import DescriptiveComplexity.Problems.Wide.RegChannelLaid
import DescriptiveComplexity.Problems.Wide.RegChannelEval
import DescriptiveComplexity.Problems.Wide.RegChannelProg
import DescriptiveComplexity.Problems.Wide.RegChannelEntry
import DescriptiveComplexity.Problems.Wide.RegChannelEnum
import DescriptiveComplexity.Problems.Wide.SpineSav
import DescriptiveComplexity.Problems.Wide.RegChannelWalk
import DescriptiveComplexity.Problems.Wide.RegChannelAccept
import DescriptiveComplexity.Problems.Wide.RegChannelYes
import DescriptiveComplexity.Problems.Wide.RegChannelNo
import DescriptiveComplexity.Problems.Wide.RegChannelReduce
import DescriptiveComplexity.Problems.Wide.DrawIxRoundSem
import DescriptiveComplexity.Problems.Wide.DrawIxVerdict
import DescriptiveComplexity.Problems.Wide.DrawIxSpineSem
import DescriptiveComplexity.Problems.Wide.DrawInstExp
import DescriptiveComplexity.Problems.Wide.DrawInstGate
import DescriptiveComplexity.Problems.Wide.DrawInstIGate
import DescriptiveComplexity.Problems.Wide.DrawInstMat
import DescriptiveComplexity.Problems.Wide.DrawInstSeq
import DescriptiveComplexity.Problems.Wide.DrawInstRound
import DescriptiveComplexity.Problems.Wide.DrawGateFacts
import DescriptiveComplexity.Problems.Wide.DrawInstVar
import DescriptiveComplexity.Problems.Wide.DrawRoundSem
import DescriptiveComplexity.Problems.Wide.DrawVerdict
import DescriptiveComplexity.Problems.Wide.DrawInstEval
import DescriptiveComplexity.Problems.Wide.DrawSpineSem
import DescriptiveComplexity.Problems.Wide.DrawRunOuter
import DescriptiveComplexity.Problems.Wide.DrawRunSpine
import DescriptiveComplexity.Problems.Wide.DrawValEnum
import DescriptiveComplexity.Problems.Wide.DrawHalt
import DescriptiveComplexity.Problems.Wide.DrawYes
import DescriptiveComplexity.Problems.Wide.DrawNo
import DescriptiveComplexity.Problems.Wide.Bridge
import DescriptiveComplexity.Problems.Wide.Instance
import DescriptiveComplexity.Problems.Wide.Key
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

**Proved**: the three problems are iso-invariant problems of the catalog and
**not vacuous** – `DescriptiveComplexity.wideAccept_nonvacuous` and its two
siblings exhibit the smallest instance there is, two elements and no transitions,
whose machine starts on the empty address in an accepting state – their
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
end accepting. `DescriptiveComplexity.Problems.Wide.Bridge` joins the two halves:
with the block index type taken to be `Fin n` – one index per variable of the
kernel, as a reduction may simply choose – the blocks of an address *are* a
valuation, and every hypothesis the fold's step rules ask for is read off
`DescriptiveComplexity.wmIncr_lexRel_iff`
(`DescriptiveComplexity.foldFrom_carry_of_wmIncr` and its two siblings). That the
layout is *definable* and not merely convenient is
`DescriptiveComplexity.Problems.Wide.Key`: the only order a first-order
interpretation can put on a tagged tuple universe is
`DescriptiveComplexity.tagTupleLe`, whose formula is
`DescriptiveComplexity.lexLeF`, and that order **is** the block-major
`DescriptiveComplexity.lexRel`
(`DescriptiveComplexity.Wide.tagTupleLe_iff_lexRel`) – so a reduction with tag type
`Fin n` draws an instance whose addresses decompose into one block per tag.

## The two programming models

`DescriptiveComplexity.WideAccept` counts its steps against the number of
addresses; the two space-bounded problems have *no* clock, acceptance being
`Relation.ReflTransGen` of the step relation. Programs for either may **roam** –
sweep up, sweep back down and start again – and the difference is only whether
the lengths are added up.
`DescriptiveComplexity.Problems.Wide.Roam` is that interface, and it states every
phase **twice**: once with a budget
(`DescriptiveComplexity.TMData.ReachesIn`, a run of at most `n` steps, which
composes by adding and may be raised) and once without, the second being the
first with the count forgotten. A phase up
(`DescriptiveComplexity.reachesIn_of_wideUp`,
`DescriptiveComplexity.reaches_of_wideUp`), a phase down
(`DescriptiveComplexity.reachesIn_of_wideDown`), the **scan** they are almost
always used for (`DescriptiveComplexity.reachesIn_scanRight`,
`DescriptiveComplexity.reachesIn_scanLeft` – hold the state, rewrite each symbol
by itself, walk until the scanning transition is withheld), and the two run
shapes `DescriptiveComplexity.accepts_of_wideRoam` and
`DescriptiveComplexity.acceptsSpace_of_wideRoam`. Every budget is a difference of
`DescriptiveComplexity.wideRank`s – of the number of addresses below one address
and below another – so consecutive phases telescope and no phase has to know where
the next one starts.

What the sum is compared against is `DescriptiveComplexity.card_wideAddr`: the
addresses **are** the subsets of the instance, so a wide machine's clock is
`2 ^ n` exactly, and a reduction buys itself `2 ^ (|Tag| · nᵈ)` steps by
choosing the tags and the dimension of its interpretation.
`DescriptiveComplexity.accepts_of_wideRoam_lt_two_pow` is the acceptance
statement in that form, which is the one a program's arithmetic produces.

Roaming is what dissolves the difficulty the model is built around – *a head
cannot read the digits of its own address* – without the lockstep mirror a
one-pass program needs. `DescriptiveComplexity.Problems.Wide.Marks` supplies the
missing half: the input channel writes at the **initial-segment** addresses, so a
reduction that names each element in the cell that element cuts gets `n`
distinguished cells, ordered like the elements
(`DescriptiveComplexity.wmSetLt_wmSeg`), disjoint
(`DescriptiveComplexity.wmSeg_injective`), missing the head's starting cell
(`DescriptiveComplexity.wmSetLt_empty_wmSeg`) and set up at time zero
(`DescriptiveComplexity.isInit_wide_marks`). One tape track over those `n` cells
is an `n`-bit **register**, a register is a mirror of an address, and a roaming
machine may walk to it and back as often as it likes. That is the register file a
space-bounded program computes with.

What a walk asks of a file is only that its cells be **strictly monotone** in the
address order, and that none of them be the empty address:
`DescriptiveComplexity.RegFile` is that interface, and distinctness
(`DescriptiveComplexity.RegFile.injective`), the converse comparison
(`DescriptiveComplexity.RegFile.lt_iff`) and the fact that nothing is a register
between two consecutive ones (`DescriptiveComplexity.RegFile.gap`) are all
derived from it. The interface does not care what indexes the cells:
`DescriptiveComplexity.IxFile` is it at an arbitrary ordered index, of which
`DescriptiveComplexity.RegFile` – one register per element – is the diagonal
case, and the general form is what a program too tightly clocked to lay a
register out per element will need. The input channel's ladder is one such file
(`DescriptiveComplexity.wmSegFile`) and it is the one a space-bounded program
uses; but it is a geometric ruler in the top half of the tape, so a program on a
clock cannot walk it twice. `DescriptiveComplexity.Problems.Wide.LowFile` builds
the other one: the registers are `n` **consecutive addresses**
(`DescriptiveComplexity.segFile`), so consecutive registers are consecutive cells
(`DescriptiveComplexity.segFile_gap`) and a pass over the file costs one step per
element. Where the stretch sits is the caller's choice and is not a free one – the
subroutines written for the ruler assume the file lies *above* the data, so a
program that wants them unchanged puts its own file above its data too, while
`DescriptiveComplexity.lowFile` takes the first `n` nonempty addresses and lies
below everything (`DescriptiveComplexity.wideRank_lowCell_le`). The same
construction at a *coarser* index is `DescriptiveComplexity.blkFile`, one
register per block and tuple
(`DescriptiveComplexity.Problems.Wide.BlkFile`): what a program too tightly
clocked to give every element a register can afford, and all a register's
contents ever depend on. What such a file can still do is hold an **address**,
which is what a random access needs: `DescriptiveComplexity.ixAddr`
(`DescriptiveComplexity.Problems.Wide.IxAddr`) is the address a mark on the
registers stands for, and it carries the order – comparison
(`DescriptiveComplexity.wmSetLe_ixAddr`) and increment
(`DescriptiveComplexity.wmIncr_ixAddr`) – as soon as the elements the registers
name are upward closed. For a clocked program's file they are, the argument tags
being the last ones (`DescriptiveComplexity.blkIxElt_mono`,
`DescriptiveComplexity.blkIxElt_up`), so the addresses it can hold are exactly the
logical ones. A program with that file writes its
own names into those cells as it walks past them – it knows which is whose by
`DescriptiveComplexity.exists_lowCell_eq`, the registers being exactly the
addresses of rank between `1` and `n` and a rank determining its address
(`DescriptiveComplexity.wideRank_injective`) – and that there is room for it is
`DescriptiveComplexity.card_lt_card_wideAddr`.

Two files finish the model. `DescriptiveComplexity.Problems.Wide.Tape` observes
that a program's tape is never a general `WPoint A → WPoint A` but a function of
the *address* – the control points are not cells and keep their blank for ever –
and restates the step, the scans and the initial configuration in that form
(`DescriptiveComplexity.wideTape`,
`DescriptiveComplexity.step_wideTape_right`,
`DescriptiveComplexity.reaches_scan_tape`,
`DescriptiveComplexity.isInit_wideTape`,
`DescriptiveComplexity.acceptsSpace_of_wideTape`), which removes the frame
condition, the symbol equation and the control-point case from every step of
every phase. It also has the phase a program lays anything out with – the
**writing sweep** `DescriptiveComplexity.reachesIn_of_wideWrite`: sweep up,
writing one symbol per cell, holding the tape
`DescriptiveComplexity.midTape` that is rewritten below the head and untouched
above it. The new symbols are a parameter, so the same statement is a
deterministic layout phase and a **guessing** one: whatever the certificate, the
run that writes it exists. `DescriptiveComplexity.Problems.Wide.Walk` is then the phase a
space-bounded machine spends its life in: **stand on the cell of `u`, write
there, scan right to the cell of the next element, repeat**
(`DescriptiveComplexity.reaches_regStep`), and the traversal of the whole file
by one induction given once (`DescriptiveComplexity.reaches_regWalk`) – state and
tape handed over as functions of the element the pointer has reached. What makes
the move a single scan rather than a search is that consecutive elements mark
cells with nothing marked between them
(`DescriptiveComplexity.not_wmSeg_between`).

The first subroutine written on all of it is
`DescriptiveComplexity.Problems.Wide.Mirror`, and it is the one every address
computation goes through: **incrementing the mirror**
(`DescriptiveComplexity.reaches_mirrorIncr`). Moving the working cell one to the
right means adding one to the mirror, and adding one is a walk down the register
file clearing the digits that are set, setting the first that is clear and
stopping – which is the binary increment of
`DescriptiveComplexity.Problems.Wide.Increment` because its least significant
digit is the `WMLe`-greatest element. The tape is taken as a function *of the
mirror*, with one coherence condition saying that changing a digit changes that
digit's cell and nothing else, so whatever else a program keeps on its tape rides
along untouched and no track discipline is fixed. The machine ends in the stopped
state whatever the mirror was, so a caller reads “the increment is finished” off
the state and never off the tape.

`DescriptiveComplexity.Problems.Wide.Test` is the read-only half:
`DescriptiveComplexity.reaches_fileTest` walks the file asking one question of
each register – *do these two tracks agree here?*, *is this track clear here?* –
and comes back with the verdict in its **state**, the tape exactly as it found
it. Both subroutines are the same shape, so what they share is settled in
`DescriptiveComplexity.Problems.Wide.Walk`: a downward pass carries one bit in
its control, and since it walks downwards that bit is a function of the *suffix*
(`DescriptiveComplexity.accState`, `DescriptiveComplexity.accStateAfter`, with
`DescriptiveComplexity.accStateAfter_succ` saying that leaving one register is
arriving at the next one down, and
`DescriptiveComplexity.accStateAfter_bot_pos`/`_neg` reading off the verdict).
Getting *to* a register is `DescriptiveComplexity.reaches_toReg` and its downward
twin – one scan each, stopped by the name the register carries.

Two facts about the layout keep all of this from colliding with the program's
data. Every marked cell contains the `WMLe`-least element, and that element is the
most significant digit, so the register file sits in the **upper half** of the
tape and the addresses missing it – the **working area**, still exponentially many
cells – lie below every register
(`DescriptiveComplexity.wmSetLt_wmSeg_of_not_bot`). And an outer loop over that
working area is `DescriptiveComplexity.reachesIn_of_wideRounds` and its erasure
`DescriptiveComplexity.reaches_of_wideRounds`: the same shape as a sweep, but with
a whole *run* between an address and its increment rather than a single step. That
is what a program's loops are written with. The budgeted form charges a round `w`
steps and the loop the product of `w` with the addresses crossed; the erased form
charges nothing, which is what lets a space-bounded program iterate a fixed point
through exponentially many stages and what a clock forbids. Its semantic twin
`DescriptiveComplexity.holds_of_wideRounds` walks the same stretch at the same
measure to say what is *true* when the machine gets there: a property of the
addresses established at the bottom and carried across each increment holds
everywhere the loop has been. The two are used together, one taking the round's
machine hypothesis and the other its tape hypothesis.

One more piece of the layer belongs to no single pass and is used by all three.
The passes take the tape as a function of *one track* and each asks the same
coherence condition: changing the track at one element changes the tape at that
element's cell and nowhere else. A program does not check that by hand – it reads
its track through `DescriptiveComplexity.regBit` (the digit at a register cell,
nothing anywhere else) and `DescriptiveComplexity.regBit_congr` is the condition,
discharged once for every program and every alphabet.

## The EXPSPACE reduction, begun

Everything below lives in `DescriptiveComplexity.Draw`, and the modules carrying
it are the `Draw…` ones: the name is what a reduction does with them – it
**draws** a program for the wide machine, tags, tracks, rules, sweeps, seeks and
the evaluation of a `DescriptiveComplexity.StepDef` – and not which problem it
draws it for. The partial fixed point is the first client and the clocked
machine of `DescriptiveComplexity.Problems.Wide.NexRun` the second, running the
same drawing with the iteration removed and one field of the record left unread
(`DescriptiveComplexity.Draw.Data.ofKernel`, step formulas `⊥`); the `DrawIx…`
modules are the same statements at an arbitrary register file, which is what the
second client needed.

`DescriptiveComplexity.Problems.Wide.DrawTags` fixes the universe the hardness
reduction draws: a tagged tuple universe whose tags are `ctrl` (the states and
transitions), `sym` (the alphabet) and the **point-valued** blocks `arg i` – **in
that order**, so the point-valued blocks are the *least* significant ones. Their
index is an arbitrary type rather than `Fin κ`, and for a reason: a program's outer
loop runs the head over the valuations of the fixed-point variable, so it needs one
block per argument of it, while its inner loop runs a *register* over the valuations
of the step formula's quantifier prefix, and a register is an address too, so it
needs one block per quantified variable. The two counts have no reason to agree.
Putting the fixed-point's arguments first makes the rest the deeper blocks, which
costs nothing: a stage is written at the argument blocks only, hence is constant
below them and may be read at any address with the right prefix.

Two consequences follow from the order alone, and the whole layout rests on
them: the addresses a program reasons about, the valuations of the fixed-point
variable, are an **initial interval** of the tape
(`DescriptiveComplexity.Draw.wmSetLe_logicalTop`, joined to the machine's own order
by `DescriptiveComplexity.Draw.Table.wmSetLe_logicalTop_reads`), which is the upper
bound `DescriptiveComplexity.reaches_of_wideRounds` asks for; and the least element of
the universe lies in the `ctrl` block, so the register file – every cell of which
contains it – sits above every logical address, and data and registers cannot
collide.

One structural note, since it is what the transition table will hang on: the
subroutines above take **their states as parameters**, so a program with several
call sites of the same subroutine gives each its own states and needs no
continuation label and no dispatch. Its phase set is exactly the list of its call
sites.

`DescriptiveComplexity.Problems.Wide.DrawMatrix` supplies the semantic half of the
step the program spends its time in. The machine evaluates the matrix of its step
formula **atom by atom** – a subroutine per atom, the accumulating assignment in
the *coordinates* of the state – and that is correct because a quantifier-free
formula is a Boolean function of its atoms:
`DescriptiveComplexity.Draw.realize_qfValue` says its realization is
`DescriptiveComplexity.Draw.qfValue` at the assignment that reads each atom off the
structure, and `DescriptiveComplexity.Draw.qfValue_congr` says only the atoms of
`DescriptiveComplexity.Draw.qfAtoms` matter. Those two are why the phase count is
*linear* in the number of atoms rather than exponential: the machine visits the
atoms once, and the final transition is a disjunction over the assignments that
satisfy `qfValue`, a finite list a defining formula can write out. The recursion
is total and the correctness is by induction on `IsQF`, the shape
`Exponential/Matrix.lean` uses for the same reason.

`DescriptiveComplexity.Problems.Wide.DrawGeom` says which elements the states, the
symbols and the transitions *are*: each carries a payload of `c` coordinates
(`DescriptiveComplexity.Draw.pad`) with a designated element beyond it, and the
kind is the tag – `phase p` for a state, `sym` for a symbol, `ctrl r` for a
transition of the rule `r`. The padding is not decoration: without it an element
would have `n^(dd-c)` spellings, and the machine's promises are that there is
*one* start state, *one* blank and at most one transition per state and symbol.
`DescriptiveComplexity.Draw.pad_injective` and the three `_ne_` lemmas are the
distinctness those obligations are discharged from.

`DescriptiveComplexity.Problems.Wide.DrawTable` is the transition table itself,
and the two promises the emitted instance has to keep. A table names, rule by
rule, a guard, the two phases, the payloads of the state and of the symbol on
each side, and the direction; the eleven relations of
`FirstOrder.Language.wide` are then read off it
(`DescriptiveComplexity.Draw.Table.Reads`), and a program's whole interaction with
it is two theorems – `DescriptiveComplexity.Draw.Table.fire_right` and
`DescriptiveComplexity.Draw.Table.fire_left`, a rule firing with its six
attributes, which is the shape every subroutine above asks for. The promises cost
what the layout was built to make them cost:
`DescriptiveComplexity.Draw.Table.wellFormed` is the order being
`DescriptiveComplexity.tagTupleLe` plus the input and the blank being written as
equations, and `DescriptiveComplexity.Draw.Table.deterministic` reduces to one
condition on the table, `DescriptiveComplexity.Draw.Table.Sep`: two guarded rules
that apply in the same state and read the same symbol are the same rule with the
same data.

What the interpretation that emits such an instance owes, and the algebra that
pays it, is `DescriptiveComplexity.Problems.Wide.DrawFactor`. An interpretation
carries *one* formula per relation symbol and tag tuple, so the obligation is
quantified over the instance: `DescriptiveComplexity.Draw.Env` bundles a finite
nonempty linearly ordered structure with the two elements a reduction may
designate – the order's least and greatest – and
`DescriptiveComplexity.Draw.URuleDefinable` says of a rule, at every such
environment at once, that its two phases and its direction are decided when the
formula is built, that its guard is a function of the **equality pattern** of
its data (`DescriptiveComplexity.EqPattern`), and that the pointer it leaves
and the tracks it writes are named slot by slot by
`DescriptiveComplexity.SlotVal` – a copy, one of the two designated elements,
or the **next** element after a slot, which is what advancing a loop variable
needs and the only source that reads the order. The atoms and connectives are
there (a slot holds `one`, a slot holds `zero`, two slots hold the same
element; conjunctions and disjunctions over an arbitrary index; a bit whose
question is itself definable; a choice between definably separated cases), and
the discharge follows the program's own shape:
`DescriptiveComplexity.Problems.Wide.DrawDefKit` does every leaf kit – the read
and write trips, the file test, the three track passes, the increment, the
seek, the advance, the reset, the walk home and the two sweeps – and
`DescriptiveComplexity.Problems.Wide.DrawDefTower` carries the statement through
the combinators – the chain, the sequencer, the element loop, the tag-branched
machinery and the tuple loop – each checkpoint's dispatch being the standard
exit guard conjoined with the caller's question, with the caller's control
update as its `dstSt`. Above them the program's own two guards are definable
once (`DescriptiveComplexity.Draw.Data.uGDefinable_exitG` and
`uGDefinable_nameG`) and the tower closes:
`DescriptiveComplexity.Problems.Wide.DrawDefStage` the stage atom's machinery,
`DrawDefKind` the three parameter packs
(`DescriptiveComplexity.Draw.UElemArgsDef`, `UTagArgsDef`,
`DescriptiveComplexity.Draw.Data.UStageArgsDef` – a pack's *static* fields,
which slot a trip walks and which block it names, may not depend on the
instance, and `DescriptiveComplexity.Draw.UConst` says so) and an atom kind's
machinery, `DrawDefVar` the matrix and the two runs of gates, `DrawDefProg` one
round, one variable's machinery, the evaluation's spine and the outer loop,
and `DrawDefAsm` the assembly – `uRulesDefinable_progAsm`, the whole rule set,
conditional only on the semantic packs meeting
`DescriptiveComplexity.Draw.Data.UVarArgsDef`.

Two files pay the packs' recurring debts. The **loop element** is the one write
that is not a copy (`DescriptiveComplexity.Problems.Wide.DrawDefLoop`):
advancing it is `DescriptiveComplexity.Draw.tupNext`, whose coordinate at the
carry is the order-successor, and
`DescriptiveComplexity.Draw.tupNext_apply_of_carry` reads it off – below the
carry a copy, at it the next element, above it the least one – with the carry
itself decided by which coordinates are maximal, hence by the pattern
(`uStDefinable_advLvE`/`uStDefinable_initLvE`/`uGDefinable_isMaxLvE`, and their
narrow twins). And the **control** is bits throughout
(`DescriptiveComplexity.Problems.Wide.DrawDefCtl`): every write is
`DescriptiveComplexity.Draw.Data.putVec` or its one-slot case `setCtl`, and
every read an existential over the levels of a slot family, so one lemma per
shape settles the layer. On top of it the **folds**
(`DescriptiveComplexity.Problems.Wide.DrawDefAcc`): reading one back is
`DescriptiveComplexity.Draw.chainFrom`, a recursion down a fixed number of
levels, so recursing the same way builds the pattern function
(`uGDefinable_chainFrom`, `accVerdict`, `sacVerdict`); writing one at a carry
is `uStDefinable_carryVec` and its two instances; and the matrix's own value at
its atoms' verdicts is the same shape over the syntax
(`uGDefinable_qfValue`, `uGDefinable_postLeaf`).
`DescriptiveComplexity.Problems.Wide.DrawDefTags` settles what a gate's branch
dispatches on – the decoding outright, and the *total* dispatch because
`DescriptiveComplexity.Draw.Data.defTag` takes its tag from a nonemptiness of
`X.Tag` rather than from a point, so that no instance can move it
(`uConst_defTag`). And
`DescriptiveComplexity.Problems.Wide.DrawDefName` settles the **names** a trip
walks to: an encoded coordinate holds a component of the one-hot code, a
payload position or the clear element, and which it holds the layout decides
when the formula is built (`uReadable_encTup`), so a naming guard is definable
as soon as its payload is (`uGDefinable_nameGF_of_readable`,
`uGDefinable_tagWitnessMatch`, `uGDefinable_domMatch`). The same reading
removes the existential over a *tuple of the instance* in the gates'
well-shapedness question: the payload coordinates carry no condition – a
witness is read straight off the cell – and every other coordinate is pinned
(`uGDefinable_exists_encAsgTup`, `uGDefinable_wellShapedG`). Last,
`DescriptiveComplexity.Problems.Wide.DrawDefGate` does a gate's **four folds** –
started, advanced, and the two conjoining exits. Each is two or three writes
nested, and what makes them definable is not new machinery but the
*commutations*: the loop element, the sub-fold's accumulators and the sub-leaf
flag are disjoint registers, so each write reads what it was given
(`uStDefinable_putVec_comp`, `uStDefinable_putLvE_comp`), and the coordinate the
fold carries is again a question about which coordinates are maximal
(`uGDefinable_tupCarry_eq`). With them
`DescriptiveComplexity.Problems.Wide.DrawDefExp` closes the discharge: an
expansion atom runs the gates' machinery one exponent along, so its pack is a
field-by-field check (`uTagArgsDef_expArgs`), and beside it the comparison and
stage atoms (`uElemArgsDef_cmpArgs`, `uStageArgsDef_stageArgs`) and the two
gate blocks (`uTagArgsDef_gateArgs`, `uTagArgsDef_igateArgs`). The result is
`DescriptiveComplexity.Draw.Data.uVarArgsDef_varArgsOf` – the semantic packs
the reduction computes meet their obligation – and with it
`uRulesDefinable_progOf`: **every rule of the emitted machine is written down
by one formula for every instance**, which is what an interpretation needs.

`DescriptiveComplexity.Problems.Wide.DrawInterp` begins the writing down. Where
the coordinates go is fixed once: a defining formula of an `n`-ary relation has
free variables `Fin n × Fin dd`, a payload occupies the first
`card (CtlIx ⊕ SlotIx)` of an argument's, and the guard and payload formulas the
definability layer hands over are **relabeled** onto them and nothing else
(`DescriptiveComplexity.Draw.guardAt`, `payAt`). Every one of the eleven
relations is then one of three shapes: a **guarded padded tuple**
(`padGuardF` – a transition, an accepting state), an **attribute**
(`attrF` – an element of a tag the rule names whose payload it writes from the
transition's own), or a **constant** (`constF` – a tag and the all-clear tuple,
the start state and the blank), each with its realization, and
`DescriptiveComplexity.Draw.eq_pad_iff` is what splits “is this padded tuple”
into the two halves a formula can say separately. The input channel's mark asks
two questions the interpreted universe would otherwise have to be quantified
over – is this cell the first, is it the last – and it must not be:
`DescriptiveComplexity.Draw.isLeast_tagTupleLe_iff` and
`isGreatest_tagTupleLe_iff` say that in the block-major order an element is
least exactly when its tag is the least tag and its tuple is all-clear, and
greatest exactly when its tag is the greatest and its tuple all-set – a tag
decision conjoined with a shape formula.

On top of them the **transitions and their five attributes** are written down.
`DescriptiveComplexity.Draw.Data.RTag` is the rule names as a type the
instance does not mention and `ITag` the tags of the interpreted universe;
`srcPhOf`, `dstPhOf`, `rightOf`, `guardFOf`, `dstFOf`, `wrFOf` (and the two
rule-independent `srcFOf`, `readFOf`) are the static data
`DescriptiveComplexity.Draw.URuleDefinable` says a rule has, extracted with
their specifications; and `trF`, `rightF`, `srcF`, `readF`, `dstF`, `writeF`
are the formulas, each with the realization that says it holds exactly of what
`DescriptiveComplexity.Draw.Table` says it should.

The remaining five are the two constants (`startF`, `blankF`), the accepting
states (`accF`, a `padGuardF` at the program's accepting predicate), the order
– which is `DescriptiveComplexity.lexLeF`, the tags compared when the formula is
built – and the **input channel**, the one with content. Its mark is
`DescriptiveComplexity.Draw.slotMark`, a register file, and every slot of it is a
tag decision, a shape formula or an equality of variables: the register flag is
set, the two extremes are the lemmas above, the block flags decode the cell's
tag, the name slots carry the cell's own first `dd₀` coordinates and the padding
flag is `canonF dd0` (`markSlotF`, `markCoordF`, `markF`, `inpF`). Not one of
them quantifies over the interpreted universe.

`DescriptiveComplexity.Draw.Data.drawInterp` is then the interpretation – one
formula per relation symbol and tuple of tags – and
`DescriptiveComplexity.Draw.Data.reads_progFrom` its point: **the interpreted
structure reads the program's table** (`DescriptiveComplexity.Draw.Table.Reads`),
so everything the run layer proved under that hypothesis applies to it. The
eleven obligations are eleven definitional unfoldings through
`relMap_one`/`relMap_two`; the only two rewrites are a rule's two phases, which
`srcPhOf` and `dstPhOf` name. `DescriptiveComplexity.Draw.Data.progFrom` is the
program at one instance – the rules the definability layer hands over with the
reduction's constants, an all-clear pointer, an all-clear blank and the register
file.

`DescriptiveComplexity.Problems.Wide.DrawPack` packs a source into that record.
`DescriptiveComplexity.Draw.exists_prenexPack` gives the prefix normal form of
every formula the program evaluates, but the *shortest* one, and a step
definition with only nullary variables and quantifier-free packs would leave the
address blocks `Fin ko ⊕ₗ Fin ki` **empty** – which is what `reaches_mainB`
spends. So the packs are padded, not cased on: `DescriptiveComplexity.Draw.PrenexPack.succ`
adds one vacuous innermost level, whose whole content is
`DescriptiveComplexity.Draw.altQuantFrom_liftLast` – a prefix over a predicate
that ignores its last coordinate is the prefix without it, in *both* polarities,
because the universe is nonempty. Beside it `DescriptiveComplexity.Draw.stdLayout`
is the encoding layout at the budget `encDim X` (the one-hot code first, the
payload after it) and `DescriptiveComplexity.Draw.Data.ofSource` is the record,
with `Draw.Data.ki_pos` for the block index.

`DescriptiveComplexity.Problems.Wide.NexPack` packs the source a
*nondeterministic* program is built from into the **same** record. That source is
a `DescriptiveComplexity.NexKernel` – an expansion, a block of relation variables
to guess, a first-order sentence to check of the guess – which is what
`DescriptiveComplexity.ExpDefinable` `DescriptiveComplexity.NP` unfolds to
(`DescriptiveComplexity.exists_nexKernel`). Put the guessed block where the
fixed-point variables go and the kernel where the output sentence goes
(`DescriptiveComplexity.NexKernel.toStepDef`) and there is nothing left to
define: the tracks a symbol carries are indexed by the block either way,
`DescriptiveComplexity.Draw.MatAtom` classifies the atoms of a matrix over a
**block** rather than over a fixed-point definition, so a stage atom and an atom
of a guess are the same thing, and
`DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` – the output evaluation of a
fixed-point program – is already the whole evaluation of a nondeterministic one
(`DescriptiveComplexity.Draw.Data.exists_out_iff_gateMat`). The step formulas
of a packed kernel are `⊥` and no program reads them; their only trace is that
the derived dimensions, being maxima over the variables, are the kernel's own
values or an unread step's vacuous demand, whichever is larger.

`DescriptiveComplexity.Problems.Wide.Double` fixes the one thing the reduction
cannot arrange after the fact. Every track of the machine is an *element* of the
base universe, so the construction needs two of them, and a reduction has to be
correct at one-element structures too. So the machinery is run not at the
instance but at a **doubled** universe (`DescriptiveComplexity.Draw.dblInterp`):
`Bool × (Fin 1 → A)`, the `false` copy carrying the instance's relations and
marked by the `old` symbol of `DescriptiveComplexity.newLang`, the `true` copy
junk. It is never a singleton (`DescriptiveComplexity.Draw.dblPt_ne`), it is a
plain one-dimensional interpretation – so composing it under the wide
interpretation keeps the dimension and only multiplies the tags by `Bool ^ dd` –
and it is exactly the extended universe of value invention, so
`DescriptiveComplexity.relativizeTo` is what reads a formula about the instance
inside it. The same file carries
`DescriptiveComplexity.Draw.boolEnv`, the two-element environment over any
relational vocabulary – the structure in which nothing holds – which is all
`uRulesDefinable_progOf` wants an environment for: naming the gate dispatch's
default tag, which is a nonemptiness the instance does not see.

`DescriptiveComplexity.Problems.Wide.RelExp` pays the price of that move, one
sentence at a time. A sentence about the instance's ordered vocabulary expanded
by a block is renamed into the extended one
(`DescriptiveComplexity.Draw.newBlockLHom`) and relativized to the mark, and then
says in the doubled universe exactly what it said in the instance
(`DescriptiveComplexity.Draw.realize_relOldBlock`): the marked part is a
substructure – the vocabularies are relational, so nothing has to be closed
under anything – and it *carries* the instance
(`DescriptiveComplexity.Draw.oldSubDLEquiv`), the reduct of its induced structure
along the renaming being what a block assignment restricts to. The assignment
travels by `DescriptiveComplexity.Draw.extAssign`, which holds of a tuple exactly
when every entry is marked and the entries' elements satisfy it; that is the
shape the *support* condition pins down
(`DescriptiveComplexity.Draw.extAssign_resAssign`), and it is what makes an
assignment over the doubled universe an assignment of the instance and nothing
more.

`DescriptiveComplexity.Problems.Wide.RelExpansion` puts the two together:
`DescriptiveComplexity.Draw.relExp` is the expansion relativized to the marked
part – the same block and the same expanded vocabulary, every sentence renamed
and relativized, every assignment required to be supported – so that a point of
it over the doubled universe is a point of the original expansion over the
instance. One tag is added, and only because `FirstOrder.Language.ExpExpansion`
demands its domain sentence be satisfiable at *every* structure, including ones
with no marked part at all, where a relativized sentence has nothing to be about:
the tag `none` is the point that exists exactly there
(`DescriptiveComplexity.Draw.noOldSentence`,
`DescriptiveComplexity.Draw.emptyBlocksSentence`), and over a doubled universe –
which always has a marked part – it contributes nothing. Discharging
`dom_nonempty` at an arbitrary structure is what
`DescriptiveComplexity.Draw.MarkPart` and `realize_relOldMark` are for: the marked
part is an instance in its own right wherever there is one.

`DescriptiveComplexity.Problems.Wide.RelExpMap` discharges the point of all
that: over a doubled universe the relativized expansion **is** the expansion over
the instance, points and relations alike
(`DescriptiveComplexity.Draw.relExpMapEquiv`). Three things make it work, and each
was arranged for it: a doubled universe always has a marked part, so the fallback
tag contributes no point (`not_domHolds_none`); a point's assignment is supported,
so it is the extension of a unique assignment of the instance
(`supported_of_domHolds`, `extAssign_resAssign`); and every sentence transports by
`realize_relOldBlock` – the domain sentence at one copy of the block, each
defining sentence at `n` copies, where extending commutes with replication on the
nose (`extAssign_replicateAssign`, which is `rfl`).

`DescriptiveComplexity.Problems.Wide.ShFinite` closes the one hypothesis the run
layer carries that was not yet a theorem. Every **site** type of the tower has a
`Finite` instance where it is defined, and so does every leaf kit's rule type;
what was missing is the tower's **shapes**, one instance per level
(`ChainSh`, `SeqSh`, `ElemSh`, `StageSh`, `TagSh`, `RoundSh`, `VarSh`, `EvalSh`,
`OuterSh`, then the concrete `KindSh` … `SFSh`). With them
`DescriptiveComplexity.Draw.Data.finite_RIx` is `Finite (Sigma …)`: **the rule
names of the emitted machine are finitely many**, which is what the run layer
assumed and what an interpretation needs of its tag type. Each instance has to be
*applied*, not searched for, one level up: a shape's argument has the type of a
site one level down, and instance search does not unfold the site definitions.

`DescriptiveComplexity.Problems.Wide.Reduce` chooses the reduction's constants
and writes the machine down. The base's extremes are
`DescriptiveComplexity.Draw.isBot_dblPt` and `isTop_dblPt` – the bottom of the
doubled universe is the marked copy of the instance's minimum, the top the junk
copy of its maximum. The dimension is `DescriptiveComplexity.Draw.srcDim`, one
coordinate of slack beyond the encoding budget and wide enough for a rule's
payload, and `srcData` is the record at it, with `srcData_dd0_lt`,
`srcData_payload_le` and `srcKIx`.

That payload bound is where the one subtlety of the packing sits. It is true
because no budget of a `Draw.Data` reads the dimension – but it is **not** `rfl`:
`DescriptiveComplexity.Draw.Data.nOf` and its relatives are defined by a match,
so their compiled matchers take the whole record as a parameter and two records
differing in the dimension are opaque to each other (`… .VarIx = … .VarIx` is
`rfl`; `… .nOf ≍ … .nOf` is not). What closes it is a congruence at every level –
`ofSource_nOf`, `ofSource_natOf`, `ofSource_kindDepth`/`kindReads`/`kindArgs`,
then `ofSource_ki`/`naDim`/`natMax`/`eDim`/`nfDim`/`ntgDim` by `Finset.sup_congr`
– each instantiated at a **constructor** of the scrutinee, where the matcher
reduces, giving `ofSource_ctlIx` and `ofSource_slotIx`.

On them `DescriptiveComplexity.Draw.dblWideInterp` is the machine written down
over the doubled universe – `drawInterp` at the packed record, the environment
`boolEnv`, and the accepting predicate `srcAccept` – and
`DescriptiveComplexity.Draw.wideInterp` is that composed with the doubling, an
interpretation of `Language.wide` in the instance's own ordered vocabulary whose
dimension is unchanged (the doubling is one-dimensional) and whose tags only gain
a Boolean per coordinate.

The correctness is then four equalities in a row.
`DescriptiveComplexity.Draw.srcReads` says the interpreted structure reads the
program's table; `dwideAcceptSpace_srcEnv_iff` runs the run layer at the
environment `srcEnv` – the doubled universe with the marked copy of the
instance's minimum and the junk copy of its maximum as designated elements, and
with the expanded universe's order *chosen* to be `encOrder`, which makes the run
layer's `hordP` an `Iff.rfl`; `wideInterpEquiv` carries that back along the
composition; and `relExpMapEquiv` plus the source problem's own
`iso_invariant` turn the fixed point into the source. The last two are the whole
of `DescriptiveComplexity.Draw.wideProblem_wideInterp_iff`, which never asks
*what* the machine decides – three isomorphisms, one wide problem, one source
problem – so `DescriptiveComplexity.Draw.dwideAcceptSpace_wideInterp_iff` is that
theorem with the run layer's answer supplied, and with it
`DescriptiveComplexity.dwideAcceptSpace_EXPSPACE_complete` and
`DescriptiveComplexity.wideAcceptSpace_EXPSPACE_complete`.

`DescriptiveComplexity.Problems.Wide.DrawTracks` names the coordinates. A payload
is a function of a finite **slot** type (`DescriptiveComplexity.Draw.slotPl`, read
back by `DescriptiveComplexity.Draw.unslot`) and a slot carrying a bit holds one of
the two designated elements (`DescriptiveComplexity.Draw.bitVal`,
`DescriptiveComplexity.Draw.bitVal_iff`), so a program never counts a coordinate
and the distinctness obligations of the table are statements about named fields.

`DescriptiveComplexity.Problems.Wide.DrawRules` writes a program rule by rule, and
splits the slots in the one way that works. A transition's data must carry **both**
payloads – the state's and the symbol's – because neither determines the other:
the symbol under the head cannot name the register the head is on, the registers
being anonymous, and the state cannot name the symbol it is about to read. So the
slots are `Q ⊕ W`, the **control** slots a state uses and the **track** slots a
symbol uses (`DescriptiveComplexity.Draw.stVec`,
`DescriptiveComplexity.Draw.syVec`), and two things follow. Firing a rule needs no
payload arithmetic – the data is the pointer and the tracks side by side, so
`DescriptiveComplexity.Draw.Prog.fire_left` and its rightward twin hand a program
its six attributes at the elements it named. And determinism becomes a check on
*rules*: the two payloads occupy disjoint coordinates, so
`DescriptiveComplexity.Draw.Table.Sep` reduces to
`DescriptiveComplexity.Draw.Prog.sep_of` – two rules that fire on the same symbol
from the same state are the same rule.

The same file carries the tape a register pass runs over,
`DescriptiveComplexity.Draw.Prog.trackTapeAt`: the track slot being walked holds the
digit of the track at this cell and the others hold whatever the program keeps
there. Its coherence condition – changing the track at one element moves the tape
only at that element's cell – is
`DescriptiveComplexity.Draw.Prog.trackTape_coh`, proved once for every program and
every alphabet, so the three passes are entered with nothing to discharge.

`DescriptiveComplexity.Problems.Wide.DrawPass` runs the three register passes off
the program's rules. What a program owes is
`DescriptiveComplexity.Draw.Prog.HasLeft` – *in this phase, at this pointer,
reading these tracks, a rule of mine goes to that phase and that pointer, writes
those tracks and moves left* – and nothing else: the symbols are computed for it,
so it never sees `DescriptiveComplexity.regBit`, never writes a tape equation and
never mentions `FirstOrder.Language.wide`. With four such families
`DescriptiveComplexity.Draw.Prog.reaches_fileIncr` is the mirror increment, and with
four `DescriptiveComplexity.Draw.Prog.reaches_fileTestG`
(`DescriptiveComplexity.Problems.Wide.DrawSub`) asks one question of every
register – a question the *tracks* decide – and brings the verdict back in the
phase. One track slot carries *this cell is a register*, which is both what
tells the acting rules from the walking one and what their separation argument
is discharged from. The background of the walked track is **element-valued**,
so the tape can carry the name marks; the mark hypotheses are `bitVal`
equations.

The increment comes in two forms, and the difference is the one thing the
anonymity of the registers costs.
`DescriptiveComplexity.Draw.Prog.reaches_fileIncrBlk` stops in the phase of the **block**
that carried – which is what the fold of `DescriptiveComplexity.Problems.Wide.Fold`
has to know, and which the machine learns not by naming the register (it cannot: a
state's payload holds elements of the source structure) but by reading the block
off that cell's *mark*, one stopping rule per block.
`DescriptiveComplexity.Draw.Prog.reaches_fileIncr` is the single-block case, the register
mark serving as its own indicator, and is the form every use that only has to
*move* an address takes.

Between passes the program writes its own data, and that is one step:
`DescriptiveComplexity.Draw.Prog.step_move` and its leftward twin change the
**background** at the cell the head leaves while carrying the track along
untouched, so a step and a register pass compose without either knowing what the
other keeps on the tape.

Navigation is there too, and it is two theorems rather than four:
`DescriptiveComplexity.Draw.Prog.reaches_fileToMark` and its downward twin get the head
to a register the caller has *marked* – the two ends of the file, which are the
only cells that have to be recognized on sight – taking the target as a parameter
rather than naming it; and `DescriptiveComplexity.Draw.Prog.reaches_seek` and
`reaches_seekBack` walk the working area to the nearest cell carrying a given
slot, arriving with the promise that nothing passed carried it, which is where the
extremum a program cannot name is taken.

On top of the pass layer sit the pieces the EXPSPACE program's atom
subroutines consume. `DescriptiveComplexity.Problems.Wide.DrawScan` scans to a
cell recognized by an arbitrary guard on its tracks
(`DescriptiveComplexity.Draw.Prog.reaches_toCell` and its three variants) – the
navigation to a register cell whose *name marks* match a tuple held in the
control. `DescriptiveComplexity.Problems.Wide.DrawEnc` encodes the points of an
exponential expansion injectively as block values
(`DescriptiveComplexity.Draw.encPt`, one membership question per bit of the
assignment, `DescriptiveComplexity.Draw.mem_encPt_asg`), and
`DescriptiveComplexity.Problems.Wide.DrawRel` moves an alternating quantifier
prefix from the points to the block values a register enumerates, by gating the
matrix polarity-correctly (`DescriptiveComplexity.Draw.altQuantFrom_gateMat`).
`DescriptiveComplexity.Problems.Wide.DrawInner` restates the fold–increment join
of `DescriptiveComplexity.Problems.Wide.Bridge` on a *final segment* of the
blocks – the `Kin` half of the argument tags, where the inner loop's register
enumerates the prefix valuations – and adds the control-scale fold rules along
a tuple successor; `DescriptiveComplexity.Problems.Wide.DrawLoop` supplies the
induction the control loops run on
(`DescriptiveComplexity.Draw.reflTransGen_of_tupLoop`).

`DescriptiveComplexity.Problems.Wide.DrawSpec` states what the program's inner
loop computes, with no machine in sight: one step of the iteration at a tuple
of points is the gated prefix over block values
(`DescriptiveComplexity.Draw.StepDef.next_iff_gateMat`), the step formula put
once into prefix normal form with its free variables re-bound first
(`DescriptiveComplexity.Draw.PrenexPack`). And
`DescriptiveComplexity.Problems.Wide.DrawAddr` fixes the argument blocks –
outer arguments first, inner prefix variables last, `K := Fin ko ⊕ₗ Fin ki` –
proves the inner tags a final segment of the tag order
(`DescriptiveComplexity.Draw.kinSeg`, the hypothesis pack of the inner loop's
fold rules), and writes the stage dictionary: the content of a stage track at
an address (`DescriptiveComplexity.Draw.trackOf`), reading only the blocks below
the variable's arity, `False` off the encodings, so the all-blank initial tape
is exactly stage `0`. Finally, `DescriptiveComplexity.Problems.Wide.DrawOrd` is
the order the reduction puts on the points: `DescriptiveComplexity.PFPDefinable`
quantifies over every linear order on the expanded universe, so the reduction
chooses the pullback of the binary block-value order along the encoding
(`DescriptiveComplexity.Draw.encOrder`), making an order atom exactly the
comparison of two encodings in the machine's own reading
(`DescriptiveComplexity.Draw.encOrder_le_iff`,
`DescriptiveComplexity.Draw.wmSetLe_iff_setLe`).

The first two concrete pieces of the program are in place.
`DescriptiveComplexity.Problems.Wide.DrawGate` decomposes the gate the way the
machine checks it (`DescriptiveComplexity.Draw.isEnc_iff_parts`: a tag witness,
well-shapedness of every member, the domain sentence at the decoded
assignment `DescriptiveComplexity.Draw.decRho`), and
`DescriptiveComplexity.Problems.Wide.DrawSlots` fixes the track and control
slot inventories (`DescriptiveComplexity.Draw.Slot`,
`DescriptiveComplexity.Draw.Ctl`) and the mark of every register cell
(`DescriptiveComplexity.Draw.slotMark`) – including the budgeted register
naming, whose uniqueness among padded cells
(`DescriptiveComplexity.Draw.eq_of_slotMark_name`) is what stops the
navigation-by-name scans at exactly one cell.
`DescriptiveComplexity.Problems.Wide.DrawSub` holds two corrections the
interface needed once its discharge was attempted: a single-cell write is a
navigation plus **one step**
(`DescriptiveComplexity.Draw.Prog.step_writeCell`), not a pass – a pass's rules
compute their written symbol from the tracks they read, which say nothing
about an independently quantified cell – and a file test must be decided by
the tracks (`DescriptiveComplexity.Draw.Prog.reaches_fileTestG`, the question a
predicate of the symbol, tied to the per-cell question by one compatibility
hypothesis). And `DescriptiveComplexity.Problems.Wide.DrawInit` joins the two
ends of a run to the pass-layer presentation: the initial tape *is* the
presentation walking any clear track with the empty track
(`DescriptiveComplexity.Draw.Prog.trackTape_initBack`, the background
`DescriptiveComplexity.Draw.Prog.initBack` being the marks over the blank), so
a program starts from `DescriptiveComplexity.Draw.Prog.isInit_prog` with no
initialization sweep, and
`DescriptiveComplexity.Draw.Prog.dwideAcceptSpace_prog` turns an accepting run
plus the separation argument into a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`.

`DescriptiveComplexity.Problems.Wide.DrawAdv` is the first composite, and the
round every sweep repeats: `DescriptiveComplexity.Draw.Prog.reaches_fileAdvance`
moves the working-cell marker one address with the mirror in tow – two marker
steps, the scan to the file top, the **bounce** turnaround (the scan cannot
overshoot the maximal cell, so entering the downward pass costs two steps
changing phase), the mirror increment, and the scan back to the marker. Its
hypotheses are the rule families of the six phases it visits and the slot
equations of its backgrounds, which is the evidence the layer's interfaces are
the right ones: the walking hypotheses had to be **cell-coupled and bounded to
the register file** – a pass whose walking rules covered every cell could
never be followed by anything, the unique deterministic continuation being to
walk on for ever – and the scans now hand their step suppliers the fact that a
stopping cell is still ahead, which is where those bounds come from.

`DescriptiveComplexity.Problems.Wide.DrawSweep` is the two shapes of a *plain*
sweep – one step per address, no register visits:
`DescriptiveComplexity.Draw.Prog.reaches_flagSweep` asks one question per cell
with the verdict in the phase (`DescriptiveComplexity.sweepState` – COMPARE),
and `DescriptiveComplexity.Draw.Prog.reaches_writeSweep` rewrites each cell
once, the background a function of the frontier (COPY). Their rules are
cell-coupled and bounded to the stretch; the program's device for the bound is
a permanent end marker planted at the top of the logical interval once, at
startup, a cell of the working area being otherwise unrecognizable. And
`DescriptiveComplexity.Problems.Wide.DrawTrip` factors the itinerary of every
visit to the register file – scan up, bounce, one pass down, scan back to the
marker – into `DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip`, the middle
pass a hypothesis: the seek loop, the test rounds of a random access and the
gate checks are all this composite around their respective passes.

On top of them, `DescriptiveComplexity.Problems.Wide.DrawSeek` is **random
access**: `DescriptiveComplexity.Draw.Prog.reaches_fileSeekTo` carries the
working-cell marker from the empty address to any target strictly below the
register file – rounds of a turnaround step, a round trip around the file test
*mirror = target*, and an ADVANCE, driven by
`DescriptiveComplexity.reaches_of_wideRounds`, the mirror invariant holding by
construction (the mirror track *is* the marker's address, the same
predicate). This is what evaluates a stage atom at a computed tuple of
points. And `DescriptiveComplexity.Problems.Wide.DrawRead` reads or writes
**one named register bit** – the leaves of the element loops:
`DescriptiveComplexity.Draw.Prog.reaches_readBit_pos`/`_neg` scan up to the
cell the name guard identifies, take one branching step, and return to the
marker; `DescriptiveComplexity.Draw.Prog.reaches_writeBit` is the same trip
with the walked track updated at that cell.

One design correction closes the semantic layer
(`DescriptiveComplexity.Problems.Wide.DrawAcc`): the sweep's control cannot
carry the fold *values* – at a carry they are not closed under the update –
so it carries the per-level **contributions**
(`DescriptiveComplexity.Draw.accCVal`), from which every fold value is a finite
Boolean chain (`DescriptiveComplexity.Draw.foldFrom_eq_accCVal`); the three
update rules along an increment are
`DescriptiveComplexity.Draw.accCVal_congr_above`,
`DescriptiveComplexity.Draw.accCVal_carry` and
`DescriptiveComplexity.Draw.accCVal_reset`.

Finally, `DescriptiveComplexity.Problems.Wide.DrawKit` is how the program
instantiates its subroutines: **composite kits** – per composite shape, a
phase inductive, a rule inductive with concrete guards, the rules function at
a phase embedding, an in-shape separation lemma, and a discharge showing any
program containing the kit's rules satisfies the composite's run theorem.
Global determinism reduces to in-shape separation plus injective, disjoint
phase embeddings. `DescriptiveComplexity.Draw.ReadKit` – the named-bit read –
is the template (`DescriptiveComplexity.Draw.ReadKit.rule`,
`DescriptiveComplexity.Draw.ReadKit.sep`,
`DescriptiveComplexity.Draw.ReadKit.reaches_pos`/`_neg`), and the full
inventory covers every composite: `DescriptiveComplexity.Draw.WriteKit` (the
named-bit write), `DescriptiveComplexity.Draw.TestKit` (the file test in its
round trip, `DescriptiveComplexity.Problems.Wide.DrawTripKits`),
`DescriptiveComplexity.Draw.ClearKit` and `DescriptiveComplexity.Draw.CopyKit`
(the whole-track writes), `DescriptiveComplexity.Draw.IncrKit` (the
block-indexed increment, landing in the phase of the block that carried),
`DescriptiveComplexity.Draw.FlagSweepKit` and
`DescriptiveComplexity.Draw.WriteSweepKit` (the plain sweeps, bounded by the
`ltp` end marker), `DescriptiveComplexity.Draw.AdvKit` (one round of a sweep)
and `DescriptiveComplexity.Draw.SeekKit` (the whole random-access loop,
seventeen rule families). Their disjoint guards forced three further
hardenings of the pass layer, each making a demanded rule and a supplyable
guard coincide: the return scans of the verdict phases are cell-coupled
(`DescriptiveComplexity.Draw.Prog.reaches_toCellBackC`, threaded through
`DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip`), the block-indexed
increment's stopping rule takes a one-hot clause
(`DescriptiveComplexity.Draw.Prog.reaches_fileIncrBlk`), and the seek's turnaround
and walking hypotheses are stated at exactly the guards' slot conditions
(`DescriptiveComplexity.Draw.Prog.reaches_fileSeekTo`). The program itself is then
**assembled from call sites** (`DescriptiveComplexity.Problems.Wide.DrawAsm`):
`DescriptiveComplexity.Draw.Assembly` packages per-site rule shapes with an
ownership map from phases to sites, `DescriptiveComplexity.Draw.Assembly.prog`
is the program whose rule names are the sigma, and
`DescriptiveComplexity.Draw.Assembly.sep` its separation, via
`DescriptiveComplexity.Draw.sep_sigma` – so each call site is built and
checked in its own file, its in-shape separation the kit's `sep` plus its
`exit_disjoint`. The per-atom call sites are indexed by the classified atoms
of the step matrices (`DescriptiveComplexity.Problems.Wide.DrawAtoms`):
`DescriptiveComplexity.Draw.MatAtom` is the kind – equality, order, expansion
relation, stage atom – `DescriptiveComplexity.Draw.matAtom?` reads it off the
syntax (total on the atoms `DescriptiveComplexity.Draw.qfAtoms` emits), and
`DescriptiveComplexity.Draw.realize_iff_qfValue_holds` is the semantic
capstone: a quantifier-free matrix realizes as its Boolean function at the
kinds' readings, which is what the machine computes once its per-atom
subroutines have filled the verdict slots. And
`DescriptiveComplexity.Draw.Data`
(`DescriptiveComplexity.Problems.Wide.DrawData`) bundles the reduction's data
– the expansion, the definition, the prenex packs, the encoding layout with
its coordinate budget – with the derived dimensions the inventories are
sized by (`ko`, `ki`, the per-variable atom lists and their classified
kinds), so every site file takes one record and nothing else. The kit
*instances* at the concrete slots are in
`DescriptiveComplexity.Problems.Wide.DrawSites`: the two plain sweeps, the
seek, the advance, the block-indexed VAL increment, the clears and copies of
the registers, the pattern write of startup
(`DescriptiveComplexity.Draw.MapKit`, wrapping the generalizing composite
`DescriptiveComplexity.Draw.Prog.reaches_fileMapTrack`), the VAL-exhausted file
test, and the navigation-by-name read/write trips with their
`DescriptiveComplexity.Draw.Data.nameG` guard. The one itinerary running
*down* the working area – resetting the marker to the bottom before a random
access – is `DescriptiveComplexity.Draw.Prog.reaches_reset` with its
`DescriptiveComplexity.Draw.ResetKit`
(`DescriptiveComplexity.Problems.Wide.DrawReset`), designed to erase and step
*right* so the empty address needs no special case. Finally,
`DescriptiveComplexity.Draw.TapeSt`
(`DescriptiveComplexity.Problems.Wide.DrawBack`) is the machine's mutable
state – registers per element, stage tracks and markers per cell – and
`DescriptiveComplexity.Draw.Data.back` its presentation as the background
family the pass layer walks, with the slot equations every kit discharge
takes proved once over it – including the one that says what a symbol does
*not* depend on: the four register slots read
`DescriptiveComplexity.bitAtOf`, set at a register cell alone, so off the
register file the background is blind to the mirror, the target, the saved
mirror and VAL alike (`DescriptiveComplexity.Draw.Data.back_congr_off_reg`).
Which cells those are is the caller's: `back` reads the permanent marks at
whatever family of cells it is given, so a program that *builds* its own file
runs the same background at it. That phase is
`DescriptiveComplexity.Draw.Prog.reachesIn_buildFile`
(`DescriptiveComplexity.Problems.Wide.DrawBuild`): a sweep of the file's stretch
that turns the blank background into `back`, the mark of each cell written from
the **pointer**, which holds the element and moves along by the order successor
(`DescriptiveComplexity.Draw.Prog.reachesIn_installSweep`). The sweep is the
stretch and no more, because off the file the background to install is already
the blank (`DescriptiveComplexity.Draw.Data.back_of_not_reg`). The same file
holds the other opening phase, `DescriptiveComplexity.Draw.Prog.reachesIn_guessTracks`:
the same sweep with the background on both sides, the stage tracks the only
thing that changes (`DescriptiveComplexity.Draw.Data.back_old_congr`) and the
assignment a *parameter* – which is what makes it a guess, the run existing for
every certificate. What those two phases sit inside is
`DescriptiveComplexity.Draw.NexPh`
(`DescriptiveComplexity.Problems.Wide.NexOuter`), the clocked program's outer
layer: the file-laying sweep, a walk home, the guess, a walk home, the
evaluation, and the accepting phase, with the evaluation's rules and the two
sweeps' writes as parameters. It does not separate in-shape at the guess and must
not – that is the program's whole nondeterminism – so what it proves instead is
`DescriptiveComplexity.Draw.Data.nexSep_postGuess`, separation at the phases no
rule returns to the guess from
(`DescriptiveComplexity.Draw.Data.postGuess_nexRule`). What turns that into
determinism where it is used is
`DescriptiveComplexity.Draw.Table.uniqueFrom_of_sepOn`
(`DescriptiveComplexity.Problems.Wide.NexDet`), by way of
`DescriptiveComplexity.Draw.Table.SepOn` and
`DescriptiveComplexity.TMData.uniqueFrom_of_invariant`: the machine is unique
from any configuration whose phase the program separates at, which is all the
read-off lemmas of `DescriptiveComplexity.Problems.Machine.DetRun` ask for. That
blindness is
what separates the machine's *threaded* states from the *unthreaded* ones
the semantics is stated at: a VAL round rewrites SAV and
TARGET and nothing else
(`DescriptiveComplexity.Draw.Data.ScratchEq`,
`DescriptiveComplexity.Draw.Data.roundEndSt_eq`), and every control the
machinery computes is blind to that difference – the generated families
read their background at the working cell alone
(`DescriptiveComplexity.Draw.elemFam_congr_rest` and its two siblings),
each atom kind's loop and exit follow
(`DescriptiveComplexity.Draw.Data.kindExitCtl_congr_scratch`), and so do
the matrix and the round
(`DescriptiveComplexity.Draw.Data.matFs_congr_scratch`,
`DescriptiveComplexity.Draw.Data.matFsT_eq_matFs`,
`DescriptiveComplexity.Draw.Data.igFs_congr_scratch`,
`DescriptiveComplexity.Draw.Data.roundCtl_congr_scratch`,
`DescriptiveComplexity.Draw.Data.roundCtlT_eq_roundCtl`), and with them the
VAL loop and one position's leg
(`DescriptiveComplexity.Draw.Data.varFXT_eq_roundFX`,
`DescriptiveComplexity.Draw.Data.varFMT_eq_varFM`,
`DescriptiveComplexity.Draw.Data.legCtlT_eq_legCtl`, and at the output
variable `outCtlT_eq_outCtl`, which is what lets `outLeg_run_thread` – the
out machinery's run with `hsav`/`htgt` dropped, since a sweep leaves the two
scratch registers wherever the last position's evaluation left them – ask
for its accepting verdict in the unthreaded form the semantics reads).
What the threading
*can* change is the semantic pack – a family indexed by the scratch
registers may pick different points at different registers – so the loop's
bridge is stated at a pack that is one pack at the round state transported
(`DescriptiveComplexity.Draw.Data.semCastT`, closed by
`DescriptiveComplexity.Draw.Data.kindSemCast_triple`: the pack leaves the
round state, travels to the round's own state and to the state its matrix
threads, and comes back). A gated position's own pack is of that shape
(`DescriptiveComplexity.Draw.Data.gatedSem_eq_semCastT`, its points being
`isEnc_of_gatedAt`'s choices – a function of the mirror alone), so the
branched leg's stage bit is the verdict the semantics reads
(`DescriptiveComplexity.Draw.Data.legBitB_gatedSem`), which is what
`DescriptiveComplexity.Draw.Data.new_last_next_at` – the per-position form
of `new_last_next`, gating being per variable – consumes; and gating at a
position *is* «the blocks below that variable's arity encode points», both
directions
(`DescriptiveComplexity.Draw.Data.isEnc_of_gatedAt`,
`DescriptiveComplexity.Draw.Data.gatedAt_of_isEnc`). With those, the branched spine's
own reading at one address is `DescriptiveComplexity.Draw.Data.new_last_trackOf_B`
– per variable, nothing assumed of the other variables' blocks – and along a
whole sweep `DescriptiveComplexity.Draw.Data.sweep_new_trackOf`: below the
address reached every stage track holds the dictionary of the *next* stage,
elsewhere what the sweep started with. One scale up again, a stage's `old`
tracks hold that stage of the iteration
(`DescriptiveComplexity.Draw.Data.stageSt_old`, by induction through the
copy-back), so the machine's convergence test is exactly the semantic one:
`DescriptiveComplexity.Draw.Data.stageEnd_conv_iff` – *this stage and the
next agree at every address below the end marker* – which is what
`DescriptiveComplexity.Draw.Data.reaches_main`'s `hconv`/`hnotconv` ask
for, with `DescriptiveComplexity.StepDef.partStage` on both sides. And the dictionary is
**faithful**: `DescriptiveComplexity.Draw.assignment_ext_of_trackOf` – two
assignments whose tracks agree over a family of addresses carrying every
tuple's own (`DescriptiveComplexity.Draw.tupAddr`) are equal – so the test
decides the *stages*, not merely their readings. A tuple's address lies in
the logical interval because it has no non-argument block, and *strictly*
below its top because the top's blocks are full while an encoding's never
are – every member of one carries a one-hot code, so the all-`zero` tuple is
not one (`DescriptiveComplexity.Draw.not_encPt_zeroTup`,
`DescriptiveComplexity.Draw.wmSetLt_tupAddr_logicalTop`; at a **nullary**
variable the address is the empty one and what places it is the interval's
nonemptiness, the two cases joined in
`DescriptiveComplexity.Draw.wmSetLt_tupAddr_logicalTop'`). And the induction
starts on a blank tape, which is stage `0` because the empty stage writes an
empty track (`DescriptiveComplexity.Draw.Data.old_trackOf_zero_of_blank`).
With that,
`DescriptiveComplexity.Draw.Data.stageEnd_conv_of_eq` and
`stageEnd_not_conv_of_ne` are the loop's two remaining hypotheses at the
*first* stable stage, which `DescriptiveComplexity.StepDef.exists_least_stable`
supplies from convergence – so what the machine's rounds test is the stage
sequence itself. The invariant is stated *over the logical
interval* and nowhere else, and that restriction is not a convenience:
outside it an address may read a stage all the same – a tuple's address with
one `ctrl` cell added lies above the top, non-argument tags being the most
significant – while the machine's tracks there stay blank. So every
dictionary hypothesis of the layer, from
`DescriptiveComplexity.Draw.Data.old_trackOf_stageTgtD` up, is an
equivalence at the addresses that are *read* rather than an equation of
tracks; what each site owes in exchange is that the address it reads lies in
the interval, and for a stage atom that address is
`DescriptiveComplexity.Draw.Data.stageTgtD`, which **is** in it
(`DescriptiveComplexity.Draw.Data.wmSetLt_stageTgtD_logicalTop`): every
cell it holds was written by a copy round at that round's destination, so it
carries argument cells alone (`stageTgtD_arg`) and each of them is a padded
one (`stageTgtD_isPad`) – which is the general
`DescriptiveComplexity.Draw.wmSetLt_logicalTop_of_isPad`, an address a program
*builds* out of padded cells being strictly below a top whose blocks are
full. Unlike the address a program *reads* from a register, this one is
placed with no hypothesis on the machine's state at all.

From the *initial* configuration the run reaches MAIN's starting one by
`DescriptiveComplexity.Draw.Data.reaches_evalEntry`: the startup, then two
steps – `step_clearMir1_exit`, which leaves the marker to the right, and
`step_chk0_back`, the checkpoint's `stay` rule walking back onto it – with
the two presentations of the tape one term
(`DescriptiveComplexity.Draw.Data.trackTape_val_eq_mir`). The state it
arrives with is `startupSt`, which is what `reaches_mainB` asks of its `st₀`,
and whose `ltp` field is what pins the end marker of the whole run.

With that the **forward half of the reduction is assembled**
(`DescriptiveComplexity.Problems.Wide.DrawYes`): a partial fixed point that
holds makes the emitted instance a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`
(`DescriptiveComplexity.Draw.Data.dwideAcceptSpace_of_pfpHolds`), the two
promises coming for free – well-formedness from the layout, determinism from
`prog_sep` – and the run being `reaches_evalEntry`, `reaches_mainB` and the
output leg in sequence
(`DescriptiveComplexity.Draw.Data.reaches_outVerdict`). Everything semantic the
loop asks for is a choice made once here: the end marker is
`DescriptiveComplexity.Draw.logicalTop`, which is *what the startup writes*
(`DescriptiveComplexity.Draw.Data.tgtTopSt_tgt` – a tag has a block exactly
when it is an argument tag), and which lies below every register because the
least element of the universe is not an argument
(`tagBlk_eq_none_of_least`, `wmSetLt_wmSeg_of_not_bot`); the VAL enumeration
is `exists_valEnum`'s chain over `Fin (n + 1)`, whose bottom and top are `0`
and `Fin.last n`; and the stage the machine stops at is the *first stable*
one (`DescriptiveComplexity.StepDef.exists_least_stable`), whose two sides
are `stageEnd_conv_of_eq` and `stageEnd_not_conv_of_ne`. The output leg
(`DescriptiveComplexity.Draw.Data.outLeg_verdict`) is the one place a
verdict is *read*: the output variable is nullary, so every hypothesis the
machinery asks about the working address's blocks is a function on `Fin 0`,
its pack is `passSem` transported by `semCastT`, and what is left is
`accVerdict_out` – the machinery's bit at the empty address **is** the output
sentence at the stage the tracks hold.

The **other half is rejection**, and it costs no invariant over the program's
rules. The emitted machine is deterministic, so the configurations reachable
from its initial one are linearly ordered
(`DescriptiveComplexity.TMData.reach_total`), and it is enough to exhibit one
run of the machine's own choosing that ends badly – provided accepting
configurations are *stuck*. They are
(`DescriptiveComplexity.Draw.Data.stuck_acc`), and the fact is one the
assembly already carries: every rule fires from a phase its own site owns
(`DescriptiveComplexity.Draw.Assembly.howner`), the accepting phase's site
contributes no rules at all (`OuterSh … .accept` is `Empty`), so no rule has
it as a source (`DescriptiveComplexity.Draw.Assembly.srcPh_ne_of_isEmpty`,
`DescriptiveComplexity.Draw.Data.srcPh_ne_acceptP`) and the case analysis is
on the *tag* of a transition rather than one case per rule. With it,
`DescriptiveComplexity.Problems.Machine.DetRun` supplies both shapes of
rejection: a run that ends badly
(`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead`) and one that
never ends (`DescriptiveComplexity.TMData.not_acceptsSpace_of_chain` – each
link of an unbounded chain costs at least one step, while a stuck
configuration is reached in one fixed number of them, so a *diverging* fixed
point is a correct rejection with no clock anywhere).

With that the **converging case is settled both ways at once**
(`DescriptiveComplexity.Problems.Wide.DrawNo`). The output leg does not need
its verdict as a hypothesis: it lands in the accepting phase whatever the
verdict, and what the verdict decides is the *bit* the exit writes at the
marker (`DescriptiveComplexity.Draw.Data.outStA`,
`DescriptiveComplexity.Draw.Data.outLeg_run_verdict` – the current
`outLeg_run_thread` is its idempotent special case). So
`DescriptiveComplexity.Draw.Data.reaches_outVerdict` asks only that the
iteration *converge* and delivers one run with an **equivalence** at its end:
the machine's accepting predicate at the state it stops in holds exactly when
the partial fixed point does. One direction is
`DescriptiveComplexity.Draw.Data.dwideAcceptSpace_of_pfpHolds`; the other,
with the dead end, is
`DescriptiveComplexity.Draw.Data.not_dwideAcceptSpace_of_converges`.

A **diverging** iteration is the remaining case, and the machine's lack of a
clock is what makes it correct rather than a bug: when no stage is stable
every convergence test fails, so MAIN keeps sweeping and its run passes an
unbounded chain of stage entries
(`DescriptiveComplexity.Draw.Data.transGen_stageB` – each link at least one
step, because the sweep leaves the head at the end-marked address and not at
the empty one). A chain like that reaches no halting configuration at all
(`DescriptiveComplexity.TMData.not_acceptsSpace_of_chain`), whence
`DescriptiveComplexity.Draw.Data.not_dwideAcceptSpace_of_diverges`.

The three cases together are the **correctness of the reduction**,
`DescriptiveComplexity.Draw.Data.dwideAcceptSpace_iff_pfpHolds`: the emitted
instance is a yes-instance exactly when the partial fixed point holds. No
induction over the program's rules appears anywhere in it – the machine's
determinism does that work, and the only side condition is that its accepting
phase is a dead end.

The **transfer to the nondeterministic problem** costs nothing and is written
once (`DescriptiveComplexity.Problems.Wide.Det`): hardness travels forward
along reductions, so proving the *deterministic* problem hard – which is what
a program with a unique run naturally gives – hands
`DescriptiveComplexity.WideAcceptSpace` its own hardness through
`DescriptiveComplexity.dwideAcceptSpace_fo_reduction_wideAcceptSpace`. The
reduction is the identity interpretation with its accepting states guarded by
the determinism sentence (`DescriptiveComplexity.SpaceTM.detF` read at
`FirstOrder.Language.wide`'s symbols, the very sentence the polynomial-level
bridge uses): a deterministic instance is copied verbatim, so the two are
isomorphic; a nondeterministic one loses every accepting state, so both sides
are no-instances. This is `DescriptiveComplexity.Problems.Machine.SpaceDet` one
exponent up, and it is why `PSPACE = NPSPACE` needs no machine-side Savitch
here either.

The **outer program is assembled**
(`DescriptiveComplexity.Problems.Wide.DrawOuter`): the program factors as an
outer loop – startup, the sweep's advance, the convergence test, the
copy-back, the output dispatch – around a per-address **evaluation** that
stays abstract (its phase type, site family and boundary rules are
parameters, the same move `Prog.reaches_fileRoundTrip` makes for the middle of a
trip). `DescriptiveComplexity.Draw.OuterPh`/`OuterSite`/`OuterSh` are the
phases, sites and rule shapes; `DescriptiveComplexity.Draw.Data.outerRule`
the rules (each site its kit's rules plus its exit rules, a sweep's first
step folded into the rule that enters it);
`DescriptiveComplexity.Draw.Data.outerSep` the in-shape separation, one
case per site from the kits' `sep` and `exit_disjoint`; and
`DescriptiveComplexity.Draw.Data.outerAsm` the
`DescriptiveComplexity.Draw.Assembly`. The evaluation itself factors once
more (`DescriptiveComplexity.Problems.Wide.DrawEval`): a **spine** of
checkpoints, one per variable position
(`DescriptiveComplexity.Draw.EvalPh`/`EvalSite`/`EvalSh`,
`DescriptiveComplexity.Draw.Data.evalRule`/`evalSep`/`evalHosrc`), each
walking back to the marker and dispatching into that variable's machinery –
the last into the outer boundary pair, erasing the marker towards the
advance or the post-sweep reset – around per-variable sub-machineries that
stay abstract in turn. One variable's machinery
(`DescriptiveComplexity.Problems.Wide.DrawVar`) is the next layer: the gates
(abstract, verdict in a control flag), the junk path writing `False`
directly, and the VAL loop – clear, matrix (abstract), exhaustion test,
block-indexed increment – with the accumulator folds as `dstSt`
*parameters* of the dispatching rules
(`DescriptiveComplexity.Draw.Data.varRule`,
`DescriptiveComplexity.Draw.Data.varSep`), since separation never reads
`dstSt`; their content is fixed with the runs. The recurring
checkpoint-around-stages pattern is a **combinator**
(`DescriptiveComplexity.Problems.Wide.DrawChain`:
`DescriptiveComplexity.Draw.chainRule`/`chainSep`/`chainHosrc`, dispatches
given as source-phase-less `DescriptiveComplexity.Draw.PreRule` descriptors,
so loops cost nothing), and the **tuple loop** – the stage atoms' bit-by-bit
block copy, a read trip storing its verdict into the control and a write
trip reading it back, around the loop-variable enumeration – is its first
client (`DescriptiveComplexity.Problems.Wide.DrawTuple`:
`DescriptiveComplexity.Draw.tupleRule`/`tupleSep`). The read and write trips
gained a stay rule at their start phase for it: every kit is now enterable
by the standard rightward dispatch off the marker. On top of them, the
**stage atom's machinery** – the random access, the largest atom
subroutine – is complete
(`DescriptiveComplexity.Problems.Wide.DrawStageAtom`:
`DescriptiveComplexity.Draw.Data.stageRule`/`stageSep`): save the mirror,
clear and build the target by per-argument tuple loops chained head to
tail, reset–clear–seek out, read the stage bit under the head in the seek's
verdict exits, restore, and reset–clear–seek home. The remaining atom
subroutines are all one shape, the **element loop**
(`DescriptiveComplexity.Problems.Wide.DrawElem`:
`DescriptiveComplexity.Draw.elemRule`/`elemSep` – leaf reads chained head to
tail, the folds in the checkpoints' `dstSt` parameters, the base-structure
atoms of a leaf evaluated in guards, which see the control), wrapped for
the tag-dependent sentences in the **tag-branched** form
(`DescriptiveComplexity.Problems.Wide.DrawTagged`:
`DescriptiveComplexity.Draw.tagRule`/`tagSep` – witness reads, an n-ary
branch checkpoint whose dispatches the decoding makes exclusive, one loop
per tag tuple): the expansion atoms at their arity, the domain gates at
one. And the **sequencer**
(`DescriptiveComplexity.Problems.Wide.DrawSeq`:
`DescriptiveComplexity.Draw.seqRule`/`seqSep`) chains heterogeneous stages –
the matrix's kind-dependent atom machineries, the gates' per-block ones –
behind checkpoints, so the machinery *vocabulary* of the program is now
complete: what remains is instantiation and the runs. The instantiation has
begun: `DescriptiveComplexity.Problems.Wide.DrawRepAtoms` classifies the
atoms of the defining sentences' replicated-block language – base-vocabulary
kinds are guards, the replicated-block kind the read leaves – with the same
capstone (`DescriptiveComplexity.Draw.realize_iff_qfValue_blkHolds`), and
`DescriptiveComplexity.Problems.Wide.DrawTower` assembles the **phase tower**:
per-kind machinery types indexed by the `DescriptiveComplexity.Draw.MatAtom`
itself (so everything reduces per constructor, the stuck `kindOf`
application confined to the last step), the matrix and gates as sequences,
one variable's machinery, the spine over the enumerated variables, and
`DescriptiveComplexity.Draw.Data.PF` – the program's phase type – with
its site mirror, the owner maps down the tower
(`DescriptiveComplexity.Draw.Data.sfOwn`) and finiteness throughout. The
rule tower has begun: `DescriptiveComplexity.Problems.Wide.DrawKindRule`
dispatches each atom to its kind's machinery behind a **parameter pack**
(`DescriptiveComplexity.Draw.StageArgs`/`TagArgs`/`ElemArgs` – the matches
and control updates stay packed until the runs, while
`DescriptiveComplexity.Draw.Data.kindSep` closes separation from the
packs alone), and `DescriptiveComplexity.Problems.Wide.DrawVarRule` builds
the matrix (`DescriptiveComplexity.Draw.Data.matrixRule`/`matrixSep`, the
sequencer over the classified atoms) and the gates
(`DescriptiveComplexity.Draw.Data.gatesRule`/`gatesSep`, per block a
well-shapedness test whose failing exit clears the verdict flag and whose
passing exit runs the tag-branched domain evaluation). Every layer also
carries its **ownership** obligation (`DescriptiveComplexity.Draw.elemHosrc`
and its siblings up to
`DescriptiveComplexity.Draw.Data.gatesHosrc`): a rule fires from a phase
its own site owns, which is what makes separation compose.
`DescriptiveComplexity.Problems.Wide.DrawProg` closes the shape layer –
one variable's machinery with its gates and matrix plugged in
(`DescriptiveComplexity.Draw.Data.varRuleF`), one copy per enumerated
variable and one for the output
(`DescriptiveComplexity.Draw.Data.smRule`), the spine over them
(`DescriptiveComplexity.Draw.Data.evalRuleF`) and the outer loop around
it, delivering **the program's whole rule set** as one
`DescriptiveComplexity.Draw.Assembly`
(`DescriptiveComplexity.Draw.Data.progAsm`), whose
`DescriptiveComplexity.Draw.Assembly.prog` and
`DescriptiveComplexity.Draw.Assembly.sep` are the program and its
determinism. The semantic content rides in one pack per variable
(`DescriptiveComplexity.Draw.Data.VarArgs`), untouched by separation and
fixed with the runs.
`DescriptiveComplexity.Problems.Wide.DrawRun` begins the
runs: the program's rules **are** its kits' rules (one `rfl` per call site,
`DescriptiveComplexity.Draw.Data.prog_rules_seek1` and its siblings), a rule
of the assembly drives a step at its own destination data
(`DescriptiveComplexity.Draw.Data.prog_hasRight`/`prog_hasLeft`), the
initial tape is the empty state's background
(`DescriptiveComplexity.Draw.Data.initBack_eq_back`, the joint between the
input channel's marks and the presentation every pass walks), and the first
leg is proved – `DescriptiveComplexity.Draw.Data.step_start`, planting the
marker and the bottom mark at the empty address. The glue between legs is
`DescriptiveComplexity.Draw.Data.trackTape_back`: a pass's presentation
*is* the background it walks, so one leg's conclusion is the next's
hypothesis whichever track each walks
(`DescriptiveComplexity.Draw.Data.trackTape_back_swap`). With it the
next legs follow: `DescriptiveComplexity.Draw.Data.reaches_tgtTop` (the
round trip writing the logical top into TARGET) and
`DescriptiveComplexity.Draw.Data.reaches_seek1` (the random access taking
the working cell there, the target address strictly below the file because
the least element carries no argument block –
`DescriptiveComplexity.Draw.tagBlk_eq_none_of_least`), with the two single
steps that bracket a loop head (an exit steps right off the marker, the
head's stay rule walks back). Then the reset takes the marker home
(`DescriptiveComplexity.Draw.Data.reaches_reset1`, whose one hypothesis
beyond the slot equations is the seek's own erasing exit – it plants the
permanent `ltp` end marker there) and a clear empties the mirror
(`DescriptiveComplexity.Draw.Data.reaches_clearMir1`). All of it chains
into **`DescriptiveComplexity.Draw.Data.reaches_startup`**: from the
initial configuration – the marks over the blank – to the entry of the
per-address evaluation, with both permanent markers planted and every
register where the loop expects it. The outer loop's other legs are built
too: the two **plain sweeps** –
`DescriptiveComplexity.Draw.Data.reaches_compare` (the verdict
accumulated in the phase by `DescriptiveComplexity.sweepState`, its per-cell
question read off the stage tracks) and
`DescriptiveComplexity.Draw.Data.reaches_copy` (the background a family
indexed by the sweep's frontier: the addresses already passed hold the next
stage) – the three walks home
(`DescriptiveComplexity.Draw.Data.reaches_home` and its three instances)
and **one round of the outer sweep**
(`DescriptiveComplexity.Draw.Data.reaches_sweepAdv`: the marker and the
mirror step on in lockstep, the erasing entry being the caller's rule, as
the reset's is). Every kit the outer program instantiates has now been
driven at the program level; what the loop still waits on is the
per-address evaluation between two rounds. Its first brick is in
`DescriptiveComplexity.Problems.Wide.DrawBack`: the permanent marks read back
at a register cell (the existential collapses by injectivity of
`DescriptiveComplexity.wmSeg`), and with them the **navigation by name** –
`DescriptiveComplexity.Draw.Data.nameG_cell` says what the guard sees,
`nameG_unique` that it stops at one cell, `not_nameG_of_not_reg` that it
never stops in the working area. The other half of that instantiation is the
control's **dictionary**, `DescriptiveComplexity.Problems.Wide.DrawCtl`:
which `DescriptiveComplexity.Draw.Ctl` slot plays which role – the loop
element's coordinates, the inner fold's accumulators, a sub-fold's, the
atoms' verdicts, the leaf-read and tag-witness flags, the gates' verdict –
with the casts through the computed budgets, their distinctness, and the
two operations every semantic parameter is built from
(`DescriptiveComplexity.Draw.Data.ctlBit`/`setCtl` and their read-back
equations) – together with the **tuple enumeration** the element loops run
on: `DescriptiveComplexity.Draw.IsMaxTup`,
`DescriptiveComplexity.Draw.tupNext` and
`DescriptiveComplexity.Draw.botTup` are the functions behind the relation
`DescriptiveComplexity.TupSucc` that
`DescriptiveComplexity.Draw.reflTransGen_of_tupLoop` indexes its rounds by,
and `DescriptiveComplexity.Draw.Data.readLv`/`putLv` are how a round's
tuple is read out of the control and written back.

What a leaf of those loops actually reads is fixed in
`DescriptiveComplexity.Problems.Wide.DrawName`: an encoded tuple is
canonically padded, so it lives in a cell the marks name
(`DescriptiveComplexity.Draw.Data.encTup_isPad`); the trip's guard – the
name guard at *computed* coordinates,
`DescriptiveComplexity.Draw.Data.nameGF` – holds at exactly that cell
(`encG_iff`); and the register digit found there is one membership question
of the block value, hence **one bit of the assignment** of the point the
block holds (`blk_encAsgTup_iff`) or its **tag test**
(`blk_encTagTup_iff`). That is the whole interface between the machine and
`DescriptiveComplexity.Draw.encPt`.

And `DescriptiveComplexity.Problems.Wide.DrawPad` settles the arithmetic of
the inner loop's levels: the VAL register has one block per level of the
*longest* pack and its enumeration plays all of them, so the machine plays a
prefix too long at both ends – below, the levels the matrix reads off the
working address; above, the levels nothing reads. Neither matters, because a
level whose matrix ignores it may be skipped over a nonempty domain
(`DescriptiveComplexity.Draw.altQuantFrom_skip`), a prefix over more
coordinates than its matrix reads plays as its restriction
(`altQuantFrom_pad`), and a matrix may be changed anywhere the walk cannot
reach (`altQuantFrom_congr_mat`).

With them, `DescriptiveComplexity.Problems.Wide.DrawLeaf` says **what the
inner loop computes**. The dictionary is fixed there: level `j` of a
variable's pack is inner block `j` of the register, the free levels reading
the working address's outer blocks instead
(`DescriptiveComplexity.Draw.Data.levelVal`), and the leaf is the gated
matrix at that valuation (`leafP` – the encodings' gates belong to the leaf,
not to the loop). `DescriptiveComplexity.Draw.Data.altQuantFrom_leafP` is
the join: the prefix of the leaf over *every* block, played from level `0`,
**is** `DescriptiveComplexity.StepDef.next` at the points the working
address encodes; and `foldFrom_leafP_top` reads that off the accumulators at
the address the loop stops at, the inner top.

`DescriptiveComplexity.Problems.Wide.DrawVerdict` closes that circle at the
machine: `DescriptiveComplexity.Draw.Data.accVerdict_next` says the
machinery's exit bit at a variable's position **is** `StepDef.next` at the
working address's points, every abstract input of the run layer's capstone
discharged from the two facts a reduction's tape maintains – the address's
outer blocks encode the argument tuple, and each stage track holds the
dictionary. Its sibling `accVerdict_out` is the same reading at the
**output** variable, where the answer is `d.out` itself at the stage the
tracks hold: a sentence has no free level, so the prefix starts where the
machine starts it (`altQuantFrom_leafP_out`, over
`DescriptiveComplexity.Draw.StepDef.out_iff_gateMat` – the nullary
`next_iff_gateMat`) and the verdict is taken at the *empty* address. That is
the bit the accepting dispatch reads, so it is the whole of what a yes-answer
of `DescriptiveComplexity.StepDef.PFPHolds` has to deliver once the stage is
stable.

The enumeration both of those read a register through is
`DescriptiveComplexity.Problems.Wide.DrawValEnum`: the VAL loop starts empty,
increments, and stops at the **Kin top** – the set of the inner-block cells –
so what it consumes is an initial segment of the binary-counter order,
indexed by `Fin (n + 1)` for the instances the run theorems ask for
(`DescriptiveComplexity.Draw.Data.exists_valEnum`, built by
`exists_wmChain` from repeated `DescriptiveComplexity.exists_wmPred`). It
delivers the five facts a semantic reading needs, the last of them the one
the machine could not be trusted for on its own: every register of the chain
holds inner cells *alone*. That is not a property of the counter but of the
layout – the Kin blocks are a final segment of the tag order
(`DescriptiveComplexity.Draw.kinSeg`), and a set at or below an upward-closed
one is contained in it (`DescriptiveComplexity.subset_of_wmSetLe`).

`DescriptiveComplexity.Problems.Wide.DrawSpineSem` carries that
along the whole spine: the mirror, the dictionary and the markers ride
every position's write (`spineRide`), so after the spine each variable's
`new` cell at the address holds one step of the iteration there
(`new_last_next`) – or nothing, at an address encoding no tuple
(`new_last_of_false`). Read in dictionary form (`new_last_trackOf`,
`new_last_trackOf_of_junk`) and iterated along the addresses by
`DescriptiveComplexity.holds_of_wideRounds`, that is `sweep_new`: a sweep
rewrites the tracks of exactly the addresses it has passed. The same file
carries the pack's transport (`kindSemCast` and its content lemmas): a
position's semantic pack is typed at that position's state, but
`DescriptiveComplexity.Draw.Data.KindSem` reads the state only through
the levels' register sets, so one pack built at the address's entry state
serves every position. That is what makes the per-position families
*constructible* rather than merely stateable: `spineNode` recurses along
the positions producing state, mirror invariant and control together, and
its projections satisfy exactly the cover equations `evalSpine_run` asks
for. One scale up the same file builds the sweep's own families
(`sweepSW`/`sweepFS`, `sweepSW_incr`/`sweepFS_incr`): an iteration along
the addresses, because a leg's writes are local to its cell but its
*control* accumulates – with the order on the addresses installed locally,
never as an ambient instance.

The **branched** family – the one a sweep runs, each position taking
whichever of its three legs its own gates call for – asks for no pack at
all: its semantic parameter is the *conditioned* family
`DescriptiveComplexity.Draw.Data.gatedSem` inhabits, a pack at every
gated position of every state and every address, built from
`DescriptiveComplexity.Draw.Data.isEnc_of_gatedAt` because a gated
position's argument blocks **are** encodings. Supplied at the top as
`fun w => dt.gatedSem hzo hlin mV`, it leaves no semantic assumption about
a position anywhere in the run layer. What the dictionary lemmas ask of a
leg is correspondingly weakened to the projection they read
(`DescriptiveComplexity.Draw.Data.WritesNew`: its variable's cell at the
marker holds its verdict, every other cell rides), which a branched leg
satisfies (`legStB_new`, `spineStOfB_writesNew`) while it is not literally
a `postVarSt` of the position's entry state – its VAL loop may normalize
the two scratch registers first.

The **element loops** of the atom subroutines have the same anchor one scale
down, `DescriptiveComplexity.Problems.Wide.DrawExp`: an atom of the expansion
holds of a tuple of points exactly when the prefix of
`DescriptiveComplexity.Draw.Data.expLeaf` – the Boolean value of the
defining sentence's matrix, its block atoms read off the argument points'
assignments and its base atoms decided by guards – is played from level `0`
(`relMap_iff_altQuantFrom_expLeaf`, and `_pad` for the loop the machine
actually runs, over every loop-variable slot). The classifier it reads that
matrix through is now stated at an **arbitrary block**
(`DescriptiveComplexity.Draw.BlkAtom` in
`DescriptiveComplexity.Problems.Wide.DrawRepAtoms`), so the same lemmas serve
the replicated block of a defining sentence and the plain block of a domain
sentence.

## What a clocked program is bound by

The EXPSPACE program above roams; the NEXPTIME one
(`DescriptiveComplexity.wideRegAccept_NEXPTIME_complete`) runs against a clock,
its file handed to it by a register channel, and the clock is what its design
answers to. What follows is what that cost, i.e., the questions a construction
that moves the file, the atom or the index has to answer again. They are
constraints on the *design* rather than on the proof: each rules out the
arrangement that would otherwise be the obvious one.

**Time is bought with tags, so an exponentially long program is affordable.**
The drawn universe is `Tag × Aᵈ`, so the clock is `2 ^ (|Tag| · nᵈ)` and `|Tag|`
is the reduction's to choose: any `2 ^ (O(nᵈ))`-step program fits, and one extra
tag multiplies the budget by `2 ^ (nᵈ)`. What the clock rules out is the
*iteration* – a partial fixed point may run through `2 ^ (2 ^ …)` stages, and no
choice of tags pays for that – and **not** the round trip. The EXPSPACE
program's shape survives it: rounds, sweeps up and back, a mirror, a seek per
atom, with the inner evaluation run **once** over the working region costing
`2 ^ (2k · nᵈ)`, which fits at `|Tag| = 2k + 2`.

**A wide machine cannot name its own elements, so it cannot lay a register
file.** A state's payload holds one element per control flag *and* one per slot
inside a `dd`-tuple, so the control takes `|A| ^ #flags` values with
`#flags < dd`, while the universe has `|Tag| · |A| ^ dd` elements
(`card_ctl_lt_card_univ`, `not_injective_ctl_name`). A file that records
addresses faithfully needs one register per element and names that separate
them, and a sweep can only write a name it holds in its control; widening the
dimension moves both sides together. **A program's file therefore comes from the
input channel or not at all**, which is why the clocked machine is handed one
(`DescriptiveComplexity.Problems.Wide.RegChannel`) and lays none.

**The mark ladder is a space-only device, at every scale.** `wmSeg x` is the
address `{y | y ≤ x}`, and `DescriptiveComplexity.WMSetLe` reads the `wmLe`-least
element as the most significant digit, so the mark of the `j`-th element sits at
address `2 ^ m − 2 ^ (m − j − 1)`, with `m` the size of the drawn universe: the
file is a geometric ruler lying entirely in the **top half** of the tape, at
1/2, 3/4, 7/8 … Reaching the stretch carrying its top `t` marks costs
`2 ^ m − 2 ^ (t − 1)` steps out of a budget below `2 ^ m`, which leaves less than
one traversal of that stretch, and adding tags scales both sides, so the reading
is scale invariant. **A clocked run may walk such a file once, and there is no
second time**; that, and not roaming, is what fails to transfer from the
space-bounded programs.

**A working region at the *bottom* of the tape is free.** Put the surplus tags in
the most significant blocks: the addresses whose high blocks are empty are an
initial stretch of `2 ^ (k · nᵈ)` cells, where the head already stands, while the
clock stays `2 ^ ((k + j) · nᵈ)`. A seek across the region costs the region, so
one seek per round is affordable, and so is a full sweep of the region per round.

**A clocked program has exactly one landmark, and it is where its head starts.**
A rule sees the control and the cell under the head and nothing else, so no rule
can tell the head its address: what a program can locate is the address it starts
on, the ones a fixed number of **tuple roll-overs** away from it (the control
counts a tuple with `tupNext` and knows it is exhausted by `IsMaxTup`), and the
ones it has itself marked. Positively, **a stretch a clocked program can walk is
one whose length is a fixed number of tuple roll-overs** – the evaluation's own
walks, the working region and the certificate guess all are. A file indexed by
*universe elements* is not, so the file is indexed by `(block, tuple)` pairs
(`DescriptiveComplexity.Wide.BlkIx`, `Option K × (Fin dd → A)`) and the laying
sweep is `|K| + 1` runs. That is also exactly what a background reads at a
register: the block one-hot goes through `tagBlk` alone and the name slots are
the tuple, so nothing of the tag beyond its block is ever used.

**A block-indexed file can still carry a seek**, and which addresses a seek
passes through is why. The tag order puts `ctrl` and `sym` in the most
significant blocks and the `arg` blocks in the least, so the **logical**
addresses – those whose non-argument blocks are empty – are an initial interval
(`wmSetLe_logicalTop`, `nonArg_downward`), and every address a seek to a logical
target passes through is logical; a file with a register per `(block, tuple)`
therefore carries every bit such a seek reads or writes. The same fact makes the
working region an initial stretch and gives it its size
(`wideRank_lt_two_pow_logical`). The index sits at the **full** width `dd` and
not at `dd₀`: a file at `dd₀` would name exactly the canonically padded elements,
enough for a copy loop that walks by name but not for a mirror, whose
intermediate logical addresses mark argument elements of every tuple.

**The file goes above the data, and the approach is what it costs.** A stage atom
seeks to a dictionary entry, an entry is a logical address, and what the atom is
given is that every logical address lies below every register – so the file has
to be laid *above* the whole logical region, which is not where a machine with
one landmark would naturally put it. The program pays for that in its opening:
the opening step plants the marker and moves right into an **approach walk**
(`NexPh.approachP`), which writes nothing and stops wherever the program likes –
one more nondeterministic choice, like the guess's stop, and for the same reason,
nothing on the tape telling the head where it is. The base is where it stops, the
file is laid from there, and the guess then sweeps the data region *below* the
file, entered from the marker's own neighbor (`reachesIn_openingRegion`,
`openingRegion_le_two_pow`). The arrangement a reader thinks of first – leave the
file at the bottom and teach the atom to seek upward past it – moves the cost
from the opening, which runs once, into the seek, which every atom runs.

**Every fixed-point variable must have an argument**, and the reduction pads the
one that does not: a nullary variable's dictionary entry is the *empty* address,
the marker's own cell, below every stretch the machine writes and the one address
an encoding can never be. The guess's range, the atom's target and the track's
own shape all come down to that, and `0 < d.B.arity` discharges the three at once
(`NexKernel.withArg` is the padding, and padding a `Σ₁` relation with a dummy
argument costs nothing).

**How a guessed relation's atoms are served.**
`DescriptiveComplexity.Problems.Wide.Blocks` serves an atom on the *leading*
blocks with one state bit, addresses sharing a prefix of blocks being a
contiguous stretch; an occurrence on any other tuple is a union of stretches, and
one bit no longer keeps it consistent. The answer taken is a **seek per
occurrence per address** – what the EXPSPACE program already does for its stage
store – rather than a normal form putting every occurrence on a prefix
(unproved) or one guessed copy per occurrence checked against the others (the
same problem again). That is why the clocked program keeps the EXPSPACE atom
machinery instead of asking the control to hold the valuation.
-/
