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
import DescriptiveComplexity.Problems.Wide.Roam
import DescriptiveComplexity.Problems.Wide.Marks
import DescriptiveComplexity.Problems.Wide.Tape
import DescriptiveComplexity.Problems.Wide.Walk
import DescriptiveComplexity.Problems.Wide.Mirror
import DescriptiveComplexity.Problems.Wide.Test
import DescriptiveComplexity.Problems.Wide.PfpTags
import DescriptiveComplexity.Problems.Wide.PfpAlphabet
import DescriptiveComplexity.Problems.Wide.PfpMatrix
import DescriptiveComplexity.Problems.Wide.PfpGeom
import DescriptiveComplexity.Problems.Wide.PfpTable
import DescriptiveComplexity.Problems.Wide.PfpTracks
import DescriptiveComplexity.Problems.Wide.PfpRules
import DescriptiveComplexity.Problems.Wide.PfpPass
import DescriptiveComplexity.Problems.Wide.PfpScan
import DescriptiveComplexity.Problems.Wide.PfpRel
import DescriptiveComplexity.Problems.Wide.PfpEnc
import DescriptiveComplexity.Problems.Wide.PfpInner
import DescriptiveComplexity.Problems.Wide.PfpLoop
import DescriptiveComplexity.Problems.Wide.PfpSpec
import DescriptiveComplexity.Problems.Wide.PfpAddr
import DescriptiveComplexity.Problems.Wide.PfpOrd
import DescriptiveComplexity.Problems.Wide.PfpGate
import DescriptiveComplexity.Problems.Wide.PfpSlots
import DescriptiveComplexity.Problems.Wide.PfpSub
import DescriptiveComplexity.Problems.Wide.PfpInit
import DescriptiveComplexity.Problems.Wide.PfpAdv
import DescriptiveComplexity.Problems.Wide.PfpSweep
import DescriptiveComplexity.Problems.Wide.PfpTrip
import DescriptiveComplexity.Problems.Wide.PfpSeek
import DescriptiveComplexity.Problems.Wide.PfpRead
import DescriptiveComplexity.Problems.Wide.PfpAcc
import DescriptiveComplexity.Problems.Wide.PfpAtoms
import DescriptiveComplexity.Problems.Wide.PfpData
import DescriptiveComplexity.Problems.Wide.PfpKit
import DescriptiveComplexity.Problems.Wide.PfpAsm
import DescriptiveComplexity.Problems.Wide.PfpTripKits
import DescriptiveComplexity.Problems.Wide.PfpIncrKit
import DescriptiveComplexity.Problems.Wide.PfpSweepKit
import DescriptiveComplexity.Problems.Wide.PfpAdvKit
import DescriptiveComplexity.Problems.Wide.PfpSeekKit
import DescriptiveComplexity.Problems.Wide.PfpReset
import DescriptiveComplexity.Problems.Wide.PfpSites
import DescriptiveComplexity.Problems.Wide.PfpBack
import DescriptiveComplexity.Problems.Wide.PfpOuter
import DescriptiveComplexity.Problems.Wide.PfpEval
import DescriptiveComplexity.Problems.Wide.PfpVar
import DescriptiveComplexity.Problems.Wide.PfpChain
import DescriptiveComplexity.Problems.Wide.PfpTuple
import DescriptiveComplexity.Problems.Wide.PfpStageAtom
import DescriptiveComplexity.Problems.Wide.PfpElem
import DescriptiveComplexity.Problems.Wide.PfpTagged
import DescriptiveComplexity.Problems.Wide.PfpSeq
import DescriptiveComplexity.Problems.Wide.PfpRepAtoms
import DescriptiveComplexity.Problems.Wide.PfpTower
import DescriptiveComplexity.Problems.Wide.PfpKindRule
import DescriptiveComplexity.Problems.Wide.PfpVarRule
import DescriptiveComplexity.Problems.Wide.PfpCtl
import DescriptiveComplexity.Problems.Wide.PfpName
import DescriptiveComplexity.Problems.Wide.PfpPad
import DescriptiveComplexity.Problems.Wide.PfpLeaf
import DescriptiveComplexity.Problems.Wide.PfpExp
import DescriptiveComplexity.Problems.Wide.PfpCmp
import DescriptiveComplexity.Problems.Wide.PfpAccCtl
import DescriptiveComplexity.Problems.Wide.PfpArgs
import DescriptiveComplexity.Problems.Wide.PfpProg
import DescriptiveComplexity.Problems.Wide.PfpRun
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

Everything above is written for `DescriptiveComplexity.WideAccept`, whose clock
counts the addresses: its programs are **one monotone sweep** and nothing more.
The two space-bounded problems have *no* clock – acceptance is
`Relation.ReflTransGen` of the step relation – so their programs may **roam**,
sweeping up and back down as often as they like, and that is a strictly larger
model with a cheaper interface.
`DescriptiveComplexity.Problems.Wide.Roam` is that interface: a phase up
(`DescriptiveComplexity.reaches_of_wideUp`), a phase down
(`DescriptiveComplexity.reaches_of_wideDown`), the **scan** they are almost
always used for (`DescriptiveComplexity.reaches_scanRight`,
`DescriptiveComplexity.reaches_scanLeft` – hold the state, rewrite each symbol by
itself, walk until the scanning transition is withheld), and the run shape
`DescriptiveComplexity.acceptsSpace_of_wideRoam`. No count occurs in any of them.

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
every phase. `DescriptiveComplexity.Problems.Wide.Walk` is then the phase a
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
state whatever the mirror was, so a caller reads "the increment is finished" off
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
working area is `DescriptiveComplexity.reaches_of_wideRounds`: the same shape as a
sweep, but with a whole *run* between an address and its increment rather than a
single step. That is what a program's loops are written with, and what a clock
would forbid – each round costs exponentially many steps and there are
exponentially many rounds.

One more piece of the layer belongs to no single pass and is used by all three.
The passes take the tape as a function of *one track* and each asks the same
coherence condition: changing the track at one element changes the tape at that
element's cell and nowhere else. A program does not check that by hand – it reads
its track through `DescriptiveComplexity.regBit` (the digit at a register cell,
nothing anywhere else) and `DescriptiveComplexity.regBit_congr` is the condition,
discharged once for every program and every alphabet.

## The EXPSPACE reduction, begun

`DescriptiveComplexity.Problems.Wide.PfpTags` fixes the universe the hardness
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
(`DescriptiveComplexity.Pfp.wmSetLe_logicalTop`, joined to the machine's own order
by `DescriptiveComplexity.Pfp.Table.wmSetLe_logicalTop_reads`), which is the upper
bound `DescriptiveComplexity.reaches_of_wideRounds` asks for; and the least element of
the universe lies in the `ctrl` block, so the register file – every cell of which
contains it – sits above every logical address, and data and registers cannot
collide.

`DescriptiveComplexity.Problems.Wide.PfpAlphabet` fixes the alphabet by the only
discipline available – a symbol is an element, hence a tagged tuple, so one
**coordinate** of the tuple is one **track**, holding one of two designated
elements of the source structure (its least and its greatest, both definable,
which is why the one-element structure is gated). `DescriptiveComplexity.Pfp.withBit`
writes a track and `DescriptiveComplexity.Pfp.bitAt` reads one; a track reads back
what was written (`DescriptiveComplexity.Pfp.bitAt_withBit`, whose only hypothesis
is that the two elements differ) and writing one leaves the others alone
(`DescriptiveComplexity.Pfp.withBit_of_ne`). Together with
`DescriptiveComplexity.regBit_congr` this is what discharges the coherence
condition of every register pass: a program's tape is
`fun r => (sym, withBit … (regBit m r))`, and the condition is `congrArg` through
`DescriptiveComplexity.Pfp.withBit_congr`. Distinctness comes from the same place
(`DescriptiveComplexity.Pfp.withBit_inj`): symbols carrying different bits are
different elements, which a transition table needs both to read a track and to be
deterministic.

One structural note, since it is what the transition table will hang on: the
subroutines above take **their states as parameters**, so a program with several
call sites of the same subroutine gives each its own states and needs no
continuation label and no dispatch. Its phase set is exactly the list of its call
sites.

`DescriptiveComplexity.Problems.Wide.PfpMatrix` supplies the semantic half of the
step the program spends its time in. The machine evaluates the matrix of its step
formula **atom by atom** – a subroutine per atom, the accumulating assignment in
the *coordinates* of the state – and that is correct because a quantifier-free
formula is a Boolean function of its atoms:
`DescriptiveComplexity.Pfp.realize_qfValue` says its realization is
`DescriptiveComplexity.Pfp.qfValue` at the assignment that reads each atom off the
structure, and `DescriptiveComplexity.Pfp.qfValue_congr` says only the atoms of
`DescriptiveComplexity.Pfp.qfAtoms` matter. Those two are why the phase count is
*linear* in the number of atoms rather than exponential: the machine visits the
atoms once, and the final transition is a disjunction over the assignments that
satisfy `qfValue`, a finite list a defining formula can write out. The recursion
is total and the correctness is by induction on `IsQF`, the shape
`Exponential/Matrix.lean` uses for the same reason.

`DescriptiveComplexity.Problems.Wide.PfpGeom` says which elements the states, the
symbols and the transitions *are*: each carries a payload of `c` coordinates
(`DescriptiveComplexity.Pfp.pad`) with a designated element beyond it, and the
kind is the tag – `phase p` for a state, `sym` for a symbol, `ctrl r` for a
transition of the rule `r`. The padding is not decoration: without it an element
would have `n^(dd-c)` spellings, and the machine's promises are that there is
*one* start state, *one* blank and at most one transition per state and symbol.
`DescriptiveComplexity.Pfp.pad_injective` and the three `_ne_` lemmas are the
distinctness those obligations are discharged from.

`DescriptiveComplexity.Problems.Wide.PfpTable` is the transition table itself,
and the two promises the emitted instance has to keep. A table names, rule by
rule, a guard, the two phases, the payloads of the state and of the symbol on
each side, and the direction; the eleven relations of
`FirstOrder.Language.wide` are then read off it
(`DescriptiveComplexity.Pfp.Table.Reads`), and a program's whole interaction with
it is two theorems – `DescriptiveComplexity.Pfp.Table.fire_right` and
`DescriptiveComplexity.Pfp.Table.fire_left`, a rule firing with its six
attributes, which is the shape every subroutine above asks for. The promises cost
what the layout was built to make them cost:
`DescriptiveComplexity.Pfp.Table.wellFormed` is the order being
`DescriptiveComplexity.tagTupleLe` plus the input and the blank being written as
equations, and `DescriptiveComplexity.Pfp.Table.deterministic` reduces to one
condition on the table, `DescriptiveComplexity.Pfp.Table.Sep`: two guarded rules
that apply in the same state and read the same symbol are the same rule with the
same data.

`DescriptiveComplexity.Problems.Wide.PfpTracks` names the coordinates. A payload
is a function of a finite **slot** type (`DescriptiveComplexity.Pfp.slotPl`, read
back by `DescriptiveComplexity.Pfp.unslot`) and a slot carrying a bit holds one of
the two designated elements (`DescriptiveComplexity.Pfp.bitVal`,
`DescriptiveComplexity.Pfp.bitVal_iff`), so a program never counts a coordinate
and the distinctness obligations of the table are statements about named fields.

`DescriptiveComplexity.Problems.Wide.PfpRules` writes a program rule by rule, and
splits the slots in the one way that works. A transition's data must carry **both**
payloads – the state's and the symbol's – because neither determines the other:
the symbol under the head cannot name the register the head is on, the registers
being anonymous, and the state cannot name the symbol it is about to read. So the
slots are `Q ⊕ W`, the **control** slots a state uses and the **track** slots a
symbol uses (`DescriptiveComplexity.Pfp.stVec`,
`DescriptiveComplexity.Pfp.syVec`), and two things follow. Firing a rule needs no
payload arithmetic – the data is the pointer and the tracks side by side, so
`DescriptiveComplexity.Pfp.Prog.fire_left` and its rightward twin hand a program
its six attributes at the elements it named. And determinism becomes a check on
*rules*: the two payloads occupy disjoint coordinates, so
`DescriptiveComplexity.Pfp.Table.Sep` reduces to
`DescriptiveComplexity.Pfp.Prog.sep_of` – two rules that fire on the same symbol
from the same state are the same rule.

The same file carries the tape a register pass runs over,
`DescriptiveComplexity.Pfp.Prog.trackTape`: the track slot being walked holds the
digit of the track at this cell and the others hold whatever the program keeps
there. Its coherence condition – changing the track at one element moves the tape
only at that element's cell – is
`DescriptiveComplexity.Pfp.Prog.trackTape_coh`, proved once for every program and
every alphabet, so the three passes are entered with nothing to discharge.

`DescriptiveComplexity.Problems.Wide.PfpPass` runs the three register passes off
the program's rules. What a program owes is
`DescriptiveComplexity.Pfp.Prog.HasLeft` – *in this phase, at this pointer,
reading these tracks, a rule of mine goes to that phase and that pointer, writes
those tracks and moves left* – and nothing else: the symbols are computed for it,
so it never sees `DescriptiveComplexity.regBit`, never writes a tape equation and
never mentions `FirstOrder.Language.wide`. With four such families
`DescriptiveComplexity.Pfp.Prog.reaches_incr` is the mirror increment, and with
four `DescriptiveComplexity.Pfp.Prog.reaches_testG`
(`DescriptiveComplexity.Problems.Wide.PfpSub`) asks one question of every
register – a question the *tracks* decide – and brings the verdict back in the
phase. One track slot carries *this cell is a register*, which is both what
tells the acting rules from the walking one and what their separation argument
is discharged from. The background of the walked track is **element-valued**,
so the tape can carry the name marks; the mark hypotheses are `bitVal`
equations.

The increment comes in two forms, and the difference is the one thing the
anonymity of the registers costs.
`DescriptiveComplexity.Pfp.Prog.reaches_incrAt` stops in the phase of the **block**
that carried – which is what the fold of `DescriptiveComplexity.Problems.Wide.Fold`
has to know, and which the machine learns not by naming the register (it cannot: a
state's payload holds elements of the source structure) but by reading the block
off that cell's *mark*, one stopping rule per block.
`DescriptiveComplexity.Pfp.Prog.reaches_incr` is the single-block case, the register
mark serving as its own indicator, and is the form every use that only has to
*move* an address takes.

Between passes the program writes its own data, and that is one step:
`DescriptiveComplexity.Pfp.Prog.step_move` and its leftward twin change the
**background** at the cell the head leaves while carrying the track along
untouched, so a step and a register pass compose without either knowing what the
other keeps on the tape.

Navigation is there too, and it is two theorems rather than four:
`DescriptiveComplexity.Pfp.Prog.reaches_toMark` and its downward twin get the head
to a register the caller has *marked* – the two ends of the file, which are the
only cells that have to be recognized on sight – taking the target as a parameter
rather than naming it; and `DescriptiveComplexity.Pfp.Prog.reaches_seek` and
`reaches_seekBack` walk the working area to the nearest cell carrying a given
slot, arriving with the promise that nothing passed carried it, which is where the
extremum a program cannot name is taken.

On top of the pass layer sit the pieces the EXPSPACE program's atom
subroutines consume. `DescriptiveComplexity.Problems.Wide.PfpScan` scans to a
cell recognized by an arbitrary guard on its tracks
(`DescriptiveComplexity.Pfp.Prog.reaches_toCell` and its three variants) – the
navigation to a register cell whose *name marks* match a tuple held in the
control. `DescriptiveComplexity.Problems.Wide.PfpEnc` encodes the points of an
exponential expansion injectively as block values
(`DescriptiveComplexity.Pfp.encPt`, one membership question per bit of the
assignment, `DescriptiveComplexity.Pfp.mem_encPt_asg`), and
`DescriptiveComplexity.Problems.Wide.PfpRel` moves an alternating quantifier
prefix from the points to the block values a register enumerates, by gating the
matrix polarity-correctly (`DescriptiveComplexity.Pfp.altQuantFrom_gateMat`).
`DescriptiveComplexity.Problems.Wide.PfpInner` restates the fold–increment join
of `DescriptiveComplexity.Problems.Wide.Bridge` on a *final segment* of the
blocks – the `Kin` half of the argument tags, where the inner loop's register
enumerates the prefix valuations – and adds the control-scale fold rules along
a tuple successor; `DescriptiveComplexity.Problems.Wide.PfpLoop` supplies the
induction the control loops run on
(`DescriptiveComplexity.Pfp.reflTransGen_of_tupLoop`).

`DescriptiveComplexity.Problems.Wide.PfpSpec` states what the program's inner
loop computes, with no machine in sight: one step of the iteration at a tuple
of points is the gated prefix over block values
(`DescriptiveComplexity.Pfp.StepDef.next_iff_gateMat`), the step formula put
once into prefix normal form with its free variables re-bound first
(`DescriptiveComplexity.Pfp.PrenexPack`). And
`DescriptiveComplexity.Problems.Wide.PfpAddr` fixes the argument blocks –
outer arguments first, inner prefix variables last, `K := Fin ko ⊕ₗ Fin ki` –
proves the inner tags a final segment of the tag order
(`DescriptiveComplexity.Pfp.kinSeg`, the hypothesis pack of the inner loop's
fold rules), and writes the stage dictionary: the content of a stage track at
an address (`DescriptiveComplexity.Pfp.trackOf`), reading only the blocks below
the variable's arity, `False` off the encodings, so the all-blank initial tape
is exactly stage `0`. Finally, `DescriptiveComplexity.Problems.Wide.PfpOrd` is
the order the reduction puts on the points: `DescriptiveComplexity.PFPDefinable`
quantifies over every linear order on the expanded universe, so the reduction
chooses the pullback of the binary block-value order along the encoding
(`DescriptiveComplexity.Pfp.encOrder`), making an order atom exactly the
comparison of two encodings in the machine's own reading
(`DescriptiveComplexity.Pfp.encOrder_le_iff`,
`DescriptiveComplexity.Pfp.wmSetLe_iff_setLe`).

The first two concrete pieces of the program are in place.
`DescriptiveComplexity.Problems.Wide.PfpGate` decomposes the gate the way the
machine checks it (`DescriptiveComplexity.Pfp.isEnc_iff_parts`: a tag witness,
well-shapedness of every member, the domain sentence at the decoded
assignment `DescriptiveComplexity.Pfp.decRho`), and
`DescriptiveComplexity.Problems.Wide.PfpSlots` fixes the track and control
slot inventories (`DescriptiveComplexity.Pfp.Slot`,
`DescriptiveComplexity.Pfp.Ctl`) and the mark of every register cell
(`DescriptiveComplexity.Pfp.slotMark`) – including the budgeted register
naming, whose uniqueness among padded cells
(`DescriptiveComplexity.Pfp.eq_of_slotMark_name`) is what stops the
navigation-by-name scans at exactly one cell.
`DescriptiveComplexity.Problems.Wide.PfpSub` holds two corrections the
interface needed once its discharge was attempted: a single-cell write is a
navigation plus **one step**
(`DescriptiveComplexity.Pfp.Prog.step_writeReg`), not a pass – a pass's rules
compute their written symbol from the tracks they read, which say nothing
about an independently quantified cell – and a file test must be decided by
the tracks (`DescriptiveComplexity.Pfp.Prog.reaches_testG`, the question a
predicate of the symbol, tied to the per-cell question by one compatibility
hypothesis). And `DescriptiveComplexity.Problems.Wide.PfpInit` joins the two
ends of a run to the pass-layer presentation: the initial tape *is* the
presentation walking any clear track with the empty track
(`DescriptiveComplexity.Pfp.Prog.trackTape_initBack`, the background
`DescriptiveComplexity.Pfp.Prog.initBack` being the marks over the blank), so
a program starts from `DescriptiveComplexity.Pfp.Prog.isInit_prog` with no
initialisation sweep, and
`DescriptiveComplexity.Pfp.Prog.dwideAcceptSpace_prog` turns an accepting run
plus the separation argument into a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`.

`DescriptiveComplexity.Problems.Wide.PfpAdv` is the first composite, and the
round every sweep repeats: `DescriptiveComplexity.Pfp.Prog.reaches_advance`
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

`DescriptiveComplexity.Problems.Wide.PfpSweep` is the two shapes of a *plain*
sweep – one step per address, no register visits:
`DescriptiveComplexity.Pfp.Prog.reaches_flagSweep` asks one question per cell
with the verdict in the phase (`DescriptiveComplexity.sweepState` – COMPARE),
and `DescriptiveComplexity.Pfp.Prog.reaches_writeSweep` rewrites each cell
once, the background a function of the frontier (COPY). Their rules are
cell-coupled and bounded to the stretch; the program's device for the bound is
a permanent end marker planted at the top of the logical interval once, at
startup, a cell of the working area being otherwise unrecognizable. And
`DescriptiveComplexity.Problems.Wide.PfpTrip` factors the itinerary of every
visit to the register file – scan up, bounce, one pass down, scan back to the
marker – into `DescriptiveComplexity.Pfp.Prog.reaches_roundTrip`, the middle
pass a hypothesis: the seek loop, the test rounds of a random access and the
gate checks are all this composite around their respective passes.

On top of them, `DescriptiveComplexity.Problems.Wide.PfpSeek` is **random
access**: `DescriptiveComplexity.Pfp.Prog.reaches_seekTo` carries the
working-cell marker from the empty address to any target strictly below the
register file – rounds of a turnaround step, a round trip around the file test
*mirror = target*, and an ADVANCE, driven by
`DescriptiveComplexity.reaches_of_wideRounds`, the mirror invariant holding by
construction (the mirror track *is* the marker's address, the same
predicate). This is what evaluates a stage atom at a computed tuple of
points. And `DescriptiveComplexity.Problems.Wide.PfpRead` reads or writes
**one named register bit** – the leaves of the element loops:
`DescriptiveComplexity.Pfp.Prog.reaches_readBit_pos`/`_neg` scan up to the
cell the name guard identifies, take one branching step, and return to the
marker; `DescriptiveComplexity.Pfp.Prog.reaches_writeBit` is the same trip
with the walked track updated at that cell.

One design correction closes the semantic layer
(`DescriptiveComplexity.Problems.Wide.PfpAcc`): the sweep's control cannot
carry the fold *values* – at a carry they are not closed under the update –
so it carries the per-level **contributions**
(`DescriptiveComplexity.Pfp.accCVal`), from which every fold value is a finite
Boolean chain (`DescriptiveComplexity.Pfp.foldFrom_eq_accCVal`); the three
update rules along an increment are
`DescriptiveComplexity.Pfp.accCVal_congr_above`,
`DescriptiveComplexity.Pfp.accCVal_carry` and
`DescriptiveComplexity.Pfp.accCVal_reset`.

Finally, `DescriptiveComplexity.Problems.Wide.PfpKit` is how the program
instantiates its subroutines: **composite kits** – per composite shape, a
phase inductive, a rule inductive with concrete guards, the rules function at
a phase embedding, an in-shape separation lemma, and a discharge showing any
program containing the kit's rules satisfies the composite's run theorem.
Global determinism reduces to in-shape separation plus injective, disjoint
phase embeddings. `DescriptiveComplexity.Pfp.ReadKit` – the named-bit read –
is the template (`DescriptiveComplexity.Pfp.ReadKit.rule`,
`DescriptiveComplexity.Pfp.ReadKit.sep`,
`DescriptiveComplexity.Pfp.ReadKit.reaches_pos`/`_neg`), and the full
inventory covers every composite: `DescriptiveComplexity.Pfp.WriteKit` (the
named-bit write), `DescriptiveComplexity.Pfp.TestKit` (the file test in its
round trip, `DescriptiveComplexity.Problems.Wide.PfpTripKits`),
`DescriptiveComplexity.Pfp.ClearKit` and `DescriptiveComplexity.Pfp.CopyKit`
(the whole-track writes), `DescriptiveComplexity.Pfp.IncrKit` (the
block-indexed increment, landing in the phase of the block that carried),
`DescriptiveComplexity.Pfp.FlagSweepKit` and
`DescriptiveComplexity.Pfp.WriteSweepKit` (the plain sweeps, bounded by the
`ltp` end marker), `DescriptiveComplexity.Pfp.AdvKit` (one round of a sweep)
and `DescriptiveComplexity.Pfp.SeekKit` (the whole random-access loop,
seventeen rule families). Their disjoint guards forced three further
hardenings of the pass layer, each making a demanded rule and a supplyable
guard coincide: the return scans of the verdict phases are cell-coupled
(`DescriptiveComplexity.Pfp.Prog.reaches_toCellBackC`, threaded through
`DescriptiveComplexity.Pfp.Prog.reaches_roundTrip`), the block-indexed
increment's stopping rule takes a one-hot clause
(`DescriptiveComplexity.Pfp.Prog.reaches_incrAt`), and the seek's turnaround
and walking hypotheses are stated at exactly the guards' slot conditions
(`DescriptiveComplexity.Pfp.Prog.reaches_seekTo`). The program itself is then
**assembled from call sites** (`DescriptiveComplexity.Problems.Wide.PfpAsm`):
`DescriptiveComplexity.Pfp.Assembly` packages per-site rule shapes with an
ownership map from phases to sites, `DescriptiveComplexity.Pfp.Assembly.prog`
is the program whose rule names are the sigma, and
`DescriptiveComplexity.Pfp.Assembly.sep` its separation, via
`DescriptiveComplexity.Pfp.sep_sigma` – so each call site is built and
checked in its own file, its in-shape separation the kit's `sep` plus its
`exit_disjoint`. The per-atom call sites are indexed by the classified atoms
of the step matrices (`DescriptiveComplexity.Problems.Wide.PfpAtoms`):
`DescriptiveComplexity.Pfp.MatAtom` is the kind – equality, order, expansion
relation, stage atom – `DescriptiveComplexity.Pfp.matAtom?` reads it off the
syntax (total on the atoms `DescriptiveComplexity.Pfp.qfAtoms` emits), and
`DescriptiveComplexity.Pfp.realize_iff_qfValue_holds` is the semantic
capstone: a quantifier-free matrix realizes as its Boolean function at the
kinds' readings, which is what the machine computes once its per-atom
subroutines have filled the verdict slots. And
`DescriptiveComplexity.Pfp.PfpData`
(`DescriptiveComplexity.Problems.Wide.PfpData`) bundles the reduction's data
– the expansion, the definition, the prenex packs, the encoding layout with
its coordinate budget – with the derived dimensions the inventories are
sized by (`ko`, `ki`, the per-variable atom lists and their classified
kinds), so every site file takes one record and nothing else. The kit
*instances* at the concrete slots are in
`DescriptiveComplexity.Problems.Wide.PfpSites`: the two plain sweeps, the
seek, the advance, the block-indexed VAL increment, the clears and copies of
the registers, the pattern write of startup
(`DescriptiveComplexity.Pfp.MapKit`, wrapping the generalizing composite
`DescriptiveComplexity.Pfp.Prog.reaches_mapTrack`), the VAL-exhausted file
test, and the navigation-by-name read/write trips with their
`DescriptiveComplexity.Pfp.PfpData.nameG` guard. The one itinerary running
*down* the working area – resetting the marker to the bottom before a random
access – is `DescriptiveComplexity.Pfp.Prog.reaches_reset` with its
`DescriptiveComplexity.Pfp.ResetKit`
(`DescriptiveComplexity.Problems.Wide.PfpReset`), designed to erase and step
*right* so the empty address needs no special case. Finally,
`DescriptiveComplexity.Pfp.TapeSt`
(`DescriptiveComplexity.Problems.Wide.PfpBack`) is the machine's mutable
state – registers per element, stage tracks and markers per cell – and
`DescriptiveComplexity.Pfp.PfpData.back` its presentation as the background
family the pass layer walks, with the slot equations every kit discharge
takes proved once over it.

The **outer program is assembled**
(`DescriptiveComplexity.Problems.Wide.PfpOuter`): the program factors as an
outer loop – startup, the sweep's advance, the convergence test, the
copy-back, the output dispatch – around a per-address **evaluation** that
stays abstract (its phase type, site family and boundary rules are
parameters, the same move `Prog.reaches_roundTrip` makes for the middle of a
trip). `DescriptiveComplexity.Pfp.OuterPh`/`OuterSite`/`OuterSh` are the
phases, sites and rule shapes; `DescriptiveComplexity.Pfp.PfpData.outerRule`
the rules (each site its kit's rules plus its exit rules, a sweep's first
step folded into the rule that enters it);
`DescriptiveComplexity.Pfp.PfpData.outerSep` the in-shape separation, one
case per site from the kits' `sep` and `exit_disjoint`; and
`DescriptiveComplexity.Pfp.PfpData.outerAsm` the
`DescriptiveComplexity.Pfp.Assembly`. The evaluation itself factors once
more (`DescriptiveComplexity.Problems.Wide.PfpEval`): a **spine** of
checkpoints, one per variable position
(`DescriptiveComplexity.Pfp.EvalPh`/`EvalSite`/`EvalSh`,
`DescriptiveComplexity.Pfp.PfpData.evalRule`/`evalSep`/`evalHosrc`), each
walking back to the marker and dispatching into that variable's machinery –
the last into the outer boundary pair, erasing the marker towards the
advance or the post-sweep reset – around per-variable sub-machineries that
stay abstract in turn. One variable's machinery
(`DescriptiveComplexity.Problems.Wide.PfpVar`) is the next layer: the gates
(abstract, verdict in a control flag), the junk path writing `False`
directly, and the VAL loop – clear, matrix (abstract), exhaustion test,
block-indexed increment – with the accumulator folds as `dstSt`
*parameters* of the dispatching rules
(`DescriptiveComplexity.Pfp.PfpData.varRule`,
`DescriptiveComplexity.Pfp.PfpData.varSep`), since separation never reads
`dstSt`; their content is fixed with the runs. The recurring
checkpoint-around-stages pattern is a **combinator**
(`DescriptiveComplexity.Problems.Wide.PfpChain`:
`DescriptiveComplexity.Pfp.chainRule`/`chainSep`/`chainHosrc`, dispatches
given as source-phase-less `DescriptiveComplexity.Pfp.PreRule` descriptors,
so loops cost nothing), and the **tuple loop** – the stage atoms' bit-by-bit
block copy, a read trip storing its verdict into the control and a write
trip reading it back, around the loop-variable enumeration – is its first
client (`DescriptiveComplexity.Problems.Wide.PfpTuple`:
`DescriptiveComplexity.Pfp.tupleRule`/`tupleSep`). The read and write trips
gained a stay rule at their start phase for it: every kit is now enterable
by the standard rightward dispatch off the marker. On top of them, the
**stage atom's machinery** – the random access, the largest atom
subroutine – is complete
(`DescriptiveComplexity.Problems.Wide.PfpStageAtom`:
`DescriptiveComplexity.Pfp.PfpData.stageRule`/`stageSep`): save the mirror,
clear and build the target by per-argument tuple loops chained head to
tail, reset–clear–seek out, read the stage bit under the head in the seek's
verdict exits, restore, and reset–clear–seek home. The remaining atom
subroutines are all one shape, the **element loop**
(`DescriptiveComplexity.Problems.Wide.PfpElem`:
`DescriptiveComplexity.Pfp.elemRule`/`elemSep` – leaf reads chained head to
tail, the folds in the checkpoints' `dstSt` parameters, the base-structure
atoms of a leaf evaluated in guards, which see the control), wrapped for
the tag-dependent sentences in the **tag-branched** form
(`DescriptiveComplexity.Problems.Wide.PfpTagged`:
`DescriptiveComplexity.Pfp.tagRule`/`tagSep` – witness reads, an n-ary
branch checkpoint whose dispatches the decoding makes exclusive, one loop
per tag tuple): the expansion atoms at their arity, the domain gates at
one. And the **sequencer**
(`DescriptiveComplexity.Problems.Wide.PfpSeq`:
`DescriptiveComplexity.Pfp.seqRule`/`seqSep`) chains heterogeneous stages –
the matrix's kind-dependent atom machineries, the gates' per-block ones –
behind checkpoints, so the machinery *vocabulary* of the program is now
complete: what remains is instantiation and the runs. The instantiation has
begun: `DescriptiveComplexity.Problems.Wide.PfpRepAtoms` classifies the
atoms of the defining sentences' replicated-block language – base-vocabulary
kinds are guards, the replicated-block kind the read leaves – with the same
capstone (`DescriptiveComplexity.Pfp.realize_iff_qfValue_repHolds`), and
`DescriptiveComplexity.Problems.Wide.PfpTower` assembles the **phase tower**:
per-kind machinery types indexed by the `DescriptiveComplexity.Pfp.MatAtom`
itself (so everything reduces per constructor, the stuck `kindOf`
application confined to the last step), the matrix and gates as sequences,
one variable's machinery, the spine over the enumerated variables, and
`DescriptiveComplexity.Pfp.PfpData.PF` – the program's phase type – with
its site mirror, the owner maps down the tower
(`DescriptiveComplexity.Pfp.PfpData.sfOwn`) and finiteness throughout. The
rule tower has begun: `DescriptiveComplexity.Problems.Wide.PfpKindRule`
dispatches each atom to its kind's machinery behind a **parameter pack**
(`DescriptiveComplexity.Pfp.StageArgs`/`TagArgs`/`ElemArgs` – the matches
and control updates stay packed until the runs, while
`DescriptiveComplexity.Pfp.PfpData.kindSep` closes separation from the
packs alone), and `DescriptiveComplexity.Problems.Wide.PfpVarRule` builds
the matrix (`DescriptiveComplexity.Pfp.PfpData.matrixRule`/`matrixSep`, the
sequencer over the classified atoms) and the gates
(`DescriptiveComplexity.Pfp.PfpData.gatesRule`/`gatesSep`, per block a
well-shapedness test whose failing exit clears the verdict flag and whose
passing exit runs the tag-branched domain evaluation). Every layer also
carries its **ownership** obligation (`DescriptiveComplexity.Pfp.elemHosrc`
and its siblings up to
`DescriptiveComplexity.Pfp.PfpData.gatesHosrc`): a rule fires from a phase
its own site owns, which is what makes separation compose.
`DescriptiveComplexity.Problems.Wide.PfpProg` closes the shape layer –
one variable's machinery with its gates and matrix plugged in
(`DescriptiveComplexity.Pfp.PfpData.varRuleF`), one copy per enumerated
variable and one for the output
(`DescriptiveComplexity.Pfp.PfpData.smRule`), the spine over them
(`DescriptiveComplexity.Pfp.PfpData.evalRuleF`) and the outer loop around
it, delivering **the program's whole rule set** as one
`DescriptiveComplexity.Pfp.Assembly`
(`DescriptiveComplexity.Pfp.PfpData.progAsm`), whose
`DescriptiveComplexity.Pfp.Assembly.prog` and
`DescriptiveComplexity.Pfp.Assembly.sep` are the program and its
determinism. The semantic content rides in one pack per variable
(`DescriptiveComplexity.Pfp.PfpData.VarArgs`), untouched by separation and
fixed with the runs.
`DescriptiveComplexity.Problems.Wide.PfpRun` begins the
runs: the program's rules **are** its kits' rules (one `rfl` per call site,
`DescriptiveComplexity.Pfp.PfpData.prog_rules_seek1` and its siblings), a rule
of the assembly drives a step at its own destination data
(`DescriptiveComplexity.Pfp.PfpData.prog_hasRight`/`prog_hasLeft`), the
initial tape is the empty state's background
(`DescriptiveComplexity.Pfp.PfpData.initBack_eq_back`, the joint between the
input channel's marks and the presentation every pass walks), and the first
leg is proved – `DescriptiveComplexity.Pfp.PfpData.step_start`, planting the
marker and the bottom mark at the empty address. The glue between legs is
`DescriptiveComplexity.Pfp.PfpData.trackTape_back`: a pass's presentation
*is* the background it walks, so one leg's conclusion is the next's
hypothesis whichever track each walks
(`DescriptiveComplexity.Pfp.PfpData.trackTape_back_swap`). With it the
next legs follow: `DescriptiveComplexity.Pfp.PfpData.reaches_tgtTop` (the
round trip writing the logical top into TARGET) and
`DescriptiveComplexity.Pfp.PfpData.reaches_seek1` (the random access taking
the working cell there, the target address strictly below the file because
the least element carries no argument block –
`DescriptiveComplexity.Pfp.tagBlk_eq_none_of_least`), with the two single
steps that bracket a loop head (an exit steps right off the marker, the
head's stay rule walks back). Then the reset takes the marker home
(`DescriptiveComplexity.Pfp.PfpData.reaches_reset1`, whose one hypothesis
beyond the slot equations is the seek's own erasing exit – it plants the
permanent `ltp` end marker there) and a clear empties the mirror
(`DescriptiveComplexity.Pfp.PfpData.reaches_clearMir1`). All of it chains
into **`DescriptiveComplexity.Pfp.PfpData.reaches_startup`**: from the
initial configuration – the marks over the blank – to the entry of the
per-address evaluation, with both permanent markers planted and every
register where the loop expects it. The outer loop's other legs are built
too: the two **plain sweeps** –
`DescriptiveComplexity.Pfp.PfpData.reaches_compare` (the verdict
accumulated in the phase by `DescriptiveComplexity.sweepState`, its per-cell
question read off the stage tracks) and
`DescriptiveComplexity.Pfp.PfpData.reaches_copy` (the background a family
indexed by the sweep's frontier: the addresses already passed hold the next
stage) – the three walks home
(`DescriptiveComplexity.Pfp.PfpData.reaches_home` and its three instances)
and **one round of the outer sweep**
(`DescriptiveComplexity.Pfp.PfpData.reaches_sweepAdv`: the marker and the
mirror step on in lockstep, the erasing entry being the caller's rule, as
the reset's is). Every kit the outer program instantiates has now been
driven at the program level; what the loop still waits on is the
per-address evaluation between two rounds. Its first brick is in
`DescriptiveComplexity.Problems.Wide.PfpBack`: the permanent marks read back
at a register cell (the existential collapses by injectivity of
`DescriptiveComplexity.wmSeg`), and with them the **navigation by name** –
`DescriptiveComplexity.Pfp.PfpData.nameG_wmSeg` says what the guard sees,
`nameG_unique` that it stops at one cell, `not_nameG_of_not_reg` that it
never stops in the working area. The other half of that instantiation is the
control's **dictionary**, `DescriptiveComplexity.Problems.Wide.PfpCtl`:
which `DescriptiveComplexity.Pfp.Ctl` slot plays which role – the loop
element's coordinates, the inner fold's accumulators, a sub-fold's, the
atoms' verdicts, the leaf-read and tag-witness flags, the gates' verdict –
with the casts through the computed budgets, their distinctness, and the
two operations every semantic parameter is built from
(`DescriptiveComplexity.Pfp.PfpData.ctlBit`/`setCtl` and their read-back
equations) – together with the **tuple enumeration** the element loops run
on: `DescriptiveComplexity.Pfp.IsMaxTup`,
`DescriptiveComplexity.Pfp.tupNext` and
`DescriptiveComplexity.Pfp.botTup` are the functions behind the relation
`DescriptiveComplexity.TupSucc` that
`DescriptiveComplexity.Pfp.reflTransGen_of_tupLoop` indexes its rounds by,
and `DescriptiveComplexity.Pfp.PfpData.readLv`/`putLv` are how a round's
tuple is read out of the control and written back.

What a leaf of those loops actually reads is fixed in
`DescriptiveComplexity.Problems.Wide.PfpName`: an encoded tuple is
canonically padded, so it lives in a cell the marks name
(`DescriptiveComplexity.Pfp.PfpData.encTup_isPad`); the trip's guard – the
name guard at *computed* coordinates,
`DescriptiveComplexity.Pfp.PfpData.nameGF` – holds at exactly that cell
(`encG_iff`); and the register digit found there is one membership question
of the block value, hence **one bit of the assignment** of the point the
block holds (`blk_encAsgTup_iff`) or its **tag test**
(`blk_encTagTup_iff`). That is the whole interface between the machine and
`DescriptiveComplexity.Pfp.encPt`.

And `DescriptiveComplexity.Problems.Wide.PfpPad` settles the arithmetic of
the inner loop's levels: the VAL register has one block per level of the
*longest* pack and its enumeration plays all of them, so the machine plays a
prefix too long at both ends – below, the levels the matrix reads off the
working address; above, the levels nothing reads. Neither matters, because a
level whose matrix ignores it may be skipped over a nonempty domain
(`DescriptiveComplexity.Pfp.altQuantFrom_skip`), a prefix over more
coordinates than its matrix reads plays as its restriction
(`altQuantFrom_pad`), and a matrix may be changed anywhere the walk cannot
reach (`altQuantFrom_congr_mat`).

With them, `DescriptiveComplexity.Problems.Wide.PfpLeaf` says **what the
inner loop computes**. The dictionary is fixed there: level `j` of a
variable's pack is inner block `j` of the register, the free levels reading
the working address's outer blocks instead
(`DescriptiveComplexity.Pfp.PfpData.levelVal`), and the leaf is the gated
matrix at that valuation (`leafP` – the encodings' gates belong to the leaf,
not to the loop). `DescriptiveComplexity.Pfp.PfpData.altQuantFrom_leafP` is
the join: the prefix of the leaf over *every* block, played from level `0`,
**is** `DescriptiveComplexity.StepDef.next` at the points the working
address encodes; and `foldFrom_leafP_top` reads that off the accumulators at
the address the loop stops at, the inner top.

The **element loops** of the atom subroutines have the same anchor one scale
down, `DescriptiveComplexity.Problems.Wide.PfpExp`: an atom of the expansion
holds of a tuple of points exactly when the prefix of
`DescriptiveComplexity.Pfp.PfpData.expLeaf` – the Boolean value of the
defining sentence's matrix, its block atoms read off the argument points'
assignments and its base atoms decided by guards – is played from level `0`
(`relMap_iff_altQuantFrom_expLeaf`, and `_pad` for the loop the machine
actually runs, over every loop-variable slot). The classifier it reads that
matrix through is now stated at an **arbitrary block**
(`DescriptiveComplexity.Pfp.BlkAtom` in
`DescriptiveComplexity.Problems.Wide.PfpRepAtoms`), so the same lemmas serve
the replicated block of a defining sentence and the plain block of a domain
sentence.

**Not proved**: hardness. Completeness for these two classes needs the machine
written in logic, as `DescriptiveComplexity.ATMAcceptSpace` needed for EXPTIME:
a reduction cannot be routed through the outer composition of an interpretation
with an expansion, which does not exist in general. The plan is `EXPONENTIAL.md`
§6.4.4 – for EXPSPACE, a roaming program with the register file above that
iterates a partial fixed point over the expansion until it stabilizes; for
NEXPTIME, the harder one-pass sweep that folds a fixed prenex kernel with the
valuation as its head position.
-/
