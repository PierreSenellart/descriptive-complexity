/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Block
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Expansion
import DescriptiveComplexity.Exponential.AddrExp
import DescriptiveComplexity.Exponential.Pull
import DescriptiveComplexity.Exponential.Order
import DescriptiveComplexity.Exponential.OrdFormula
import DescriptiveComplexity.Exponential.OrdExtend
import DescriptiveComplexity.Exponential.TagBits
import DescriptiveComplexity.Exponential.PointGuard
import DescriptiveComplexity.Exponential.Rounds
import DescriptiveComplexity.Exponential.PointAtoms
import DescriptiveComplexity.Exponential.Matrix
import DescriptiveComplexity.Exponential.Peel
import DescriptiveComplexity.Exponential.Translate
import DescriptiveComplexity.Exponential.Increment
import DescriptiveComplexity.Exponential.Trivialize
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.Exponential.Kernel
import DescriptiveComplexity.Exponential.KernelPad
import DescriptiveComplexity.Exponential.KernelArity
import DescriptiveComplexity.Exponential.Free
import DescriptiveComplexity.Exponential.FreeCopy
import DescriptiveComplexity.Exponential.SecondOrderFixedPoint
import DescriptiveComplexity.Exponential.Classes
import DescriptiveComplexity.Exponential.Reach
import DescriptiveComplexity.Exponential.Game
import DescriptiveComplexity.Exponential.GameSO
import DescriptiveComplexity.Exponential.GameNode
import DescriptiveComplexity.Exponential.GamePhase
import DescriptiveComplexity.Exponential.GameMove
import DescriptiveComplexity.Exponential.GameRounds
import DescriptiveComplexity.Exponential.GameKernel
import DescriptiveComplexity.Exponential.GameGraph
import DescriptiveComplexity.Exponential.GameState
import DescriptiveComplexity.Exponential.GameSpec
import DescriptiveComplexity.Exponential.GamePrefix
import DescriptiveComplexity.Exponential.GameNodes
import DescriptiveComplexity.Exponential.GameExp
import DescriptiveComplexity.Exponential.Inclusions
import DescriptiveComplexity.Exponential.PSpaceOn
import DescriptiveComplexity.Exponential.Simulate
import DescriptiveComplexity.Exponential.Gate
import DescriptiveComplexity.Exponential.FreeSpace
import DescriptiveComplexity.Exponential.FreeTime
import DescriptiveComplexity.Exponential.AltQuant
import DescriptiveComplexity.Exponential.BlockClaim
import DescriptiveComplexity.Exponential.GameProgram
import DescriptiveComplexity.Exponential.GameTape
import DescriptiveComplexity.Exponential.GameCtrl
import DescriptiveComplexity.Exponential.GameMachine
import DescriptiveComplexity.Exponential.GameRun
import DescriptiveComplexity.Exponential.GameAsk
import DescriptiveComplexity.Exponential.GameSweep
import DescriptiveComplexity.Exponential.GamePlay
import DescriptiveComplexity.Exponential.GameBack
import DescriptiveComplexity.Exponential.GameAskBack
import DescriptiveComplexity.Exponential.GameInterp
import DescriptiveComplexity.Exponential.GamePlayBack

/-!
# The exponential classes, by expansion

EXPTIME, NEXPTIME and EXPSPACE, defined by reading the polynomial-level logics
over a universe that is one exponential larger.

## The idea in one line

> A **second-order** fixed point is a first-order fixed point **read over a
> structure whose universe is the assignments of a second-order block**.

A block with a variable of arity `a` has `2^(n^a)` assignments on a universe of
size `n`. An **exponential expansion** (`DescriptiveComplexity.ExpExpansion`)
maps a finite ordered `L`-structure `A` to a structure whose universe is a
definable set of tagged block assignments, each relation being defined by a
first-order sentence over the base vocabulary expanded by as many copies of the
block as the symbol has arguments. Reading a class `C` there is the operator
`DescriptiveComplexity.ComplexityClass.exp`, and

```
EXPTIME := SO(≤, LFP)        EXPSPACE := SO(≤, PFP)        NEXPTIME := NP.exp
EXPTIME  = PTIME.exp         EXPSPACE  = PSPACE.exp
```

where the `≤` is the order the expansion's *own sentences* read; it can be
removed from both, the expansion guessing it into its block
(`DescriptiveComplexity.mem_EXPTIME_iff_solfpDefinableFree`,
`DescriptiveComplexity.mem_EXPSPACE_iff_sopfpDefinableFree`). The two
equalities on the second line are theorems
(`DescriptiveComplexity.EXPTIME_eq_PTIME_exp`,
`DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`) that hold because the library
already proves FO(≤, LFP) = PTIME and FO(≤, PFP) = PSPACE: they are those two
capture theorems read on the expanded universe.

No third-order syntax is introduced and none is needed: the expansion has
already made the second-order objects the first-order elements of a new sort,
which is the type-lowering translation of higher-order logic into many-sorted
first-order logic over the power type ([Henkin 1950][henkin1950completeness]).

## What the design buys

`exp` is an operator on an **abstract**
`DescriptiveComplexity.ComplexityClass`, so the structural results transfer
instead of being reproved:

* `DescriptiveComplexity.ComplexityClass.exp_compl` carries closure under
  complement one exponential up, whence `EXPTIME = coEXPTIME` from
  `DescriptiveComplexity.piP_zero_eq` and `EXPSPACE = coEXPSPACE` from
  `DescriptiveComplexity.PSPACE_eq_coPSPACE` – two facts that each cost a large
  development, and neither is spent twice;
* `DescriptiveComplexity.ComplexityClass.exp_mono` carries every
  polynomial-level inclusion, whence `EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE` and
  `EXPTIME ⊆ EXPSPACE` (which reads, on the definitions, **SO(LFP) ⊆
  SO(PFP)**).

The same construction one operator up is `DescriptiveComplexity.Exponential.Game`:
a **second-order alternating game** — four first-order sentences over a block,
saying which assignments are universal, which win outright, which start and
which moves are legal — is the AND/OR graph `DescriptiveComplexity.GAME` reads
on the expansion whose points are its states, whence
`DescriptiveComplexity.SOGameDefinable.mem_EXPTIME`: **SO-GAME ⊆ SO(LFP)**, the
second-order shadow of `GAME ∈ PTIME`. It is the way into EXPTIME that needs no
succinctness argument, and what an alternating space-bounded machine will
consume — its configurations being the assignments of a block with one variable
for the state, one for the head and one for the tape.

Two normal forms prepare the machine that will consume it, by giving a
*finite control* everything it needs to decide a fixed first-order sentence:
`DescriptiveComplexity.exists_altQuant` turns a sentence into an **alternating
quantifier prefix**, played one variable at a time – a phase index and a tuple,
one coordinate written per step – over a quantifier-free matrix, and
`DescriptiveComplexity.exists_blockClaims` turns that matrix into a **base
formula determined by the claimed truth values of finitely many block atoms**
(`DescriptiveComplexity.BlockAtom`: a copy, a relation variable, and where its
arguments sit among the matrix's variables). Together they say that a
specification's sentences need no evaluator: the prefix is moves, the claims
are one nondeterministic move and finitely many tape lookups, and what is left
is a condition on the source structure, i.e. a guard of the transition
relation. `DescriptiveComplexity.exists_questionData` packages the composite as
the interface such a machine consumes, for each of the six questions
(`DescriptiveComplexity.GameQuestion`) it has to answer – the four sentences of
the specification and the two negations, all read in the same two-copy
language. `DescriptiveComplexity.Exponential.GameTape` then lays out the tape
such a machine runs on – two sentinels, one cell per atom of each of two
regions, a right sentinel, ordered by
`DescriptiveComplexity.TapeTag.fam` and then lexicographically – and identifies
a tape with the *pair of block assignments* it holds
(`DescriptiveComplexity.assignOfTape_tapeOfAssign`) – a cell carrying its own
address, so that the machine never has to know where its head is.
`DescriptiveComplexity.Exponential.GameCtrl` fixes the control: the phases
(`DescriptiveComplexity.MachPh`) and which player owns each
(`DescriptiveComplexity.MachPh.IsUniv`), and
`DescriptiveComplexity.Exponential.GameMachine` assembles the
`DescriptiveComplexity.ATMData` itself, with its rules as a parameter – the two
promises `DescriptiveComplexity.ATMAcceptSpace` folds into its yes-instances
being independent of them
(`DescriptiveComplexity.gameMachine_wellFormed`,
`DescriptiveComplexity.gameMachine_blocksSplit`). Its three walks are run in
the same file – `DescriptiveComplexity.sweep_run` writes a guessed assignment
into a region, `DescriptiveComplexity.rewind_run` brings the head back to the
lowest position and hands over, `DescriptiveComplexity.seek_run` either meets
the cell a challenged claim addresses or reaches the end of the tape having
found none – and `DescriptiveComplexity.Exponential.GameRun` says what it is to
sit at a phase of the control (`DescriptiveComplexity.CtrlCfg`), building a
step of the control graph and, for the universal phases, reading every step
back as one. On that, `DescriptiveComplexity.GameProg.altWin_ask`: **if a
question holds of the two assignments the tape carries, the machine wins from
the entry of its prefix** – the prefix played one variable at a time, the
matrix claimed in one move and settled by a challenge round, and no evaluator
anywhere. `DescriptiveComplexity.Exponential.GameSweep` does the same for the
other half of a move: a sweep is read back at the level of configurations
(`DescriptiveComplexity.sweepCfg_cases`), the invariant being *the tape holds
some pair of assignments agreeing with the original outside the region being
written* – so a half-finished sweep is again a tape, and the universal player's
sweep is answered for every assignment of that region
(`DescriptiveComplexity.altWin_sweep_all`). On those two,
`DescriptiveComplexity.Exponential.GamePlay` runs the **forward simulation**:
one clause of `DescriptiveComplexity.SOGameSpec.Wins` at a time, a winning
state of the game is a winning configuration of the machine
(`DescriptiveComplexity.altWin_play`), and the machine accepts whenever the
game does (`DescriptiveComplexity.altAcceptsSpace_of_accepts`) – the starting
position being *guessed* by the very first sweep, since the initial tape is
empty. `DescriptiveComplexity.Exponential.GameBack` begins the converse, where
the two players exchange roles: an existential phase has to be case-analysed
and a universal one instantiated, so every step lemma is used in the other
direction. Its content is the phases that settle a question –
`DescriptiveComplexity.pre_of_altWin`, `claim_of_altWin`, `check_of_altWin`,
`concOk_of_altWin`, and `seekArrives_of_altWin`, an induction on
`DescriptiveComplexity.ATMData.AltWin` itself along a walk whose phase never
changes. `DescriptiveComplexity.Exponential.GameAskBack` closes that half at the
program: an *arrival* is a correct claim, and
`DescriptiveComplexity.GameProg.ask_of_altWin` is the converse of `altWin_ask` –
**if the machine wins from the entry of a question's prefix, the question
holds**. `DescriptiveComplexity.Exponential.GamePlayBack` closes the
simulation: one induction whose motive has a clause per phase of the game, with
the universal sweep followed *forward* along a chain the motive quantifies over,
giving `DescriptiveComplexity.altAcceptsSpace_iff_accepts` – **the machine
accepts exactly when the game does**. `DescriptiveComplexity.Exponential.GameInterp`
writes that machine *down*: every relation of the alternating vocabulary is a
first-order formula of the ordered source, so the interpretation is an ordinary
(not relativized) one – the junk tuples are excluded by `Posn`, a relation, and
not by the universe. That is
`DescriptiveComplexity.atmAcceptSpace_EXPTIME_hard` and, with the membership
half, `DescriptiveComplexity.atmAcceptSpace_EXPTIME_complete`: **`APSPACE =
EXPTIME`**, an alternating machine given as much space as its input has
positions decides exactly deterministic exponential time.

The one inclusion with content is `DescriptiveComplexity.PSPACE_subset_EXPTIME`:
an `DescriptiveComplexity.SOTCSpec` *is* the graph REACH reads on the expansion
whose points are its states, so SO(TC) ⊆ SO(LFP) – the second-order shadow of
`NL ⊆ PTIME`. It also gives `PSPACE ⊆ NL.exp`, and `NL.exp ⊆ EXPTIME` comes
back by monotonicity.

## The expanded universe is ordered, definably

An expansion's own universe carries a linear order — tag first, then the
assignment read as a **binary number**, `ρ` below `σ` at the least atom where
they differ (`DescriptiveComplexity.ExpExpansion.mapLinearOrder`) — and that
order is itself **first-order definable over the base**
(`DescriptiveComplexity.SOBlock.realize_ordLtF`), because a padded atom is one
of finitely many relation variables together with a tuple of *base* elements.
`DescriptiveComplexity.ExpExpansion.ordExtend` adds the order symbol to the
expanded vocabulary and defines it that way, exactly as
`DescriptiveComplexity.FOInterpretation.ordExtend` does one level down.

This is what any composition reading an expansion's order needs. It is not by
itself enough for such a composition: an interpretation's *quantifiers* range
over the points of the expanded universe, hence over block assignments, which
is a second-order condition over the base — see `ROADMAP.md` §3.

## The translation lemma

**An FO sentence over an expansion is a second-order sentence over the base**
(`DescriptiveComplexity.ExpExpansion.exists_translate`): a quantifier ranging
over the points of `X.Map A` ranges over block assignments, which is a
second-order quantifier over `A`. That is the type-lowering reading of
[Henkin 1950][henkin1950completeness] made into a theorem, and the honest
statement of what keeps an interpretation from being composed *after* an
expansion (`ROADMAP.md` §3).

A quantified point is a block extended by tag bits
(`DescriptiveComplexity.SOBlock.withTag`) satisfying a guard
(`DescriptiveComplexity.ExpExpansion.pointGuardF`); the expansion's own
sentences are read at chosen rounds of the prefix
(`DescriptiveComplexity.ExpExpansion.roundLHom`); the three atoms and the
quantifier-free matrix translate
(`DescriptiveComplexity.ExpExpansion.realize_translQF`); and one quantifier
peels into two blocks — one `∃`, one `∀`, of which one is real and the other
vacuous, so that the prefix alternates strictly as
`DescriptiveComplexity.SORealize` requires
(`DescriptiveComplexity.ExpExpansion.altBlockQuant_peel_step`). The assembly is
an induction on the `FirstOrder.Language.BoundedFormula.IsPrenex` proof, with
the translated sentence produced *existentially*: the inequalities bounding the
rounds a subformula needs are then in scope exactly where its round indices are
built, so no fallback round and no cast appears anywhere.

## The gate: `PSPACE = NL.exp`

`DescriptiveComplexity.PSPACE_eq_NL_exp` pins the operator at the one level
where the library independently knows the answer, in **both** directions:
polynomial space *is* nondeterministic logarithmic space read one exponential
up. The easy half is `DescriptiveComplexity.PSPACE_subset_NL_exp` above; the
converse (`DescriptiveComplexity.NL_exp_subset_PSPACE`) goes through the
*machine* model of FO(TC) (`DescriptiveComplexity.tcDefinable_iff_automaton`),
whose tests are quantifier-free by fiat, so that
`DescriptiveComplexity.ExpExpansion.translQF` translates them as they stand and
no quantifier over the expanded universe is ever evaluated. Three steps: the
walk is carried to the **trivialized** expansion (`Exponential.Trivialize`),
where every tagged assignment is a point and a head's `succ` is the plain binary
increment (`Exponential.Increment`); the carried walk is compiled into a two-way
multi-head automaton; and that automaton is simulated by an
`DescriptiveComplexity.SOTCSpec` over the base
(`DescriptiveComplexity.ExpExpansion.autoSpec`), a configuration — a control
state and `k` points — being one assignment of one block.

`LOGSPACE.exp ⊆ PSPACE` follows by monotonicity; the reverse inclusion is not
claimed, since the graph a walk draws is asked REACH of, and REACH is not known
here to be in `DescriptiveComplexity.LOGSPACE`.

The other bound from above is the one nothing else tests
(`DescriptiveComplexity.ExpExpansion.mem_PSPACE_of_fo_on_expansion`): **every
first-order property of an exponential expansion is in `PH`, hence in
`PSPACE`**. Everything else proved here validates the operator from below
(`PSPACE ⊆ NL.exp ⊆ EXPTIME`).

## Layout

| file | content |
|---|---|
| `Exponential.Block` | `SOBlock.replicate`, commuting with the block pullback |
| `Exponential.Copies` | reading stacked block expansions inside a replicated one |
| `Exponential.Expansion` | `ExpExpansion`, its universe, its expanded structure |
| `Exponential.Pull` | an interpretation followed by an expansion is an expansion |
| `Exponential.Order` | the order on an expanded universe, semantically |
| `Exponential.OrdFormula` | that order as a first-order sentence, and its correctness |
| `Exponential.OrdExtend` | the expansion extended with its own order |
| `Exponential.TagBits` | a tag as arity-0 relation variables, and its guard |
| `Exponential.PointGuard` | the guard saying a guessed block is a point |
| `Exponential.Rounds` | placing an expansion's sentences into a quantifier prefix |
| `Exponential.PointAtoms` | the three atoms a kernel can state about points |
| `Exponential.Matrix` | translating a quantifier-free matrix |
| `Exponential.Peel` | peeling one quantifier into one block |
| `Exponential.Translate` | the translation lemma, by induction on prenex form |
| `Exponential.Increment` | the successor of a point, and the two endpoints of the order |
| `Exponential.Trivialize` | trading an expansion's domain for a mark, walk included |
| `Exponential.Class` | `ExpDefinable`, `ComplexityClass.exp`, `exp_mono`, `exp_compl` |
| `Exponential.Free` | expansions that see no order; the order, guessed into the block |
| `Exponential.FreeCopy` | the copies of an order-guessing expansion, and “some copy answers yes” |
| `Exponential.SecondOrderFixedPoint` | SO(LFP), SO(PFP) and the two bridge theorems |
| `Exponential.Classes` | EXPTIME, NEXPTIME, EXPSPACE and their hardness discharges |
| `Exponential.Reach` | an SO(TC) walk is REACH on an expansion |
| `Exponential.Game` | a second-order alternating game is GAME on an expansion |
| `Exponential.GameSO` | a second-order quantifier prefix, played as a game: `SO ⊆ SO-GAME` |
| `Exponential.GameNode` | the nodes of an interpreted AND/OR graph, as states of a game |
| `Exponential.GamePhase` | the sentences a phased game is made of: phases, and freezing |
| `Exponential.GameMove` | a one-copy sentence read in a copy, and one variable moved onto another |
| `Exponential.GameRounds` | whole rounds kept, overwritten or shifted by a move |
| `Exponential.GameKernel` | a defining formula of an interpretation, as an alternating prefix |
| `Exponential.GameGraph` | the six questions an interpreted AND/OR graph asks, and their kernels |
| `Exponential.GameState` | the phases of the graph game, and what a state of it is |
| `Exponential.GameSpec` | the four sentences of the graph game, and what they say |
| `Exponential.GamePrefix` | the prefix phases play the alternating prefix |
| `Exponential.GameNodes` | the node phases play the interpreted AND/OR graph |
| `Exponential.GameExp` | **EXPTIME = SO-GAME** |
| `Exponential.AltQuant` | a sentence as an alternating prefix over a quantifier-free matrix |
| `Exponential.BlockClaim` | a matrix as a base formula plus claimed block atoms |
| `Exponential.GameProgram` | the six questions a machine playing a game must answer |
| `Exponential.GameTape` | the tape: positions, order, and a tape as a pair of assignments |
| `Exponential.GameCtrl` | its control: the phases, who owns each, and the control graph |
| `Exponential.GameMachine` | the machine itself, its nine rule families and its three walks |
| `Exponential.GameRun` | a configuration of the control, and the steps out of it |
| `Exponential.GameAsk` | asking a question of the machine: the prefix, the claim, the challenge |
| `Exponential.GameSweep` | the sweep read back, and the two sweeps of the game |
| `Exponential.GamePlay` | the machine plays the game: the forward simulation |
| `Exponential.GameBack` | reading a win back: the phases that settle a question |
| `Exponential.GameAskBack` | a question, read back: an arrival is a correct claim |
| `Exponential.GamePlayBack` | the game read back: **acceptance is exactly the game's** |
| `Exponential.GameInterp` | the machine in logic: **APSPACE = EXPTIME** |
| `Exponential.Inclusions` | the complement equalities and the inclusions |
| `Exponential.PSpaceOn` | an FO property of an expansion is in `PH`, hence in `PSPACE` |
| `Exponential.Simulate` | a machine walking an expanded universe, as a walk over the base |
| `Exponential.Gate` | `PSPACE = NL.exp` |
| `Exponential.FreeSpace` | `EXPSPACE = SO(PFP)`: the copy is guessed as a relation |
| `Exponential.FreeTime` | `EXPTIME = SO(LFP)`: the copy is named by a point |

## Literature

The succinctness upgrade is [Galperin–Wigderson 1983][galperin1983succinct],
[Papadimitriou–Yannakakis 1986][papadimitriou1986note] and, in general form,
[Veith 1998][veith1998succinct]. Naming the deterministic classes after their
fixpoint logics follows [Abiteboul–Vardi–Vianu
1997][abiteboul1997fixpoint]; that work is stated in the relational
(order-free, generic) setting, so it is cited here as motivation for the
*names* and never as a capture theorem – SO(LFP) and SO(PFP) are definitions in
this development, and what is proved in their place are the bridge theorems
above. For NEXPTIME the literature's characterization is existential
*third*-order logic ([Leivant 1989][leivant1989descriptive];
[Hella–Turull-Torres 2006][hella2006higher]); this development does not build a
third-order syntax layer and so does not state that equivalence – an honest and
narrow gap, recorded in `DescriptiveComplexity.Exponential.Classes`.
-/
