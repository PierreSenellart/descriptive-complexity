/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Game.Hardness

/-!
# GAME, alternating reachability

The PTIME entry the catalog was missing a *non-syntactic* representative of:
`DescriptiveComplexity.GAME` asks whether the existential player wins the
reachability game on an AND/OR graph.

## Where it sits

Read with the universal player removed, the three clauses of
`DescriptiveComplexity.WinsOn` are the three clauses of reachability, so GAME is
`DescriptiveComplexity.REACH` with alternation — one operator more, one class up
(NL to PTIME), the same step `DescriptiveComplexity.QSAT` takes from
`DescriptiveComplexity.SAT`.

## What is proved here

**Membership** (`DescriptiveComplexity.game_mem_PTIME`): the winning set is a
least fixed point, so GAME is FO(LFP) definable and PTIME membership follows
from the library's own translation of FO(LFP) into the Horn fragment. The one
piece of work is that the universal clause — *every* successor wins — is not a
Horn body, and is computed instead by a scan of the linear order, from the
greatest element down; see
`DescriptiveComplexity.Problems.Game.Membership`.

**Hardness** (`DescriptiveComplexity.game_PTIME_hard`): unit propagation *is* a
game. Inside a `Language.sat`-instance, the variables are the existential nodes
and the clauses the universal ones, with a move from a variable to each clause
having it as its positive literal and a move from a clause to each of its
negative literals; a clause with no negative literal is marked as winning
outright — which is exactly why the stuck-universal convention was chosen — and
the goal clauses are the marked starts. The existential player then wins exactly
when some goal clause has all its negative literals forced, which on a Horn
formula is unsatisfiability. So what the game decides is the *complement* of
HORN-SAT, and `DescriptiveComplexity.piP_zero_eq` (polynomial time is closed
under complement) carries hardness back — the same last step
`DescriptiveComplexity.Problems.Cvp.Hardness` takes.
-/
