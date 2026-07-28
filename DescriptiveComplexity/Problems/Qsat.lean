/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Blocks
import DescriptiveComplexity.Problems.Qsat.Complement
import DescriptiveComplexity.Problems.Qsat.Hardness

/-!
# QSAT: quantified Boolean formulas with an unbounded prefix

Umbrella file for `DescriptiveComplexity.QSAT`, the quantified Boolean formula problem
with the quantifier prefix carried by the instance (also known as TQBF): the
canonical PSPACE-complete problem ([Stockmeyer–Meyer
1973][stockmeyer1973word]; [Immerman 1999][immerman1999descriptive]).

Unlike the bounded families `DescriptiveComplexity.QBF k` of
`DescriptiveComplexity.Problems.Qbf`, whose number of alternations is fixed by the
problem, here the prefix is part of the input – a linear order on the marked
variables together with a polarity mark – so one problem carries arbitrarily
many alternations. That is exactly the step from the polynomial hierarchy to
PSPACE.

## The semantics and the membership half

* `DescriptiveComplexity.Problems.Qsat.Defs`: the vocabulary
  `FirstOrder.Language.qsat`, well-formedness `DescriptiveComplexity.QsatWf`, the game
  semantics `DescriptiveComplexity.QsatWins` with its three rules read backwards, and
  the problem `DescriptiveComplexity.QSAT`.
* `DescriptiveComplexity.Problems.Qsat.Membership`: the membership half,
  `DescriptiveComplexity.qsat_sotcDefinable` – the depth-first evaluation of the game
  tree as a walk over four relation variables.
* `DescriptiveComplexity.Problems.Qsat.Blocks`: the block reading of the prefix
  (`DescriptiveComplexity.qsatWins_block_ex`, `DescriptiveComplexity.qsatWins_block_all`), which
  turns the one-variable-at-a-time game into the textbook one quantifier per
  block of like polarity – the form every reduction into QSAT needs.

## The hardness half: Savitch as an interpretation

PSPACE-hardness is a reduction from `DescriptiveComplexity.SUCCINCTREACH` (already
PSPACE-complete, `DescriptiveComplexity.SUCCINCTREACH_PSPACE_complete`) by Savitch's
recursive doubling ([Savitch 1970][savitch1970relationships]), written as an
ordered first-order interpretation of dimension `2`. Its pieces are:

* `DescriptiveComplexity.Savitch` (top level): the recursive doubling itself, for
  an arbitrary relation whose vertices are known up to a classifying map into a
  finite type – `DescriptiveComplexity.SavPow`, and the pigeonhole
  `DescriptiveComplexity.savPow_of_reflTransGen` saying that it *is* reachability;
* `DescriptiveComplexity.Problems.Qsat.Reach`: SUCCINCT-REACH read through it,
  `DescriptiveComplexity.succinctReachable_iff_savPow`;
* `DescriptiveComplexity.Problems.Qsat.Tags`: what the elements of the constructed
  instance are – which propositional variable, which clause, and in which order
  the prefix quantifies them;
* `DescriptiveComplexity.Problems.Qsat.Interp`: the defining formulas and the
  interpretation `DescriptiveComplexity.qsatInterp`;
* `DescriptiveComplexity.Problems.Qsat.Prefix`: the constructed instance is well
  formed (`DescriptiveComplexity.qsatWf_qsatInterp`), and its prefix splits into
  blocks;
* `DescriptiveComplexity.Problems.Qsat.Levels`: the levels of the recursion and the
  ten projections through which the correctness proof reads a valuation;
* `DescriptiveComplexity.Problems.Qsat.Matrix` and
  `DescriptiveComplexity.Problems.Qsat.Parts`: what the matrix says, clause tag by
  clause tag and then as four semantic conditions
  (`DescriptiveComplexity.qsatMatrix_iff_parts`);
* `DescriptiveComplexity.Problems.Qsat.Peel`: the five block transitions of the
  prefix;
* `DescriptiveComplexity.Problems.Qsat.Leaf`: the innermost block, whose three
  auxiliary valuations witness the two endpoint conditions and one move of the
  walk (`DescriptiveComplexity.game_aux`);
* `DescriptiveComplexity.Problems.Qsat.Induction`: playing the three blocks of one
  level is one step of the recursion (`DescriptiveComplexity.game_step`), and
  iterating that down the levels is `DescriptiveComplexity.game_level`;
* `DescriptiveComplexity.Problems.Qsat.Hardness`: correctness
  (`DescriptiveComplexity.qsatHolds_iff`) and the reduction
  `DescriptiveComplexity.succinctReach_ordered_fo_reduction_qsat`.

## The complement

The evaluation walk of the membership half is *deterministic*: it does not
search for an accepting computation, it computes the value of the formula. So
reading its answer the other way round decides the complement,
`DescriptiveComplexity.Problems.Qsat.Complement`. Together with hardness that is
`PSPACE = coPSPACE` (`DescriptiveComplexity.PSpaceCompl`).
-/

namespace DescriptiveComplexity

/-- **QSAT is in PSPACE**: the depth-first evaluation of the game tree is an
SO(TC) walk. -/
theorem qsat_PSPACE_mem : QSAT ∈ PSPACE :=
  qsat_mem_PSPACE

/-- **QSAT is PSPACE-complete** ([Stockmeyer–Meyer 1973][stockmeyer1973word]):
the canonical complete problem for `DescriptiveComplexity.PSPACE`. -/
theorem qsat_PSPACE_complete : PSPACE.Complete QSAT :=
  QSAT_PSPACE_complete

end DescriptiveComplexity
