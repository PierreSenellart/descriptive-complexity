/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Numbers.Unary
import DescriptiveComplexity.Numbers.Binary
import DescriptiveComplexity.Numbers.Digits
import DescriptiveComplexity.Numbers.Wide

/-!
# Number encodings

Umbrella file for the shared number-representation layer, and the place the
per-problem choice of encoding is argued. Numbers are not a primitive of the
framework: an instance is a finite structure, so a number it carries has to be
read off that structure, and the *semantics* of numbers (sums, comparisons) is
always computed in Lean inside `DecisionProblem.Holds`. What the encoding
constrains is which reductions stay first-order, and whether the problem keeps
its intended complexity.

Two encodings are in use across the catalog, complements rather than rivals:

* **unary**, a number as the *cardinality of a marked set*
  (`DescriptiveComplexity.Numbers.Unary`): order-free, isomorphism-invariant
  for free, quantifier-free, and available at arity 2 as well – the threshold
  as the cardinality of a marked binary relation, which is what objectives
  counting arcs need. The tagged framework does cardinality arithmetic
  natively: disjoint union via tags adds, dimension multiplies, complement
  subtracts. Honest only for numbers that are polynomially bounded – a unary
  SubsetSum is in P, hence not NP-hard.
* **binary**, a number as a set of *bit positions*
  (`DescriptiveComplexity.Numbers.Binary`, with the order as a relation symbol
  of the vocabulary in `DescriptiveComplexity.Numbers.BinRel`, base-`B` digits
  in `DescriptiveComplexity.Numbers.Digits` and wide positions in
  `DescriptiveComplexity.Numbers.Wide`): the universe holds items and
  positions, separated by unary predicates and linearly ordered, and `Holds`
  decodes `∑ 2 ^ i`. The honest encoding for problems whose numbers must be
  exponential in the instance size (Knapsack, Partition, Job Sequencing, 0-1
  Integer Programming), at the price of every reduction into such a problem
  having to construct the order.

Inside formulas, comparison and addition of binary numbers are
FO(≤)-definable, but multiplication is not (it is TC⁰): a reduction into a
binary problem can only write numbers it can define one bit at a time, and an
iterated sum is not one of them. Reductions the other way, from a binary
problem into a unary one, are unproblematic – formulas only ever read bits,
never sum them.

That the choice is part of the statement and not bookkeeping is itself a
theorem: `DescriptiveComplexity.no_unary_encoding`
(`DescriptiveComplexity.Encoding.UnaryBlowup`) shows that no encoding of
subset-sum instances sized by bit length can spend one universe element per
unit of weight, with the binary encoding of the same instances as the positive
contrast.
-/
