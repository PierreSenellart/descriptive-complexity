/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime.Compile
import DescriptiveComplexity.LogTime.Simulate
import DescriptiveComplexity.HeadEvalArith

/-!
# A machine model at the bottom of the ladder: sweeping logarithmic time

Every class of this library above the bottom has its machine model *proved*
equal to the logic that defines it – `LOGSPACE` its multi-head automaton, `NL`
its nondeterministic one, `PTIME` its program. AC⁰ had nothing. This module
gives it a machine, in the shape the classical theory prescribes for the
logarithmic-time hierarchy (Sipser 1983; [Barrington, Immerman & Straubing
1990][barrington1990uniformity]), and proves the inclusion that the shape makes
provable.

## The model

`DescriptiveComplexity.LTMachine`: a list of registers, each filled by one of
the two players (so an alternation is a change of polarity along the list), and
a deterministic base test of the tuple they leave behind. A register holds an
element of the universe – an address of `posCount A ≈ log n` bits – so filling
one is the logarithmic block of guesses of the classical `Σₖ-TIME(log n)` normal
form. The base test is a Boolean combination of

* **queries** – an input relation at a tuple of registers, which is the random
  access of the model and needs no index tape here: reading the input at an
  address *is* evaluating a relation at a tuple; and
* **sweeps** – one pass over the bit positions, low to high, by a finite
  automaton reading one bit of each register at each position
  (`DescriptiveComplexity.Sweep`).

Nothing in the base evaluates `≤`, `+` or `×`: that is the point. The bound is a
constant number of passes over a tape of `log n` bits, hence a logarithmic clock
with a constant number of head reversals.

## The sandwich

`FO(≤, +, BIT)` in prenex form  ⊆  sweeping logarithmic time  ⊆  `FO(≤, +, ×)`.

Both fences are proved (`DescriptiveComplexity.BitDefinable.ltDecidable` and
`DescriptiveComplexity.LTDecidable.ac0Definable`), and the gap between them is
named rather than hidden: it is Immerman's mutual definability, of which the
library has `BIT` from `+, ×` (`DescriptiveComplexity.arithDef_bit`) and not
`×` from `BIT`.

## What is proved

* **The arithmetic comes out, bit by bit.**
  `DescriptiveComplexity.leSweep_accepts` and
  `DescriptiveComplexity.plusSweep_accepts`: the comparison and the ripple-carry
  addition are sweeps, so the model computes the numeric predicates `≤` and
  `plus` rather than reading them – the bit-level analogue of what
  `DescriptiveComplexity.HeadArith` does one resource bound higher.
* **The logic is inside the model.**
  `DescriptiveComplexity.BitDefinable.ltDecidable`: every prenex sentence over
  the order, the addition and a *guarded* bit atom (`p` is a position and the
  bit of `x` there is set) is decided by such a machine, atom by atom – the
  guard is what keeps `BIT` bit-level, since for a `p` that is not a place value
  `DescriptiveComplexity.BitAt` is a condition modulo `2p`, which no sweep
  decides.
* **The model is inside the logic.**
  `DescriptiveComplexity.LTDecidable.ac0Definable`: every problem decided by
  such a machine is AC⁰ definable, hence
  (`DescriptiveComplexity.LTDecidable.mem_LOGSPACE`) in LOGSPACE. The proof is
  the interesting one: a sweep carries a constant number of state bits past each
  of the `log n` positions, so its whole history is a constant number of *bit
  vectors over the positions* – and such a vector is an element of the universe.
  The sentence guesses those elements and pins them with the transition of the
  sweep, using the bit predicate `DescriptiveComplexity.BitAt`, which is itself
  first-order in `≤`, `+` and `×` once positions are named by their place values
  (`DescriptiveComplexity.LogTime.Bits`).

## What is not proved, and why

That every AC⁰ definable problem is decided by such a machine – equivalently,
that the sandwich collapses – is **open here, and not for want of
engineering**. A sweep passes a constant
number of bits across each position; multiplication of two `log n`-bit numbers
accumulates a column count that grows with the number of positions, so `×` is
not a constant number of sweeps. Lifting the restriction is no help either: a
base that revisits its positions unboundedly often (a machine that *counts*)
leaves the budget the simulation above lives on, and simulating it in the logic
is exactly the hard half of the classical `AC⁰ = LH` theorem. The honest
statement is therefore a sandwich that does not collapse, with the missing step
named: `×` from `BIT`, and a prenex normal form for `BoundedFormula`.

The bridge does not touch the structures-versus-strings gap either: like
`DescriptiveComplexity.mem_LOGSPACE_iff_automaton`, it relates a logic and a
machine over the *same* structure-based framework.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Sweeping logarithmic time is inside LOGSPACE**, through AC⁰ and the
arithmetic head programs of `DescriptiveComplexity.HeadEvalArith`. -/
theorem LTDecidable.mem_LOGSPACE {P : DecisionProblem L} (h : LTDecidable P) :
    P ∈ LOGSPACE :=
  ac0Definable_mem_LOGSPACE h.ac0Definable

/-- **A bit-definable problem is in LOGSPACE**, through the machine and AC⁰. -/
theorem BitDefinable.mem_LOGSPACE {P : DecisionProblem L} (h : BitDefinable P) :
    P ∈ LOGSPACE :=
  h.ltDecidable.mem_LOGSPACE

end DescriptiveComplexity
