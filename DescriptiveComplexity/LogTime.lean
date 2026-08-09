/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime.Fields
import DescriptiveComplexity.LogTime.Compile
import DescriptiveComplexity.LogTime.Simulate
import DescriptiveComplexity.HeadEvalArith
import DescriptiveComplexity.HeadEvalBit

/-!
# A machine model at the bottom of the ladder: alternating logarithmic time

Every class of this library above the bottom has its machine model *proved*
equal to the logic that defines it – `LOGSPACE` its multi-head automaton, `NL`
its nondeterministic one, `PTIME` its program. AC⁰ had nothing. This module
gives it a machine, in the shape the classical theory prescribes for the
logarithmic-time hierarchy (Sipser 1983; [Barrington, Immerman & Straubing
1990][barrington1990uniformity]), and proves it equal to a logic – to
`FO(≤, BIT)`, which is the classical logic for AC⁰.

## The model

`DescriptiveComplexity.LTMachine`: a list of registers, each filled by one of
the two players (so an alternation is a change of polarity along the list), and
a deterministic base test of the tuple they leave behind. A register holds an
element of the universe – an address of `posCount A ≈ log n` bits – so filling
one is the logarithmic block of guesses of the classical `Σₖ-TIME(log n)` normal
form. The base test is a Boolean combination of

* **queries** – an input relation at a tuple of registers, which is the random
  access to the *instance* and needs no index tape here: reading the input at an
  address *is* evaluating a relation at a tuple;
* **reads** – `DescriptiveComplexity.BaseTest.bit`, the bit of one register at
  the position named by another, which is the random access to the machine's own
  *addresses*; and
* **sweeps** – one pass over the bit positions, low to high, by a finite
  automaton reading one bit of each register at each position
  (`DescriptiveComplexity.Sweep`).

Nothing in the base evaluates `≤`, `+` or `×`: that is the point. The bound is a
constant number of passes over a tape of `log n` bits, hence a logarithmic clock
with a constant number of head reversals, plus addressing.

## The characterization

prenex `FO(≤, +, BIT)`  =  alternating logarithmic time,

which is `DescriptiveComplexity.ltDecidable_iff_bitDefinable`: **the machine
model is exactly a logic**, and – since `+` is a derived predicate here
(`DescriptiveComplexity.bitDef_plus_free`) and `≤` is classically derivable from
`BIT` too – exactly the logic `FO(≤, BIT)` whose identification with
`FO(≤, +, ×)` and with (DLOGTIME-uniform) AC⁰ is [Immerman
1999][immerman1999descriptive] Thm 1.17 and [Barrington, Immerman & Straubing
1990][barrington1990uniformity].

## What is proved

* **The arithmetic comes out, bit by bit.**
  `DescriptiveComplexity.leSweep_accepts` and
  `DescriptiveComplexity.plusSweep_accepts`: the comparison and the ripple-carry
  addition are sweeps, so the model computes the numeric predicates `≤` and
  `plus` rather than reading them – the bit-level analogue of what
  `DescriptiveComplexity.HeadArith` does one resource bound higher. Nothing was
  handed to the base but addressing.
* **The logic is inside the model.**
  `DescriptiveComplexity.BitDefinable.ltDecidable`: every prenex sentence over
  the order, the addition and the bit atom is decided by such a machine, atom by
  atom.
* **The model is inside the logic.**
  `DescriptiveComplexity.LTDecidable.bitDefinable`: every problem decided by such
  a machine is defined by a prenex sentence of the *same* logic. The proof is the
  interesting one: a sweep carries a constant number of state bits past each of
  the `log n` positions, so its whole history is a constant number of *bit
  vectors over the positions* – and such a vector is an element of the universe.
  The sentence guesses those elements and pins them with the transition of the
  sweep.

## Why bit positions are named by their index

The bit atom is `DescriptiveComplexity.BitIx`: `BIT(x, i)` with the position
named by the element whose *rank* is the exponent. The alternative – naming a
position by its place value, the element of rank `2 ^ i` – makes the bit atom
first-order in `FO(≤, +, ×)` outright (`DescriptiveComplexity.arithDef_bit`), and
was the earlier design here. It cannot be used for a machine, and the reason is
worth keeping:

> With a base of sweeps and a place-value bit atom, every atom is a **regular**
> relation of the registers' bit tracks read in parallel, alternating registers
> are projections and complements, and the whole model collapses to what a finite
> automaton reading `Nat.card A` in binary can decide. Such a model cannot
> multiply, and does not contain AC⁰: “the universe has a prime number of
> elements” is `FO(≤, +, ×)` – try all pairs of divisors – and is not a
> 2-automatic set of cardinalities.

Reading a bit at a *guessed index* is exactly what escapes that: it is not a
regular relation of the tracks, and it is what a random-access machine does. The
price is paid on the other side, in `DescriptiveComplexity.PowArithDef`.

## Where it lands, and what is not proved

**`LTDecidable ⊆ LOGSPACE`, outright**
(`DescriptiveComplexity.LTDecidable.mem_LOGSPACE`, through
`DescriptiveComplexity.BitDefinable.dtcDefinable` in
`DescriptiveComplexity.HeadEvalBit`): the logic is evaluated by a deterministic
multi-head automaton with `2 * vars + 8` heads, the registers swept, the order
and the input atoms read as guards, the addition and the bit *computed* by
`DescriptiveComplexity.HeadProgram.plusP` and
`DescriptiveComplexity.HeadProgram.bitP`. No part of Immerman's mutual
definability is used on this route.

What is **not** proved is that the logic of this module *is*
`DescriptiveComplexity.AC0Definable`, i.e. `FO(≤, +, BIT) = FO(≤, +, ×)`. That is
a statement about two vocabularies, not about the machine, and it is [Immerman
1999][immerman1999descriptive] Thm 1.17, whose two halves are named here and
neither built:

* **`⊆`** is `DescriptiveComplexity.PowArithDef`, the definability of `i ↦ 2 ^ i`
  in `FO(≤, +, ×)` (Thm 1.17(2), a packing argument on the doubling chain of
  `i`). Everything else in that translation is built, so the AC⁰ reading
  (`DescriptiveComplexity.BitDefinable.ac0Definable`) takes it as a hypothesis.
* **`⊇`** is the Bit Sum Lemma (Thm 1.17(1)): counting the ones of a `log n`-bit
  word by guessing packed running sums, which eliminates `×` in favour of the bit
  atom. The counting it needs is in a *formula*, not in a machine; the base never
  has to multiply.

The bridge does not touch the structures-versus-strings gap either: like
`DescriptiveComplexity.mem_LOGSPACE_iff_automaton`, it relates a logic and a
machine over the *same* structure-based framework.
-/

namespace DescriptiveComplexity

/-! The results of this module are stated where they are proved:
`DescriptiveComplexity.ltDecidable_iff_bitDefinable`
(`DescriptiveComplexity.LogTime.Compile`),
`DescriptiveComplexity.LTDecidable.mem_LOGSPACE`
(`DescriptiveComplexity.HeadEvalBit`) and
`DescriptiveComplexity.BitDefinable.ac0Definable`
(`DescriptiveComplexity.LogTime.BitLogic`). -/

end DescriptiveComplexity
