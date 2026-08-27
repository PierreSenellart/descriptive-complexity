/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime.Fields
import DescriptiveComplexity.LogTime.Pow
import DescriptiveComplexity.LogTime.Small
import DescriptiveComplexity.LogTime.Translate
import DescriptiveComplexity.LogTime.BitSum.Sizes
import DescriptiveComplexity.LogTime.BitSum.Blocks
import DescriptiveComplexity.LogTime.BitSum.Counter
import DescriptiveComplexity.LogTime.BitSum.Ones
import DescriptiveComplexity.LogTime.BitSum.Table
import DescriptiveComplexity.LogTime.BitSum.Sum
import DescriptiveComplexity.LogTime.BitSum.Level2
import DescriptiveComplexity.LogTime.BitSum.Level1
import DescriptiveComplexity.LogTime.BitSum.Columns
import DescriptiveComplexity.LogTime.BitSum.Times
import DescriptiveComplexity.LogTime.Compile
import DescriptiveComplexity.LogTime.Simulate
import DescriptiveComplexity.HeadEvalArith
import DescriptiveComplexity.HeadEvalBit

/-!
# A machine model at the bottom of the ladder: the logarithmic-time hierarchy

Every class of this library above the bottom has its machine model *proved*
equal to the logic that defines it – `LOGSPACE` its multi-head automaton, `NL`
its nondeterministic one, `PTIME` its program. This module gives AC⁰ one too,
in the shape the classical theory prescribes for the logarithmic-time hierarchy
([Sipser 1983][sipser1983borel]; [Barrington, Immerman & Straubing
1990][barrington1990uniformity]), and proves it equal to a logic – to
`FO(≤, BIT)`, which is the classical logic for AC⁰ – and, through both halves
of Immerman's Thm 1.17, to `DescriptiveComplexity.AC0Definable` itself: the
machine model **is** AC⁰.

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

prenex `FO(≤, +, BIT)`  =  constant-alternation logarithmic time,

which is `DescriptiveComplexity.ltDecidable_iff_bitDefinable`: **the machine
model is exactly a logic**, and – since `+` is a derived predicate here
(`DescriptiveComplexity.bitDef_plus_free`) and `≤` is itself definable from `BIT`
alone ([Dawar, Doets, Lindell & Weinstein 1998][dawar1998finiteranks]; not proved
here) – exactly the logic `FO(≤, BIT)` whose identification with
`FO(≤, +, ×)` and with (DLOGTIME-uniform) AC⁰ is [Immerman
1999][immerman1999descriptive] Thm 1.17 and [Barrington, Immerman & Straubing
1990][barrington1990uniformity]. In textbook form the two halves of the
characterization are [Vollmer 1999][vollmer1999introduction] Cor 4.32
(logtime-uniform AC⁰ is logarithmic time with constant alternation) and
Thm 4.73 (`FO[<, BIT]` is logtime-uniform AC⁰, through Lemma 4.72, the
simulation of a logarithmic-time machine by a sentence); his Lemma 4.71, the
bit count of a `log n`-bit number in `FO[<, BIT]`, is what
`DescriptiveComplexity.LogTime.BitSum` builds.

**Alternation is constant here, and has to be.** A machine fixes its register
list and the polarity of each register, so the number of alternations is a
constant of the machine and the class is the union `⋃ₖ Σₖ-TIME(log n)` of the
logarithmic-time hierarchy – which is what AC⁰ is. Logarithmic time with
*unbounded* alternation, the class usually called ALOGTIME, is
(DLOGTIME-uniform) NC¹ ([Ruzzo 1981][ruzzo1981uniform]) and is strictly larger:
PARITY lies in it and not in AC⁰ ([Furst, Saxe & Sipser 1984][furst1984parity];
[Håstad 1986][hastad1986almost]; by the polynomial method, [Vollmer
1999][vollmer1999introduction] §3.3). Nothing in this module bears on that class.

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
first-order in `FO(≤, +, ×)` outright (`DescriptiveComplexity.arithDef_bit`), but
it cannot be used for a machine, and the reason is worth keeping:

> With a base of sweeps and a place-value bit atom, every atom is a **regular**
> relation of the registers' bit tracks read in parallel, alternating registers
> are projections and complements, and the whole model collapses to what a finite
> automaton reading `Nat.card A` in binary can decide. Such a model cannot
> multiply, and does not contain AC⁰: “the universe has a prime number of
> elements” is `FO(≤, +, ×)` – try all pairs of divisors – and is not a
> 2-automatic set of cardinalities.

Reading a bit at a *guessed index* is exactly what escapes that: it is not a
regular relation of the tracks, and it is what a random-access machine does. The
price is paid on the other side, in `DescriptiveComplexity.powArithDef`, and it
is paid in full.

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

**`LTDecidable = AC⁰`, outright**
(`DescriptiveComplexity.ac0Definable_iff_ltDecidable`): the logic of this
module *equals* `DescriptiveComplexity.AC0Definable` – `FO(≤, +, BIT)` equals
`FO(≤, +, ×)`, which is the whole of [Immerman
1999][immerman1999descriptive] Thm 1.17, a statement about two vocabularies and
not about the machine (and one the circuit-complexity literature takes on
trust: [Vollmer 1999][vollmer1999introduction] p. 163 cites a 1994 e-mail of
Lindell for it):

* **`⊆`** is `DescriptiveComplexity.powArithDef`, the definability of `i ↦ 2 ^ i`
  in `FO(≤, +, ×)` (Thm 1.17(2)), proved in `DescriptiveComplexity.LogTime.Pow`
  by a packing argument on the doubling chain of `i`: two guessed elements, the
  chain below the top and its exponents packed into the fields the chain
  delimits.
* **`⊇`** is `DescriptiveComplexity.AC0Definable.ltDecidable`:
  `DescriptiveComplexity.LogTime.Translate` translates a whole `FO(≤, +, ×)`
  formula atom by atom, and the one atom the bit logic does not have as a
  primitive – `DescriptiveComplexity.TimesBitDef`, the bit-definability of
  `orank x * orank y = orank z` – is Thm 1.17(1) whole, proved in
  `DescriptiveComplexity.LogTime.BitSum`: the **Bit Sum Lemma**
  (`DescriptiveComplexity.BitSum.PopAll`, three nested packings of running
  sums, based on a guessed table indexed by the value of a doubly logarithmic
  word) and, over it, the schoolbook columns of the product, each block of
  columns added by a **guessed carry chain** packed into one element
  (`DescriptiveComplexity.BitSum.RangeSum`,
  `DescriptiveComplexity.BitSum.timesCert_iff`). The counting is in a
  *formula*, not in a machine; the base never has to multiply.

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
(`DescriptiveComplexity.LogTime.BitLogic`), with the naming bridge
`DescriptiveComplexity.powArithDef` (`DescriptiveComplexity.LogTime.Pow`) and
the converse translation
`DescriptiveComplexity.ac0Definable_iff_ltDecidable`
(`DescriptiveComplexity.LogTime.Translate`). -/

end DescriptiveComplexity
