/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.Strings.Examples
public import DescriptiveComplexity.Strings.NP
public import DescriptiveComplexity.Strings.PTime

/-!
# The bridge to machine classes on bit strings

The classes of this library are logical, and a decision problem is a property of finite
structures, so that no machine and no string encoding appears in their definitions. This
part of the library compares them with the textbook classes, for `NP` and `PTIME`: over a
vocabulary with finitely many relation symbols
(`DescriptiveComplexity.Strings.FinVocab`),

* `P ∈ NP` exactly when the language of the binary encodings of the yes-instances of `P`
  has polynomially bounded certificates checked in polynomial time by a Mathlib
  `Turing.FinTM2` (`DescriptiveComplexity.Strings.mem_NP_iff_languageInNP`), and
* `P ∈ PTIME` exactly when a polynomial-time `Turing.FinTM2` decides that language
  (`DescriptiveComplexity.Strings.mem_PTIME_iff_inP`).

## What is proved, and what is taken

The archive-side definitions (the encodings, the machine classes, the existential
second-order logic, and FO(LFP)) are those of two entries of the Lax archive by Szymon
Toruńczyk: [`lax-988886`](https://laxarchive.org/lax-988886/), Fagin's theorem, and
[`lax-751879`](https://laxarchive.org/lax-751879/), the Immerman–Vardi theorem. The directory
`DescriptiveComplexity/Strings/Lax/` mirrors them, with the same names and the same bodies
(`CONTRIBUTING.md` says what may be edited there). Where an entry states a lemma as an axiom
of its concept layer, the mirror proves it; the two capture theorems are the only things left
unproved, and they are hypotheses here
(`DescriptiveComplexity.Strings.Lax.FaginCaptures`,
`DescriptiveComplexity.Strings.Lax.ImmermanVardiCaptures`), not axioms. The library proves
the logical side outright (`DescriptiveComplexity.Strings.mem_NP_iff_definable`,
`DescriptiveComplexity.Strings.mem_PTIME_iff_definable`): the class equals what the entry's
logic defines. A submission to the Lax archive replaces the mirror by the two entries,
which discharges the hypotheses.

No class of the library is redefined, and nothing here acquires an axiom.

## The layout

* `DescriptiveComplexity.Strings.Vocab` and
  `DescriptiveComplexity.Strings.VocabCommand`: numbering the symbols of a vocabulary.
* `DescriptiveComplexity.Strings.Transport`: structures and problems across the two
  formalisms.
* `DescriptiveComplexity.Strings.FirstOrder`: one translation of first-order formulas into
  the syntaxes of the archive and back into a language with more relations.
* `DescriptiveComplexity.Strings.ExistentialSecondOrder` and
  `DescriptiveComplexity.Strings.NP`: `∃SO`, then `NP`.
* `DescriptiveComplexity.Strings.FixedPointForward`: from a simultaneous least fixed point of
  the library to nested ones, by Bekić's principle.
* `DescriptiveComplexity.Strings.Program` and
  `DescriptiveComplexity.Strings.FixedPointBackward`: from nested and negated fixed points to
  one inflationary induction.
* `DescriptiveComplexity.Strings.PTime`: `PTIME`.
* `DescriptiveComplexity.Strings.Examples`: some problems of the catalog, on bit strings.
-/
