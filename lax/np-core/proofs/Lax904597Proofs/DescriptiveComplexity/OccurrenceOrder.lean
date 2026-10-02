/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax904597Proofs.DescriptiveComplexity.Problems.Sat
import Mathlib.Data.Set.Finite.Lemmas
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Literal occurrences of a CNF structure, ordered

Semantic layer shared by the reductions *from* SAT (to 3-colorability, to
3SAT…): literal *occurrences* of a `Language.sat`-structure, their traversal
along a linear order of the universe, and the truth of literals and of prefix
disjunctions under an assignment.

An occurrence of a clause `c` is a pair `(x, s)` with `x` an element and
`s : Bool` a sign, such that `x` occurs in `c` with sign `s` (`OccIn`).
Occurrences are ordered lexicographically (variable first, then sign,
`false < true`): `occLt`. On a finite universe every clause with at least one
occurrence has a first (`MinOcc`) and last (`MaxOcc`) occurrence, and every
occurrence that is not first has an immediate predecessor (`SuccOcc`,
`exists_succOcc`), which is unique in both directions. These are the facts
needed to thread a gadget chain (an OR-gadget chain for 3-colorability, a
clause-splitting chain for 3SAT) along the occurrences of each clause.

For chain-correctness arguments, `LitTrue` states that a literal is true under
an assignment, and `PrefixOr`/`PrefixOrStrict` state that some occurrence of a
clause up to (resp. strictly before) a given position is true; the lemmas
relating them to `MinOcc`/`MaxOcc`/`SuccOcc` implement the usual invariant of
chain constructions.

Everything in this file is first-order definable over
`Language.sat.sum Language.order`; the corresponding formulas and their
realization lemmas are in `Lax904597Proofs.DescriptiveComplexity.OccurrenceFormulas`.
-/

namespace Lax904597Proofs.DescriptiveComplexity

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap Lax904597.Sat.satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap Lax904597.Sat.satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap Lax904597.Sat.satNegIn ![c, x]

section Order

variable [LinearOrder A]

/-! ### Truth of prefix disjunctions -/

variable [Finite A]

end Order

end SatOcc

end Lax904597Proofs.DescriptiveComplexity


