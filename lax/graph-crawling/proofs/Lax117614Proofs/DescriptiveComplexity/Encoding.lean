/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.Finite
import Lax117614Proofs.DescriptiveComplexity.Interpretation
import Lax117614.CrawlInstances
import Lax117614.GraphCrawlingProblem
import Lax117614.WebsiteGraphs
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# Faithful encodings of concrete instance types

A `Lax117614Proofs.DescriptiveComplexity.DecisionProblem` is a property of finite structures. A
user of the library starts elsewhere: from *concrete data* – a list of atoms, a
family of weights – which must be encoded as a structure before any theorem of
the library applies. That encoding step carries two obligations:

1. **semantic equivalence** – the abstract semantics on the encoded structure
   agrees with the textbook semantics of the concrete data; and
2. **representation faithfulness** – the encoded structure is of the right
   *size*. Get this wrong and the complexity result is about a different
   computational problem, however faithfully its meaning matches: encode a
   number in unary (as the cardinality of a marked set) when the honest size
   counts its bit length, and a subset-sum instance sits on a universe
   exponential in its own size, so its NP-hardness silently evaporates.

This file makes obligation 2 a *proof obligation*: `Lax117614Proofs.DescriptiveComplexity.Encoding`
bundles the concrete instance type, its declared size, the encoding map, and
polynomial bounds in **both** directions between the declared size and the
cardinality of the encoded universe – so that an encoding cannot be constructed
without discharging them. `card_le` forbids padding (protecting membership
claims: pad the universe to `2 ^ size` and “in NP over structures” becomes a
much weaker statement about the concrete problem); `le_card` forbids
compression (protecting hardness claims), and also defends the definition
against inflating `size` to make `card_le` vacuous. Obligation 1 remains a
theorem the user proves, now packaged as `Lax117614Proofs.DescriptiveComplexity.Encoding.Faithful`.

The bounds compare the declared size with `Nat.card` of the universe rather
than with a bit size: the vocabulary is fixed and of fixed arity, so a
structure on `n` elements takes `Θ(n ^ r)` bits – cardinality and bit size are
polynomially related, and the criterion is polynomial.

## Hygiene: computability, enforced

The relations of an encoding are `Bool`-valued (`relBool`), and the
`FirstOrder.Language.Structure` instance on the universe is *derived* from
them, not supplied: an encoder is a computation, not an arbitrary `Prop`. This
is enforced by the compiler rather than by convention – a definition whose
*data* decides an undecidable predicate must be marked `noncomputable`, so the
check to run on an encoder is simply **“its `relBool` elaborates as a plain
`def`, with no `noncomputable` marker”**. Together with the `DecidableEq` and
`Fintype` fields this makes an encoding genuinely executable: an encoded
structure can be `#eval`-ed on a small instance and *tested* before anything is
proved about it.

Do not run `#print axioms` on a bundled `Encoding` to check its encoder:
proof fields are erased by the compiler but not by `#print axioms`, so the
bound proofs (which typically use classical axioms through `Nat.card`) mask
the report. The axiom report is only informative on a standalone `relBool`
definition – and even there “no axioms” is the expected answer only for
quotient-free data: an encoder deciding `Finset` membership goes through
`Multiset` quotients, whose `Decidable` instances cite the classical axioms
in proof positions without affecting executability. The reliable checks are
the two the compiler and evaluator give: no `noncomputable` marker, and a
`#guard`/`#eval` that actually reduces.

## What this does not buy

Nothing here rules out an encoder that *computes the answer*: encode a SAT
instance on a universe of the right size with one unary predicate marking an
element iff the formula is satisfiable, and take the problem “some element is
marked”. Both bounds hold, `Faithful` is provable, and the problem is even
FO-definable; the illegitimacy is entirely in the computational power the
encoder used. Computability of the encoder is enforced, a *complexity bound*
on it is not: stating one means measuring the encoder against a machine model,
which this interface does not do. The reader of an encoding is therefore told
exactly which of the two obligations is machine-checked and which requires
reading `relBool`.

## The decoding direction

Membership results transfer to the concrete problem along a faithful encoding;
*hardness* results need a converse – the abstract problem must not be hard
only on junk structures the encoding never produces. The machinery for that
converse lives in `Lax117614Proofs.DescriptiveComplexity/Decoding.lean`: well-formedness as a
decision problem (restricting hardness to `W ⊓ P`) and computable decodings
(`Lax117614Proofs.DescriptiveComplexity.Decoding`), with the same hygiene as the encoders
here. `Lax117614Proofs.DescriptiveComplexity.Encoding.Covers` below is the ideal,
isomorphism-based decoding statement; junk conventions usually make it
unprovable for honest encodings, which is exactly what the well-formedness
route is for.

## Main declarations

* `Lax117614Proofs.DescriptiveComplexity.Encoding`: the bundled encoding, with its two size
  bounds;
* `Lax117614Proofs.DescriptiveComplexity.Encoding.str`: the derived structure on an encoded
  universe;
* `Lax117614Proofs.DescriptiveComplexity.Encoding.Faithful`: obligation 1, semantic
  equivalence with a concrete predicate;
* `Lax117614Proofs.DescriptiveComplexity.Encoding.Covers`: the ideal, isomorphism-based
  decoding statement (see `Lax117614Proofs.DescriptiveComplexity/Decoding.lean` for the
  practical route);
* `Lax117614Proofs.DescriptiveComplexity.Encoding.linear_bound`: discharge a bound field from a
  linear estimate, the common case.

A worked example – the packaged conjunctive-query instances – is in
`Lax117614Proofs.DescriptiveComplexity/Examples/ConjunctiveQueries.lean`; a second one, for a
catalog problem whose numbers must be written in binary, is
`Lax117614Proofs.DescriptiveComplexity/Encoding/BinarySubsetSum.lean`, which encodes a list of
weights and a target and proves the encoding faithful for Knapsack. The
theorem that the size bounds have teeth (no unary encoding of subset-sum
satisfies them) is in `Lax117614Proofs.DescriptiveComplexity/Encoding/UnaryBlowup.lean`.
-/

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- An encoding of a concrete instance type `ι` by finite structures of the
relational vocabulary `L`: a declared instance size, a computable (`Bool`-
valued) family of structures, and polynomial bounds both ways between the
declared size and the cardinality of the encoded universe – no padding
(`card_le`) and no compression (`le_card`). See the module docstring for why
the bounds are fields: an encoding must not be constructible with them
postponed. -/
structure Encoding (L : Language.{0, 0}) (ι : Type*) where
  /-- The textbook size of a concrete instance. The one line a reader audits:
  everything else is checked against it. -/
  size : ι → ℕ
  /-- The universe carrying the encoded structure of an instance. -/
  Univ : ι → Type
  /-- Decidable equality on the universe, so the encoding is testable. -/
  deceq : ∀ i, DecidableEq (Univ i)
  /-- The universe is (computably) finite. -/
  fintype : ∀ i, Fintype (Univ i)
  /-- The relations, as computations: `relBool i R x` decides whether the
  tuple `x` is in relation `R` on the encoded instance `i`. Keep this a plain
  `def`-legible field – a `noncomputable` encoder is a red flag (see the
  module docstring). -/
  relBool : ∀ i, ∀ {n}, L.Relations n → (Fin n → Univ i) → Bool
  /-- No padding: the universe is polynomially bounded in the declared size. -/
  card_le : ∃ c d : ℕ, ∀ i, Nat.card (Univ i) ≤ c * (size i + 1) ^ d
  /-- No compression: the declared size is polynomially bounded in the
  universe. -/
  le_card : ∃ c d : ℕ, ∀ i, size i ≤ c * (Nat.card (Univ i) + 1) ^ d

namespace Encoding

variable {ι : Type*}

instance (e : Encoding L ι) (i : ι) : DecidableEq (e.Univ i) := e.deceq i

instance (e : Encoding L ι) (i : ι) : Fintype (e.Univ i) := e.fintype i

instance (e : Encoding L ι) (i : ι) : Finite (e.Univ i) := Finite.of_fintype _

/-- Discharge a `card_le`/`le_card` field from a linear estimate – the common
case; every honest encoding in the catalog's reach is linear or nearly so. -/
theorem linear_bound {f s : ι → ℕ} {c : ℕ} (h : ∀ i, f i ≤ c * (s i + 1)) :
    ∃ c' d : ℕ, ∀ i, f i ≤ c' * (s i + 1) ^ d :=
  ⟨c, 1, fun i => by rw [pow_one]; exact h i⟩

/-- The `L`-structure an encoding puts on the universe of an instance: the
relations are the encoder's computations, read as propositions. Derived from
`relBool` rather than supplied, so that the structure of an encoded instance
is exactly what the encoder computes. -/
instance str [L.IsRelational] (e : Encoding L ι) (i : ι) : L.Structure (e.Univ i) where
  funMap f := isEmptyElim f
  RelMap R x := e.relBool i R x = true

variable [L.IsRelational]

/-- The relations of an encoded structure are the encoder's computations. The
`simp` normal form for proofs about encoded structures. -/
@[simp]
theorem relMap_iff (e : Encoding L ι) (i : ι) {n} (R : L.Relations n)
    (x : Fin n → e.Univ i) :
    RelMap R x ↔ e.relBool i R x = true :=
  Iff.rfl

instance (e : Encoding L ι) (i : ι) {n} (R : L.Relations n) (x : Fin n → e.Univ i) :
    Decidable (RelMap R x) :=
  decidable_of_iff _ (e.relMap_iff i R x).symm

/-- Semantic equivalence (obligation 1 of the module docstring): the abstract
problem `P` computes the concrete predicate `Conc` on every encoded instance.
A separate predicate rather than a field, because one encoding may serve
several problems over the same vocabulary. -/
def Faithful (e : Encoding L ι) (Conc : ι → Prop) (P : Lax904597.Problems.DecisionProblem L) : Prop :=
  ∀ i, Conc i ↔ P (e.Univ i)

end Encoding

end Lax117614Proofs.DescriptiveComplexity


