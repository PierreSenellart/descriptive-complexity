/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.SetTheory.Cardinal.Finite
import DescriptiveComplexity.Interpretation

/-!
# Faithful encodings of concrete instance types

A `DescriptiveComplexity.DecisionProblem` is a property of finite structures. A
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

This file makes obligation 2 a *proof obligation*: `DescriptiveComplexity.Encoding`
bundles the concrete instance type, its declared size, the encoding map, and
polynomial bounds in **both** directions between the declared size and the
cardinality of the encoded universe – so that an encoding cannot be constructed
without discharging them. `card_le` forbids padding (protecting membership
claims: pad the universe to `2 ^ size` and "in NP over structures" becomes a
much weaker statement about the concrete problem); `le_card` forbids
compression (protecting hardness claims), and also defends the definition
against inflating `size` to make `card_le` vacuous. Obligation 1 remains a
theorem the user proves, now packaged as `DescriptiveComplexity.Encoding.Faithful`.

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
check to run on an encoder is simply **"its `relBool` elaborates as a plain
`def`, with no `noncomputable` marker"**. Together with the `DecidableEq` and
`Fintype` fields this makes an encoding genuinely executable: an encoded
structure can be `#eval`-ed on a small instance and *tested* before anything is
proved about it.

Do not run `#print axioms` on a bundled `Encoding` to check its encoder:
proof fields are erased by the compiler but not by `#print axioms`, so the
bound proofs (which typically use classical axioms through `Nat.card`) mask
the report. The axiom report is only informative on a standalone `relBool`
definition – and even there "no axioms" is the expected answer only for
quotient-free data: an encoder deciding `Finset` membership goes through
`Multiset` quotients, whose `Decidable` instances cite the classical axioms
in proof positions without affecting executability. The reliable checks are
the two the compiler and evaluator give: no `noncomputable` marker, and a
`#guard`/`#eval` that actually reduces.

## What this does not buy

Nothing here rules out an encoder that *computes the answer*: encode a SAT
instance on a universe of the right size with one unary predicate marking an
element iff the formula is satisfiable, and take the problem "some element is
marked". Both bounds hold, `Faithful` is provable, and the problem is even
FO-definable; the illegitimacy is entirely in the computational power the
encoder used. Computability of the encoder is enforced, a *complexity bound*
on it is not – that would need the machine bridge (`ROADMAP.md` §7), on top of
which "the encoder is computed by a polynomial-time machine" becomes
expressible. Until then the reader of an encoding is told exactly which of the
two obligations is machine-checked and which still requires reading `relBool`.

## The decoding direction

Membership results transfer to the concrete problem along a faithful encoding;
*hardness* results need the converse – every abstract instance is (equivalent
to) an encoded one, else the concrete problem could be the easy fragment of a
hard abstract one. `DescriptiveComplexity.Encoding.Covers` is the ideal,
isomorphism-based statement; `DescriptiveComplexity.Encoding.CoversUpTo` is the
weaker, semantic variant that suffices for the hardness reading and that
remains provable when junk conventions make some abstract structures literally
unrepresentable (their junk being invisible to the semantics). Neither feeds a
*formal* hardness transfer – the library has no complexity classes over
concrete instance types – but each is the checkable piece of the transfer the
reader performs.

## Main declarations

* `DescriptiveComplexity.Encoding`: the bundled encoding, with its two size
  bounds;
* `DescriptiveComplexity.Encoding.str`: the derived structure on an encoded
  universe;
* `DescriptiveComplexity.Encoding.Faithful`: obligation 1, semantic
  equivalence with a concrete predicate;
* `DescriptiveComplexity.Encoding.Covers`, `DescriptiveComplexity.Encoding.CoversUpTo`:
  the decoding direction;
* `DescriptiveComplexity.Encoding.linear_bound`: discharge a bound field from a
  linear estimate, the common case.

A worked example – the packaged conjunctive-query instances – is in
`DescriptiveComplexity/Examples/ConjunctiveQueries.lean`; the theorem that the
size bounds have teeth (no unary encoding of subset-sum satisfies them) is in
`DescriptiveComplexity/Encoding/UnaryBlowup.lean`.
-/

namespace DescriptiveComplexity

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

/-- Discharge a `card_le`/`le_card` field from a degree-`d` estimate. -/
theorem poly_bound {f s : ι → ℕ} {c d : ℕ} (h : ∀ i, f i ≤ c * (s i + 1) ^ d) :
    ∃ c' d' : ℕ, ∀ i, f i ≤ c' * (s i + 1) ^ d' :=
  ⟨c, d, h⟩

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
def Faithful (e : Encoding L ι) (Conc : ι → Prop) (P : DecisionProblem L) : Prop :=
  ∀ i, Conc i ↔ P (e.Univ i)

/-- Faithfulness transports along (extensional) equality of decision problems,
so a user may state it against the bundled problem or against the raw
predicate. -/
theorem faithful_congr {e : Encoding L ι} {Conc : ι → Prop} {P Q : DecisionProblem L}
    (hPQ : ∀ (A : Type) [L.Structure A], P A ↔ Q A) :
    e.Faithful Conc P ↔ e.Faithful Conc Q :=
  forall_congr' fun _ => iff_congr Iff.rfl (hPQ _)

/-- The encoding reaches every finite structure up to isomorphism: the ideal
decoding direction. Junk conventions can make this literally unprovable for an
honest encoding (some abstract structures carry facts the concrete type cannot
represent); `CoversUpTo` is the semantic fallback. -/
def Covers (e : Encoding L ι) : Prop :=
  ∀ (A : Type) [L.Structure A] [Finite A], ∃ i, Nonempty (A ≃[L] e.Univ i)

/-- The encoding reaches every finite structure up to the *semantics* of `P`:
each abstract instance is decided by `P` exactly as some concrete instance is
by `Conc`. This is what the hardness reading actually needs, and it survives
junk conventions (unrepresentable facts being invisible to the semantics).

Two honesty caveats. It does not feed a formal hardness transfer – the
library has no complexity classes over concrete instance types. And as a
*statement* it is classically near-vacuous: whenever `Conc` has one
yes-instance and one no-instance, casing on `P A` discharges it without any
decoding. Its value is therefore the explicit transcription an honest proof
constructs (as the conjunctive-query tutorial's does); a proof by classical
casing certifies nothing, and where no honest transcription exists (see the
graph-crawling tutorial) the right move is to say so. -/
def CoversUpTo (_e : Encoding L ι) (Conc : ι → Prop) (P : DecisionProblem L) : Prop :=
  ∀ (A : Type) [L.Structure A] [Finite A], ∃ i, Conc i ↔ P A

/-- A faithful encoding that covers all finite structures up to isomorphism
covers them up to semantics: isomorphism-invariance of the problem closes the
square. -/
theorem Faithful.coversUpTo {e : Encoding L ι} {Conc : ι → Prop} {P : DecisionProblem L}
    (hf : e.Faithful Conc P) (hc : e.Covers) : e.CoversUpTo Conc P := by
  intro A _ _
  obtain ⟨i, ⟨u⟩⟩ := hc A
  exact ⟨i, (hf i).trans (P.iso_invariant u).symm⟩

end Encoding

end DescriptiveComplexity
