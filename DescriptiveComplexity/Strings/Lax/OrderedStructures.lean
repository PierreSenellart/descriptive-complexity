/-
Mirror of `Lax751879.OrderedStructures`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

/-!
# Finite ordered relational structures and queries

A finite relational vocabulary is a finite list of arities. An ordered
structure of size `n` has universe `{0, …, n - 1}`, its usual strict order, and
an interpretation of each relation symbol: the canonical representative of a
finite linearly ordered structure up to isomorphism. The order is available to
formulas as a distinguished atomic predicate.

A pointed structure additionally carries a `k`-tuple of elements, and a `k`-ary
query is a property of these pointed structures; `k = 0` gives Boolean queries.
Empty universes and nullary relation symbols are allowed. The vocabulary and
query arity are fixed independently of the input structure.

The declarations of this directory mirror two entries of the Lax archive: see
`DescriptiveComplexity.Strings`.
-/

namespace DescriptiveComplexity.Strings.Lax.OrderedStructures

/-- A finite relational vocabulary: the list of the arities of its symbols. -/
abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

/-- A finite ordered structure: a size, and a Boolean table per symbol. -/
structure OrderedStructure (σ : Vocabulary) where
  /-- The size of the universe `Fin size`. -/
  size : Nat
  /-- The interpretation of each relation symbol. -/
  relation : (r : Symbol σ) → (Fin (σ.get r) → Fin size) → Bool

/-- An ordered structure with a distinguished `k`-tuple of elements. -/
structure PointedStructure (σ : Vocabulary) (k : Nat) where
  /-- The underlying structure. -/
  structureValue : OrderedStructure σ
  /-- The distinguished tuple. -/
  tuple : Fin k → Fin structureValue.size

/-- A `k`-ary query: a property of pointed structures. -/
abbrev Query (σ : Vocabulary) (k : Nat) := PointedStructure σ k → Prop

end DescriptiveComplexity.Strings.Lax.OrderedStructures
