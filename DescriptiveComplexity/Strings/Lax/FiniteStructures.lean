/-
Mirror of `Lax988886.FiniteStructures`: lax-988886, “Fagin's theorem”, formalized by Szymon
Toruńczyk with GPT 6, https://github.com/szymtor/fagin at commit
333e9cbdbd8a389561da30908cabf36051048a13. Released under Apache 2.0 license.
-/
module

public import DescriptiveComplexity.Strings.Lax.OrderedStructures
public import DescriptiveComplexity.Strings.Lax.StructureEncoding

/-!
# Finite relational structures and their properties

A structure has universe `Fin n` and an interpretation of each relation. The
numbering is used for binary input encodings; it is not available as an order
predicate in the logic. Properties are required to be invariant under
isomorphism, so they do not depend on the numbering. The representation and
dense binary encoding are reused from the Immerman–Vardi entry, forgetting its
distinguished order. Empty universes and nullary relations are allowed.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings.Lax.FiniteStructures

/-- A finite relational vocabulary. -/
abbrev Vocabulary := OrderedStructures.Vocabulary
/-- The symbols of a vocabulary. -/
abbrev Symbol := OrderedStructures.Symbol
/-- A finite structure over a vocabulary. -/
abbrev Structure := OrderedStructures.OrderedStructure
/-- An interpretation of a vocabulary on the universe `Fin n`. -/
abbrev Interpretation (σ : Vocabulary) (n : Nat) :=
  (r : Symbol σ) → (Fin (σ.get r) → Fin n) → Bool
/-- A property of finite structures. -/
abbrev Property (σ : Vocabulary) := Structure σ → Prop

/-- An isomorphism of finite structures. -/
structure Isomorphism {σ : Vocabulary} (A B : Structure σ) where
  /-- The bijection of the universes. -/
  equivalence : Fin A.size ≃ Fin B.size
  /-- The bijection preserves every relation. -/
  preserves : ∀ (r : Symbol σ) (a : Fin (σ.get r) → Fin A.size),
    B.relation r (equivalence ∘ a) = A.relation r a

/-- A property that does not distinguish isomorphic structures. -/
def IsomorphismInvariant {σ : Vocabulary} (Q : Property σ) : Prop :=
  ∀ A B : Structure σ, Nonempty (Isomorphism A B) → (Q A ↔ Q B)

/-- The encoding of a structure: that of the structure pointed by the empty tuple. -/
def encode {σ : Vocabulary} (A : Structure σ) : List Bool :=
  StructureEncoding.encode ⟨A, Fin.elim0⟩

/-- The language of the encodings of the structures satisfying a property. -/
def language {σ : Vocabulary} (Q : Property σ) (w : List Bool) : Prop :=
  ∃ A : Structure σ, encode A = w ∧ Q A

end DescriptiveComplexity.Strings.Lax.FiniteStructures
