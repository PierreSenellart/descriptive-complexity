/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Block
import DescriptiveComplexity.OrderedComposition

/-!
# Exponential expansions: reading a structure over its second-order objects

The one construction the exponential classes are built from. An **exponential
expansion** of `L`-structures maps a finite ordered `L`-structure `A` to a
structure over another vocabulary `E` whose *universe is a definable set of
tagged assignments of a second-order block*. A block with a variable of arity
`a` has `2^(n^a)` assignments on a universe of size `n`, so the expanded
universe is exponentially larger than `A`, and a resource bound read there is
one exponential higher than the same bound read on `A`.

The data (`DescriptiveComplexity.ExpExpansion`) mirrors
`DescriptiveComplexity.RelFOInterpretation` one level up:

* a finite `Tag` type and a block `B`, whose pairs `(t, ρ)` are the candidate
  points – the analogue of the tagged tuples `Tag × A^dim`;
* a **domain sentence** `dom t` per tag, over the ordered base vocabulary
  expanded by one copy of the block, cutting the universe down to a definable
  set (`DescriptiveComplexity.ExpExpansion.Map`, a subtype);
* a **defining sentence** `relSentence r τ` per relation symbol of `E` and per
  tuple of tags, over the ordered base vocabulary expanded by as many copies of
  the block as the symbol has arguments
  (`DescriptiveComplexity.SOBlock.replicate`).

Three design points, each paying for itself downstream.

**The tags are part of the data, not a separate dimension.** A `d`-tuple of
points is a tag tuple together with an assignment of the replicated block, so
composing an expansion with a first-order interpretation gives an expansion
again, on the nose rather than up to an embedding
(`DescriptiveComplexity.Exponential.Pull`). Without the tag factor every
hardness discharge would owe a relativization argument.

**There is a domain sentence.** Hardness in this library is cofinal hardness
and `DescriptiveComplexity.cofinalHard_iff` hands out *relativized* reductions
`≤ʳᶠᵒ[≤]`, whose target universe is already a subtype; an expansion composed
with one is again an expansion only if expansions may carve out their universe
too. `dom_nonempty` is then the same obligation, for the same reason, as in
`DescriptiveComplexity.RelOrderedFOReduction`.

**The sentences see the order, the problem does not.** This is the discipline
of `DescriptiveComplexity.SOTCSpec`: the capture theorems this development
builds on are the ordered ones, while order-invariance is what makes the notion
a `DescriptiveComplexity.DecisionProblem`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### The data -/

/-- An **exponential expansion** of `L`-structures into `E`-structures: the
universe is a definable set of tagged assignments of the block `B`, and each
relation symbol of `E` is defined, at each tuple of tags, by a first-order
sentence over the ordered base vocabulary expanded by one copy of the block per
argument. -/
structure ExpExpansion (L : Language.{0, 0}) : Type 1 where
  /-- The tags: finitely many copies of the space of block assignments. -/
  Tag : Type
  /-- Tags are finite, so that finite structures expand to finite
  structures. -/
  [tagFinite : Finite Tag]
  /-- The block whose assignments are the points of the expanded universe. -/
  B : SOBlock
  /-- The vocabulary of the expanded structure. -/
  E : Language.{0, 0}
  /-- The expanded vocabulary is relational, as every vocabulary of this
  library. -/
  [eRelational : E.IsRelational]
  /-- The domain sentence of each tag: a tagged assignment `(t, ρ)` is a point
  of the expanded universe iff `dom t` holds of `ρ`. -/
  dom : Tag → ((L.sum Language.order).sum B.lang).Sentence
  /-- The defining sentence of each relation symbol at each tuple of tags, over
  as many copies of the block as the symbol has arguments. -/
  relSentence : ∀ {n : ℕ}, E.Relations n → (Fin n → Tag) →
    ((L.sum Language.order).sum (B.replicate n).lang).Sentence
  /-- The definable domain is inhabited, so that nonempty structures expand to
  nonempty structures. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (ρ : B.Assignment A),
      @Sentence.Realize _ A (B.structure₁ (L := L.sum Language.order) ρ) (dom t)

attribute [instance] ExpExpansion.tagFinite ExpExpansion.eRelational

namespace ExpExpansion

variable (X : ExpExpansion L)

/-! ### The expanded universe -/

/-- A candidate point of the expanded universe: a tagged assignment of the
block. An `abbrev`, so that the pair structure stays visible to `rw` and to
instance search – only `DescriptiveComplexity.ExpExpansion.Map` needs to be
opaque, to carry the expanded structure. -/
protected abbrev Point (A : Type) : Type :=
  X.Tag × X.B.Assignment A

variable {X}

/-- The domain condition on a candidate point: its tag's domain sentence holds
of its assignment. -/
def DomHolds {A : Type} [L.Structure A] [LinearOrder A] (p : X.Point A) : Prop :=
  @Sentence.Realize _ A (X.B.structure₁ (L := L.sum Language.order) p.2) (X.dom p.1)

variable (X)

/-- **The expanded universe**: the tagged block assignments satisfying their
tag's domain sentence. -/
protected def Map (A : Type) [L.Structure A] [LinearOrder A] : Type :=
  {p : X.Point A // DomHolds p}

variable {X}

/-- The point of the expanded universe carried by a tag and an assignment
satisfying the domain sentence. -/
def pt {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag) (ρ : X.B.Assignment A)
    (h : DomHolds (X := X) (t, ρ)) : X.Map A :=
  ⟨(t, ρ), h⟩

@[simp]
theorem pt_tag {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag)
    (ρ : X.B.Assignment A) (h : DomHolds (X := X) (t, ρ)) : (pt t ρ h).1.1 = t :=
  rfl

@[simp]
theorem pt_assign {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag)
    (ρ : X.B.Assignment A) (h : DomHolds (X := X) (t, ρ)) : (pt t ρ h).1.2 = ρ :=
  rfl

/-- Two points of the expanded universe are equal as soon as their tags and
their assignments are: the domain condition is a proof. -/
theorem map_ext {A : Type} [L.Structure A] [LinearOrder A] {x y : X.Map A}
    (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext_iff.mpr ⟨h₁, h₂⟩)

variable (X)

/-- **The expanded structure**: an `n`-ary symbol holds of `n` points iff its
defining sentence, at their tags, holds in the base structure with the `n`
copies of the block interpreted by their assignments. -/
instance mapStructure (A : Type) [L.Structure A] [LinearOrder A] :
    X.E.Structure (X.Map A) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    @Sentence.Realize _ A
      ((X.B.replicate n).structure₁ (L := L.sum Language.order)
        (X.B.replicateAssign fun i => (xs i).1.2))
      (X.relSentence r fun i => (xs i).1.1)

theorem relMap_map {A : Type} [L.Structure A] [LinearOrder A] {n : ℕ} (r : X.E.Relations n)
    (xs : Fin n → X.Map A) :
    RelMap r xs ↔
      @Sentence.Realize _ A
        ((X.B.replicate n).structure₁ (L := L.sum Language.order)
          (X.B.replicateAssign fun i => (xs i).1.2))
        (X.relSentence r fun i => (xs i).1.1) :=
  Iff.rfl

/-! ### Finiteness and nonemptiness -/

instance mapFinite (A : Type) [L.Structure A] [LinearOrder A] [Finite A] :
    Finite (X.Map A) :=
  inferInstanceAs (Finite {p : X.Point A // DomHolds p})

instance mapNonempty (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (X.Map A) :=
  let ⟨t, ρ, h⟩ := X.dom_nonempty A
  ⟨pt t ρ h⟩

end ExpExpansion

end DescriptiveComplexity
