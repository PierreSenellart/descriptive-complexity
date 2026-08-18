/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Expansion
import DescriptiveComplexity.OrderWalk

/-!
# The order on an expanded universe

An exponential expansion's sentences see the order of the structure they expand
(`DescriptiveComplexity.ExpExpansion`). To compose an expansion with anything
that reads *its* order – which is what a complete problem for an exponential
class needs – that order must in turn be **definable by a first-order sentence
over the base**. It is, and this file builds it: the analogue, one level up, of
`DescriptiveComplexity.tagTupleOrder` and
`DescriptiveComplexity.FOInterpretation.ordExtend`.

## The order

Points of the expanded universe are tagged block assignments. Order them by
tag first – statically, by an arbitrary linear order on the finite tag type –
and then by reading an assignment as a **binary number**: `ρ` is below `σ` when,
at the least atom where they differ, `σ` holds and `ρ` does not.

“Atom” here means a relation variable of the block together with a tuple of
elements. Arities differ from variable to variable, so the atoms are indexed by
a dependent sum; this file avoids it by **padding** every tuple to the block's
maximal arity (`DescriptiveComplexity.blockArityBound`), which turns the index
type into a plain product `B.ι × (Fin D → A)` – exactly the shape
`DescriptiveComplexity.tagTupleOrder` already orders. Padding loses nothing:
an assignment is determined by the atoms it makes true
(`DescriptiveComplexity.SOBlock.atomSet_injective`), since every tuple of the
relevant arity is the prefix of some padded tuple.

## Layers

1. `DescriptiveComplexity.setLinearOrder` – the binary-number order on the
   subsets of any finite linearly ordered index type, obtained from Mathlib's
   `Pi.Lex` on functions to `Bool`, so that transitivity and totality are
   inherited rather than proved.
2. `DescriptiveComplexity.SOBlock.atomSet` – an assignment read as such a
   subset, and its injectivity.
3. `DescriptiveComplexity.ExpExpansion.mapLinearOrder` – the two put together
   with the tag, and transported to the subtype `X.Map A`.

The defining *formula* and its realization lemma live in
`DescriptiveComplexity.Exponential.OrdFormula`; this file is the semantics it
is proved against.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The binary-number order on subsets of a finite linear order -/

section SetOrder

variable {I : Type}

open Classical in
/-- The key ordering subsets of `I`: the characteristic function, read
lexicographically with `False < True`. -/
private noncomputable def setKey (S : I → Prop) : Lex (I → Bool) :=
  toLex fun i => decide (S i)

open Classical in
private theorem setKey_injective : Function.Injective (setKey (I := I)) := by
  intro S T h
  funext i
  exact propext (decide_eq_decide.mp (congrFun (toLex.injective h) i))

variable (I) in
/-- **The binary-number order on subsets** of a finite linearly ordered index
type: one subset is below another when, at the least index where they differ,
the second contains it and the first does not. Lifted from `Pi.Lex`, so the
linear-order axioms come for free. -/
@[instance_reducible]
noncomputable def setLinearOrder [LinearOrder I] [Finite I] : LinearOrder (I → Prop) :=
  LinearOrder.lift' setKey setKey_injective

/-- **What the order says**, unfolded. -/
theorem setLinearOrder_lt_iff [LinearOrder I] [Finite I] (S T : I → Prop) :
    (setLinearOrder I).lt S T ↔ ∃ i, (∀ j, j < i → (S j ↔ T j)) ∧ ¬S i ∧ T i := by
  classical
  have he : ∀ (U V : I → Prop) (i : I), (decide (U i) = decide (V i)) ↔ (U i ↔ V i) :=
    fun _ _ _ => decide_eq_decide
  have hb : ∀ (U V : I → Prop) (i : I), (decide (U i) < decide (V i)) ↔ (¬U i ∧ V i) := by
    intro U V i
    by_cases hu : U i <;> by_cases hv : V i <;> simp [hu, hv]
  have hlt : (setLinearOrder I).lt S T ↔ setKey S < setKey T := Iff.rfl
  rw [hlt]
  constructor
  · rintro ⟨i, hag, hi⟩
    exact ⟨i, fun j hj => (he S T j).mp (hag j hj), (hb S T i).mp hi⟩
  · rintro ⟨i, hag, hi⟩
    exact ⟨i, fun j hj => (he S T j).mpr (hag j hj), (hb S T i).mpr hi⟩

end SetOrder

/-! ### An assignment read as a set of padded atoms -/

namespace SOBlock

variable (B : SOBlock) {A : Type}

/-- The index of a **padded atom** of a block: a relation variable together
with a tuple of the block's maximal arity, of which only the first
`B.arity i` coordinates are read. A plain product, deliberately: the honest
index type is a dependent sum, and padding trades it for a shape
`DescriptiveComplexity.tagTupleOrder` already orders. -/
abbrev AtomIx (A : Type) : Type := B.ι × (Fin (blockArityBound B) → A)

/-- The padded atoms an assignment makes true. -/
def atomSet (ρ : B.Assignment A) : B.AtomIx A → Prop :=
  fun p => ρ p.1 fun j => p.2 (Fin.castLE (arity_le_blockArityBound B p.1) j)

/-- A tuple of the arity of `i`, padded out to the block's maximal arity. -/
private noncomputable def padTuple [Nonempty A] (i : B.ι) (x : Fin (B.arity i) → A) :
    Fin (blockArityBound B) → A :=
  fun k => if h : (k : ℕ) < B.arity i then x ⟨k, h⟩ else Classical.arbitrary A

private theorem padTuple_castLE [Nonempty A] (i : B.ι) (x : Fin (B.arity i) → A)
    (j : Fin (B.arity i)) :
    B.padTuple i x (Fin.castLE (arity_le_blockArityBound B i) j) = x j := by
  have hj : ((Fin.castLE (arity_le_blockArityBound B i) j : Fin (blockArityBound B)) : ℕ)
      < B.arity i := j.isLt
  simp only [padTuple, dif_pos hj]
  exact congrArg x (Fin.val_injective rfl)

variable (A) in
/-- **The padded atoms are linearly ordered**: the relation variable first, in
an arbitrary order on the finite index type of the block, then the tuple
lexicographically. This is `DescriptiveComplexity.tagTupleOrder` at
`Tag := B.ι`, written directly as a lift into `B.ι ×ₗ Lex (Fin D → A)` so that
its strict order unfolds by `DescriptiveComplexity.prodLex_lt_iff` without a
detour through `DescriptiveComplexity.tagTupleLe`. -/
@[instance_reducible]
noncomputable def atomIxLinearOrder [LinearOrder A] : LinearOrder (B.AtomIx A) :=
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  LinearOrder.lift' (fun p : B.AtomIx A => toLex (p.1, toLex p.2))
    (by
      intro p q h
      have h' : (p.1, toLex p.2) = (q.1, toLex q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h'
      exact Prod.ext_iff.mpr ⟨h1, toLex.injective h2⟩)

/-- The order on padded atoms **as a plain relation**. Consumers use this
rather than `<`: `AtomIx` is a product, so the product's own order instances
would compete with `DescriptiveComplexity.SOBlock.atomIxLinearOrder` and `<`
would resolve ambiguously. All the instance juggling is confined to this file. -/
def atomLt [LinearOrder A] (p q : B.AtomIx A) : Prop :=
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  p.1 < q.1 ∨ (p.1 = q.1 ∧ toLex p.2 < toLex q.2)

/-- **What the order on padded atoms is**: the plain relation above. -/
theorem atomIx_lt_iff [LinearOrder A] (p q : B.AtomIx A) :
    (B.atomIxLinearOrder A).lt p q ↔ B.atomLt p q := by
  letI : LinearOrder B.ι := finiteLinearOrder B.ι
  exact prodLex_lt_iff (B := Lex (Fin (blockArityBound B) → A))

/-- **An assignment is determined by the padded atoms it makes true**: every
tuple of the relevant arity is the prefix of a padded tuple, so nothing is lost
by the padding. -/
theorem atomSet_injective [Nonempty A] : Function.Injective (B.atomSet (A := A)) := by
  intro ρ σ h
  funext i x
  have := congrFun h (i, B.padTuple i x)
  rw [atomSet, atomSet] at this
  simpa only [B.padTuple_castLE i x] using this

/-- **The comparison of two assignments, packaged**: the binary-number order on
their padded atoms, stated entirely in terms of
`DescriptiveComplexity.SOBlock.atomLt` so that no consumer has to resolve an
order instance on a product. -/
theorem atomSet_lt_iff [LinearOrder A] [Finite A] (ρ σ : B.Assignment A) :
    letI := B.atomIxLinearOrder A
    ((setLinearOrder (B.AtomIx A)).lt (B.atomSet ρ) (B.atomSet σ) ↔
      ∃ p : B.AtomIx A, (∀ q, B.atomLt q p → (B.atomSet ρ q ↔ B.atomSet σ q)) ∧
        ¬B.atomSet ρ p ∧ B.atomSet σ p) := by
  letI := B.atomIxLinearOrder A
  rw [setLinearOrder_lt_iff]
  refine exists_congr fun p => and_congr_left' (forall_congr' fun q => ?_)
  exact imp_congr_left (B.atomIx_lt_iff q p)

end SOBlock

/-! ### The order on the points of an expansion -/

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L) (A : Type)
variable [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The order on the candidate points of an expansion**: tag first, then the
assignment read as a binary number. -/
@[instance_reducible]
noncomputable def pointLinearOrder : LinearOrder (X.Point A) :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  letI := X.B.atomIxLinearOrder A
  letI := setLinearOrder (X.B.AtomIx A)
  LinearOrder.lift' (fun p : X.Point A => toLex (p.1, X.B.atomSet p.2))
    (by
      intro p q h
      have h' : (p.1, X.B.atomSet p.2) = (q.1, X.B.atomSet q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h'
      exact Prod.ext_iff.mpr ⟨h1, X.B.atomSet_injective h2⟩)

/-- **The order on the expanded universe**, carried to the definable subset. -/
@[instance_reducible]
noncomputable def mapLinearOrder : LinearOrder (X.Map A) :=
  letI := X.pointLinearOrder A
  LinearOrder.lift' (fun x : X.Map A => x.1) fun _ _ h => Subtype.ext h

end ExpExpansion

end DescriptiveComplexity
