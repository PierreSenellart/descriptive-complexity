import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Lax134656.PartialFixedPoint
import Lax480241.Expansions
import Lax535992.LeastFixedPoint
import Lax904597.Problems
import Lax904597.SecondOrder
import Lax904597.Interpretations

/-!
---
title: Second-order fixed points
type: definition
---
SO(≤, LFP) and SO(≤, PFP) are first-order logic with least and partial fixed
points read one exponential up: a problem $P$ is SO(≤, LFP)-definable when
an exponential expansion $X$ and an FO(≤, LFP)-definable problem $Q$ of its
vocabulary are such that $P(A)$ holds exactly when $Q(X(A))$ does, for every
nonempty finite structure $A$ and every linear order on it. The order-free
forms use expansions whose sentences read no order, the equivalence being
asked of structures carrying none.
-/

namespace Lax480241.SecondOrderFixedPoints

open Lax134656.PartialFixedPoint Lax480241.Expansions Lax535992.LeastFixedPoint Lax904597.Problems
open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- An **order-free exponential expansion**: as
`ExpExpansion`, except that the domain sentence and the
defining sentences live over the bare vocabulary expanded by copies of the
block, with no order symbol available. Its universe is therefore defined on a
structure carrying no order. -/
structure ExpExpansionFree (L : Language.{0, 0}) : Type 1 where
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
  /-- The domain sentence of each tag, over the bare vocabulary. -/
  dom : Tag → (L.sum B.lang).Sentence
  /-- The defining sentence of each relation symbol at each tuple of tags, over
  the bare vocabulary and as many copies of the block as the symbol has
  arguments. -/
  relSentence : ∀ {n : ℕ}, E.Relations n → (Fin n → Tag) →
    (L.sum (SOBlock.replicate B n).lang).Sentence
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (ρ : B.Assignment A),
      @Sentence.Realize _ A (SOBlock.structure₁ B (L := L) ρ) (dom t)

namespace ExpExpansionFree

variable (X : ExpExpansionFree L)

attribute [instance] tagFinite eRelational

/-- A candidate point: a tagged assignment of the block. -/
abbrev Point (A : Type) : Type := X.Tag × X.B.Assignment A

variable {X}

/-- The domain condition on a candidate point. -/
def DomHolds {A : Type} [L.Structure A] (p : X.Point A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ X.B (L := L) p.2) (X.dom p.1)

variable (X)

/-- **The expanded universe**: the tagged block assignments satisfying their
tag's domain sentence. No order on `A` is involved. -/
def Map (A : Type) [L.Structure A] : Type := {p : X.Point A // DomHolds p}

variable {X}

variable (X)

/-- **The expanded structure.** -/
instance mapStructure (A : Type) [L.Structure A] : X.E.Structure (X.Map A) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    @Sentence.Realize _ A
      (SOBlock.structure₁ (SOBlock.replicate X.B n) (L := L)
        (SOBlock.replicateAssign X.B fun i => (xs i).1.2))
      (X.relSentence r fun i => (xs i).1.1)

instance mapFinite (A : Type) [L.Structure A] [Finite A] : Finite (X.Map A) :=
  inferInstanceAs (Finite {p : X.Point A // DomHolds p})

instance mapNonempty (A : Type) [L.Structure A] [Finite A] [Nonempty A] :
    Nonempty (X.Map A) :=
  let ⟨t, ρ, h⟩ := X.dom_nonempty A
  ⟨⟨(t, ρ), h⟩⟩

end ExpExpansionFree

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **SO(PFP) without the order**: a partial fixed point over a second-order
universe *defined without an order*, the equivalence being asked of structures
carrying none. -/
def SOPFPDefinableFree (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansionFree L) (Q : DecisionProblem X.E), PFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **SO(LFP) without the order**: a least fixed point over a second-order
universe *defined without an order*, the equivalence being asked of structures
carrying none. -/
def SOLFPDefinableFree (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansionFree L) (Q : DecisionProblem X.E), LFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **SO(≤, LFP)**: a least fixed point over a second-order universe. The
problem holds of `A` exactly when an FO(≤, LFP) definition holds of an
exponential expansion of `A`. The order the expansion's own sentences read can
be removed (`solfpDefinable_iff_free`), by guessing it
into the block. -/
def SOLFPDefinable (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), LFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

/-- **SO(≤, PFP)**: a partial fixed point over a second-order universe. The
order the expansion's own sentences read can be removed
(`sopfpDefinable_iff_free`), by guessing it into the
block. -/
def SOPFPDefinable (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), PFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

end Lax480241.SecondOrderFixedPoints
