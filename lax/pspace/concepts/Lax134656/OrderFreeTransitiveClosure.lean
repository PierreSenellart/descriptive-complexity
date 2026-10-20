import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax904597.SecondOrder
import Lax535992.InflationaryFixedPoint
import Lax134656.SecondOrderTransitiveClosure

/-!
---
title: Second-order transitive closure without an order
type: definition
---
An order-free second-order transitive-closure specification over a
vocabulary $L$ is a specification whose three sentences are over $L$ and
the copies of the block alone, with no order symbol. It defines, on any
$L$-structure, the same graph on the assignments of the block and the same
acceptance condition. A decision problem $P$ over $L$ is order-free SO(TC)
definable when some such specification accepts, for every nonempty finite
$L$-structure $A$, exactly when $A$ is a yes-instance of $P$: no linear
order appears in the statement.
-/

namespace Lax134656.OrderFreeTransitiveClosure

open Lax904597.Problems Lax904597.SecondOrder Lax535992.InflationaryFixedPoint
open Lax134656.SecondOrderTransitiveClosure

open FirstOrder

open Language Structure

/-- An SO(TC) specification that does **not** see a linear order: as in
`SOTCSpec`, the states of the walk are the assignments of
a block, but the three sentences live over the bare vocabulary expanded by
copies of the block, with no order symbol available. -/
structure SOTCSpecFree (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : ((L.sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : (L.sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : (L.sum B.lang).Sentence

namespace SOTCSpecFree

section Semantics

variable {L : Language.{0, 0}} (spec : SOTCSpecFree L) {A : Type} [L.Structure A]

variable (A) in
/-- A state of the walk: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- One step of the walk: the transition sentence, read with the current state
in the first copy of the block and the next state in the second. -/
def Step (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₂ (L := L) spec.B ρ σ) spec.step

/-- Reachability in the walk: the reflexive-transitive closure of
`SOTCSpecFree.Step`. -/
abbrev Reach : spec.State A → spec.State A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A state is a starting state when it satisfies the source sentence. -/
def IsSrc (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L) spec.B ρ) spec.src

/-- A state is accepting when it satisfies the target sentence. -/
def IsTgt (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L) spec.B ρ) spec.tgt

variable (A) in
/-- The structure is accepted: some accepting state is reachable from some
starting state. No order on `A` is involved. -/
def Accepts : Prop :=
  ∃ ρ σ : spec.State A, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ spec.Reach ρ σ

end Semantics

end SOTCSpecFree

/-- A decision problem is *order-free SO(TC) definable* if it is defined by an
`SOTCSpecFree` on nonempty finite structures – with **no linear order in the
statement at all**, unlike `SOTCDefinable`. -/
def SOTCDefinableFree {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : SOTCSpecFree L,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ spec.Accepts A

end Lax134656.OrderFreeTransitiveClosure
