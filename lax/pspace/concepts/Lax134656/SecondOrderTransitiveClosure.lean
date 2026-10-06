import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.SecondOrder
import Lax535992.InflationaryFixedPoint

/-!
---
title: Second-order logic with a transitive closure
type: definition
---
A second-order transitive-closure specification over a vocabulary $L$
consists of a block of relation variables and three first-order sentences
over $L \cup \{\le\}$: a transition sentence over two copies of the
block, and a source and a target sentence over one copy. On a linearly
ordered $L$-structure it defines a directed graph whose nodes, the states,
are the assignments of relations to the block, with an edge from one state
to another when the transition sentence holds with the first copy of the
block read as the current state and the second as the next. The
specification accepts the structure when some state satisfying the target
sentence is reachable, by a possibly empty path, from some state satisfying
the source sentence.

A decision problem $P$ over $L$ is SO(TC) definable when some specification
accepts, for every nonempty finite $L$-structure $A$ and every linear order
on $A$, exactly when $A$ is a yes-instance of $P$. A state holds
polynomially many bits and a path may be exponentially long: this is the
logic SO(TC), which captures polynomial space on ordered structures, in the
normal form of a single application of the operator.
-/

namespace Lax134656.SecondOrderTransitiveClosure

open Lax904597.Problems Lax904597.SecondOrder Lax535992.InflationaryFixedPoint

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by *two* copies of a block's vocabulary –
the current state and the next one – interpreted by two assignments. -/
@[reducible]
def SOBlock.structure₂ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ σ : B.Assignment A) : ((L.sum B.lang).sum B.lang).Structure A :=
  @sumStructure (L.sum B.lang) B.lang A (SOBlock.structure₁ B ρ) (B.structure σ)

/-- A single-`TC` definition over a second-order block: the states of the walk
are the assignments of the block `B`, and the transition, source, and target
conditions are first-order sentences over the base vocabulary expanded by the
order and by copies of the block. The transition sentence sees two copies –
the current state and the next one.

The order is visible to all three sentences; the problem itself does not see
it. -/
structure SOTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : ((L.sum Language.order).sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : ((L.sum Language.order).sum B.lang).Sentence

namespace SOTCSpec

section Semantics

variable {L : Language.{0, 0}} (spec : SOTCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A state of the walk: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- One step of the walk: the transition sentence, read with the current state
in the first copy of the block and the next state in the second. -/
def Step (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₂ (L := L.sum Language.order) spec.B ρ σ) spec.step

/-- Reachability in the walk: the reflexive-transitive closure of
`SOTCSpec.Step`. -/
abbrev Reach : spec.State A → spec.State A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A state is a starting state when it satisfies the source sentence. -/
def IsSrc (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L.sum Language.order) spec.B ρ) spec.src

/-- A state is accepting when it satisfies the target sentence. -/
def IsTgt (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L.sum Language.order) spec.B ρ) spec.tgt

variable (A) in
/-- The structure is accepted: some accepting state is reachable from some
starting state. -/
def Accepts : Prop :=
  ∃ ρ σ : spec.State A, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ spec.Reach ρ σ

end Semantics

end SOTCSpec

/-- A decision problem is *SO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure over the assignments
of a second-order quantifier block: there is an `SOTCSpec` whose accepting
states are reachable from its starting states exactly on the yes-instances.
The equivalence is required for *every* linear order on the universe: the
problem itself does not see the order, while the three sentences may. -/
def SOTCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : SOTCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

end Lax134656.SecondOrderTransitiveClosure
