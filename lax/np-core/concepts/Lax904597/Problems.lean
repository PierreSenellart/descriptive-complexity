import Mathlib.ModelTheory.Semantics

/-!
---
title: Decision problems on finite structures
type: definition
---
A decision problem over a relational vocabulary $L$ is an
isomorphism-invariant property of $L$-structures: for each universe `A`
carrying an $L$-structure, whether `A` is a yes-instance, with the
requirement that isomorphic structures are both yes-instances or both
no-instances. Invariance is part of the notion, as in finite model theory: a
problem cannot tell apart two presentations of the same structure.
Finiteness is not built in; it is a hypothesis of every statement that needs
it, and every complexity-theoretic notion below reads a problem on its
finite instances only.
-/

namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
