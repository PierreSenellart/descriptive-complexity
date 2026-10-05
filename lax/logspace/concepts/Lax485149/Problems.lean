import Lax904597.Problems

/-!
---
title: Problems given by a property of structures
type: definition
---
The decision problems of the NP core are bundled with a proof that they do
not distinguish isomorphic structures. For the problems of this submission
the bundling is done once and for all: the problem given by a property $\Pi$
of structures has as yes-instances the structures isomorphic to one
satisfying $\Pi$, which is invariant by construction. When $\Pi$ is itself
invariant, as every property here is, this is the problem whose yes-instances
are exactly the structures satisfying $\Pi$; that equivalence is stated,
problem by problem, in a lemma of its own.
-/

namespace Lax485149.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax485149.Problems
