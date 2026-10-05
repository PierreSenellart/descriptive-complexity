import Lax904597.Problems

/-!
---
title: The complement of a decision problem
type: definition
---
The complement $P^c$ of a decision problem $P$ over a relational vocabulary
has as yes-instances the structures that are no-instances of $P$. It is a
decision problem: a property and its negation are invariant under the same
isomorphisms.
-/

namespace Lax485149.Complement

open Lax904597.Problems

open FirstOrder

open Language

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

end Lax485149.Complement
