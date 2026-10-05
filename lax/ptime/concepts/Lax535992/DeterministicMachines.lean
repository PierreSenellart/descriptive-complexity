import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Machines

/-!
---
title: Acceptance by deterministic Turing machines
type: definition
---
An instance is a machine instance of the NP core: a finite structure
describing a Turing machine, by its transitions and their attributes,
together with its input and a linear order of positions that bounds both
the tape and the number of steps. The machine is deterministic when it has
at most one start state, at most one transition applicable in a given state
on a given symbol, and each transition has at most one destination state
and one written symbol. The instance is a yes-instance of deterministic
machine acceptance when it is well-formed, deterministic, and the machine
accepts its input within the bounds; the problem is the decision problem of
the structures isomorphic to such an instance. Determinism is part of the
problem, not a promise.
-/

namespace Lax535992.DeterministicMachines

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Machines Lax485149.Problems

namespace TMData

variable {A : Type} (M : TMData A)

/-- **Determinism**: one start state, at most one transition applicable in a
given state on a given symbol, and at most one destination and written symbol
per transition. Together with well-formedness this leaves at most one step
from any configuration and at most one initial configuration, so the run is
unique. Every conjunct is first-order. -/
def Deterministic : Prop :=
  (∀ q q', M.Start q → M.Start q' → q = q') ∧
    (∀ τ τ' q a, M.Tr τ → M.Tr τ' → M.Src τ q → M.Src τ' q → M.Read τ a → M.Read τ' a →
      τ = τ') ∧
    (∀ τ q q', M.Dst τ q → M.Dst τ q' → q = q') ∧
    ∀ τ a a', M.Write τ a → M.Write τ a' → a = a'

end TMData

/-- Deterministic machine acceptance: is the machine instance well-formed,
deterministic and accepting within the bounds of the instance? -/
def DTMAccept : DecisionProblem turing :=
  DecisionProblem.ofPred fun A _ =>
    (tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts

end Lax535992.DeterministicMachines
