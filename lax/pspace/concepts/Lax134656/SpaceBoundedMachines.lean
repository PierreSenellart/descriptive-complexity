import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Lax904597.Problems
import Lax485149.Problems
import Lax904597.Machines
import Lax535992.DeterministicMachines

/-!
---
title: Acceptance by Turing machines in bounded space
type: definition
---
An instance is a machine instance of the NP core: a finite structure
describing a Turing machine with its input and a linear order of positions.
The machine accepts in bounded space when some run from an initial
configuration reaches an accepting state, whatever its length: the tape is
the set of positions, so the space is bounded by the instance, while the
number of steps is not. An instance is a yes-instance of machine acceptance
in bounded space when it is well formed and accepts in this sense, and of
its deterministic variant when the machine is moreover deterministic; each
problem is the decision problem of the structures isomorphic to such an
instance.
-/

namespace Lax134656.SpaceBoundedMachines

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Machines Lax485149.Problems Lax535992.DeterministicMachines

namespace TMData

variable {A : Type} (M : TMData A)

/-- **Acceptance in bounded space**: some run from an initial configuration
reaches an accepting state, with *no bound on its length*. The space is
bounded by construction, the tape being indexed by the positions; a run may
visit exponentially many configurations, so acceptance is reachability in the
configuration graph. -/
def AcceptsSpace : Prop :=
  ∃ c₀ c : Config A, M.IsInit c₀ ∧ Relation.ReflTransGen M.Step c₀ c ∧ M.Acc c.state

end TMData

/-- The instance is a well-formed machine accepting in bounded space. -/
def NTMAcceptsSpace (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.AcceptsSpace (tmData A)

/-- The instance is a well-formed deterministic machine accepting in bounded
space. -/
def DTMAcceptsSpace (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ TMData.AcceptsSpace (tmData A)

/-- Machine acceptance in bounded space. -/
def NTMAcceptSpace : DecisionProblem turing :=
  DecisionProblem.ofPred fun A _ => NTMAcceptsSpace A

/-- Deterministic machine acceptance in bounded space. -/
def DTMAcceptSpace : DecisionProblem turing :=
  DecisionProblem.ofPred fun A _ => DTMAcceptsSpace A

end Lax134656.SpaceBoundedMachines
