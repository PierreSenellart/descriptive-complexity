import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: SAT-UNSAT
type: definition
---
An instance is a pair of CNF formulas on one universe: a structure with two
copies of the vocabulary of CNF instances, one for each formula. It is a
yes-instance of SAT-UNSAT when the first formula is satisfiable and the
second is not. SAT-UNSAT is the decision problem of the structures
isomorphic to such an instance.
-/

namespace Lax564036.SatUnsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of *pairs* of CNF instances: two copies of
the symbols of CNF instances, one per side. -/
inductive satPairRel : ℕ → Type
  /-- `isClause₁ c`: `c` is a clause of the first formula. -/
  | isClause₁ : satPairRel 1
  /-- `posIn₁ c x`: `x` occurs positively in the first formula's clause `c`. -/
  | posIn₁ : satPairRel 2
  /-- `negIn₁ c x`: `x` occurs negatively in the first formula's clause `c`. -/
  | negIn₁ : satPairRel 2
  /-- `isClause₂ c`: `c` is a clause of the second formula. -/
  | isClause₂ : satPairRel 1
  /-- `posIn₂ c x`: `x` occurs positively in the second formula's clause `c`. -/
  | posIn₂ : satPairRel 2
  /-- `negIn₂ c x`: `x` occurs negatively in the second formula's clause `c`. -/
  | negIn₂ : satPairRel 2
  deriving DecidableEq

/-- The relational vocabulary of pairs of CNF instances. -/
def satPair : Language :=
  ⟨fun _ => Empty, satPairRel⟩

instance instIsRelationalSatPair : IsRelational satPair := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- “Is a clause of the first formula”. -/
abbrev spIsCl₁ : satPair.Relations 1 := .isClause₁

/-- “Occurs positively in”, first formula. -/
abbrev spPos₁ : satPair.Relations 2 := .posIn₁

/-- “Occurs negatively in”, first formula. -/
abbrev spNeg₁ : satPair.Relations 2 := .negIn₁

/-- “Is a clause of the second formula”. -/
abbrev spIsCl₂ : satPair.Relations 1 := .isClause₂

/-- “Occurs positively in”, second formula. -/
abbrev spPos₂ : satPair.Relations 2 := .posIn₂

/-- “Occurs negatively in”, second formula. -/
abbrev spNeg₂ : satPair.Relations 2 := .negIn₂

open FirstOrder

open Language Structure

section Defs

variable (A : Type) [satPair.Structure A]

/-- Satisfiability of the side of the instance read by the given triple of
symbols: some assignment of truth values makes every clause of that side
contain a true literal. Both sides of SAT-UNSAT are instances of this. -/
def SatWith (isCl : satPair.Relations 1)
    (pos neg : satPair.Relations 2) : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap isCl ![c] →
    ∃ x : A, (RelMap pos ![c, x] ∧ ν x) ∨ (RelMap neg ![c, x] ∧ ¬ν x)

end Defs

/-- SAT-UNSAT: the first formula of the pair is satisfiable and the second is
not. -/
def SATUNSAT : DecisionProblem satPair :=
  DecisionProblem.ofPred fun A _ =>
    SatWith A spIsCl₁ spPos₁ spNeg₁ ∧ ¬SatWith A spIsCl₂ spPos₂ spNeg₂

end Lax564036.SatUnsat
