/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import FOReduction.Interpretation

/-!
# SAT and 3-colorability as properties of first-order structures

Following descriptive complexity, decision problems are classes of finite
structures over a fixed vocabulary.

* A CNF formula is a `FirstOrder.Language.sat`-structure: elements are clauses
  and propositional variables, `satIsClause c` distinguishes the clauses, and
  `satPosIn c x` / `satNegIn c x` say that the literal `x` / `¬x` occurs in
  clause `c`. `FirstOrder.Satisfiable` is the usual satisfiability.
* A (directed) graph is a `FirstOrder.Language.graph`-structure (already in
  Mathlib); `FirstOrder.ThreeColorable` is properness of some
  3-coloring. On structures arising from Mathlib's `SimpleGraph` this agrees
  with `SimpleGraph.Colorable` (`FirstOrder.threeColorable_iff_colorable`).
-/

namespace FirstOrder

open Language Structure

namespace Language

/-- Relation symbols of the language of CNF instances. -/
inductive satRel : ℕ → Type
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
protected def sat : Language :=
  ⟨fun _ => Empty, satRel⟩
  deriving IsRelational

/-- The symbol for "is a clause". -/
abbrev satIsClause : Language.sat.Relations 1 := .isClause

/-- The symbol for "occurs positively in". -/
abbrev satPosIn : Language.sat.Relations 2 := .posIn

/-- The symbol for "occurs negatively in". -/
abbrev satNegIn : Language.sat.Relations 2 := .negIn

end Language

section Sat

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is satisfiable if some assignment of truth
values to its elements makes every clause contain a true literal. (Elements
that are not variables of the CNF formula may be assigned arbitrarily; they are
harmless since no clause mentions them.) -/
def Satisfiable : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

end Sat

/-- SAT, as a problem on `Language.sat`-structures. -/
def SAT : DecisionProblem Language.sat := fun A inst => @Satisfiable A inst

section Graph

variable (V : Type) [Language.graph.Structure V]

/-- A `Language.graph`-structure is 3-colorable if the vertices can be colored
with 3 colors so that adjacent vertices get distinct colors. (On structures
with self-loops this is never satisfiable, matching the usual convention.) -/
def ThreeColorable : Prop :=
  ∃ c : V → Fin 3, ∀ x y : V, RelMap adj ![x, y] → c x ≠ c y

end Graph

/-- 3-colorability, as a problem on `Language.graph`-structures. -/
def ThreeCol : DecisionProblem Language.graph := fun V inst => @ThreeColorable V inst

/-- On the first-order structure associated to a simple graph,
`ThreeColorable` coincides with Mathlib's `SimpleGraph.Colorable 3`. -/
theorem threeColorable_iff_colorable {V : Type} (G : SimpleGraph V) :
    @ThreeColorable V G.structure ↔ G.Colorable 3 := by
  letI := G.structure
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {u v} h => hc u v h⟩
  · rintro ⟨C⟩
    exact ⟨C, fun u v h => C.valid h⟩

end FirstOrder
