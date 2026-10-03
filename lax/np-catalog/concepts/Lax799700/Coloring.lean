import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Order
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Lax799700.CliqueFamily
import Lax904597.Classes
import Lax799700.Problems

/-!
---
title: Coloring, chromatic number and clique cover
type: theorem
---
Three problems built on one generic property, ColorableOn: a map into
$k$ colors separating the pairs related by a conflict relation. KCol $k$,
on graphs, asks whether the graph is $k$-colorable for a $k$ fixed once
and for all, and is NP-complete for every $k \geq 3$ by a first-order
reduction from 3-colorability. ChromaticNumber, on marked graphs, asks
whether the chromatic number is at most $k$ where $k$ is the cardinality
of the marked set, the unary representation of a threshold; this is
Karp's CHROMATIC NUMBER, and it is NP-hard by an ordered first-order
reduction from 3-colorability. CliqueCover, on the same vocabulary, asks
whether the vertices can be covered by at most $k$ cliques; a clique
cover is a proper coloring of the complement graph, so the first-order
interpretation complementing the edges off the diagonal reduces
Chromatic Number to Clique Cover.

The two threshold problems take their conflict relation off the diagonal,
so they are about the underlying loopless graph. Their existential
second-order definitions guess a coloring in palette form, a map into the
marked set itself, since the number $k$ is not available to a formula.

-/

namespace Lax799700.Coloring

open Lax799700.CliqueFamily

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

/-- A `k`-coloring for the conflict relation `Cfl`: a map into `Fin k` giving
distinct values to conflicting elements. -/
def ColorableOn (Cfl : A → A → Prop) (k : ℕ) : Prop :=
  ∃ c : A → Fin k, ∀ x y, Cfl x y → c x ≠ c y

end Generic

section Fixed

variable (k : ℕ) (V : Type) [Language.graph.Structure V]

/-- A `Language.graph`-structure is `k`-colorable if the vertices can be
colored with `k` colors so that adjacent vertices get distinct colors. -/
def KColorable : Prop :=
  ColorableOn (fun x y : V => RelMap adj ![x, y]) k

end Fixed

section Conflicts

variable {A : Type} [markedGraph.Structure A]

/-- The conflict relation of the chromatic-number problem: adjacency off the
diagonal. -/
def MGConflict (x y : A) : Prop := x ≠ y ∧ MGAdj x y

/-- The conflict relation of the clique-cover problem: non-adjacency off the
diagonal – two vertices may share a clique exactly when they are adjacent. -/
def MGCoConflict (x y : A) : Prop := x ≠ y ∧ ¬MGAdj x y

end Conflicts

section Threshold

variable (A : Type) [markedGraph.Structure A]

/-- A marked graph has chromatic number at most the size of its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallChromaticNumber : Prop :=
  Finite A ∧ ColorableOn (MGConflict (A := A)) {x : A | MGMarked x}.ncard

/-- A marked graph can be covered by at most as many cliques as its marked
set has elements. -/
def HasSmallCliqueCover : Prop :=
  Finite A ∧ ColorableOn (MGCoConflict (A := A)) {x : A | MGMarked x}.ncard

end Threshold

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `HasSmallChromaticNumber` is isomorphism-invariant. -/
axiom hasSmallChromaticNumber_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasSmallChromaticNumber A ↔ HasSmallChromaticNumber B)

/-- The problem ChromaticNumber: does the structure satisfy `HasSmallChromaticNumber`? -/
def ChromaticNumber : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasSmallChromaticNumber

/-- The yes-instances of ChromaticNumber are exactly the structures satisfying
`HasSmallChromaticNumber`. -/
axiom chromaticNumber_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], ChromaticNumber A ↔ HasSmallChromaticNumber A

/-- ChromaticNumber is NP-complete. -/
axiom chromaticNumber_NP_complete : NP.Complete ChromaticNumber

/-- The property `HasSmallCliqueCover` is isomorphism-invariant. -/
axiom hasSmallCliqueCover_iso : ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B],
  (A ≃[Lax799700.CliqueFamily.markedGraph] B) → (HasSmallCliqueCover A ↔ HasSmallCliqueCover B)

/-- The problem CliqueCover: does the structure satisfy `HasSmallCliqueCover`? -/
def CliqueCover : DecisionProblem Lax799700.CliqueFamily.markedGraph :=
  DecisionProblem.ofPred HasSmallCliqueCover

/-- The yes-instances of CliqueCover are exactly the structures satisfying
`HasSmallCliqueCover`. -/
axiom cliqueCover_iff : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], CliqueCover A ↔ HasSmallCliqueCover A

/-- CliqueCover is NP-complete. -/
axiom cliqueCover_NP_complete : NP.Complete CliqueCover

/-- The property `KColorable k` is isomorphism-invariant, for every `k`. -/
axiom kColorable_iso : ∀ {k : ℕ} {A B : Type} [FirstOrder.Language.graph.Structure A]
  [FirstOrder.Language.graph.Structure B],
  (A ≃[FirstOrder.Language.graph] B) → (KColorable k A ↔ KColorable k B)

/-- The problem KCol k: is the graph k-colorable? -/
def KCol (k : ℕ) : DecisionProblem FirstOrder.Language.graph :=
  DecisionProblem.ofPred (KColorable k)

/-- The yes-instances of KCol k are exactly the k-colorable graphs. -/
axiom kCol_iff : ∀ (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A],
  KCol k A ↔ KColorable k A

/-- k-colorability is NP-complete for every k ≥ 3. -/
axiom kCol_NP_complete : ∀ {k : ℕ}, 3 ≤ k → NP.Complete (KCol k)

end Lax799700.Coloring
