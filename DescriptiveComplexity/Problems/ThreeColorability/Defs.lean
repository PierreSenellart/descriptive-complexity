/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import DescriptiveComplexity.Interpretation

/-!
# 3-colorability: definition

A (directed) graph is a `FirstOrder.Language.graph`-structure (already in
Mathlib); `DescriptiveComplexity.ThreeColorable` is properness of some 3-coloring, and
`DescriptiveComplexity.ThreeCol` the bundled decision problem. On structures arising
from Mathlib's `SimpleGraph` this agrees with `SimpleGraph.Colorable`
(`DescriptiveComplexity.threeColorable_iff_colorable`).

The reductions to and from SAT, and NP-completeness, are in
`DescriptiveComplexity.Problems.ThreeColorability`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Graph

variable (V : Type) [Language.graph.Structure V]

/-- A `Language.graph`-structure is 3-colorable if the vertices can be colored
with 3 colors so that adjacent vertices get distinct colors. (On structures
with self-loops this is never satisfiable, matching the usual convention.) -/
def ThreeColorable : Prop :=
  ∃ c : V → Fin 3, ∀ x y : V, RelMap adj ![x, y] → c x ≠ c y

end Graph

private theorem comp_vec₂ {A B : Type} (f : A → B) (a b : A) : f ∘ ![a, b] = ![f a, f b] := by
  funext j
  fin_cases j <;> simp

private theorem threeColorable_of_iso {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) (h : ThreeColorable A) :
    ThreeColorable B := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun b => c (e.symm b), fun x y hxy => ?_⟩
  refine hc (e.symm x) (e.symm y) ?_
  have h' := StrongHomClass.map_rel e.symm adj ![x, y]
  rw [comp_vec₂] at h'
  exact h'.mpr hxy

/-- 3-colorability is isomorphism-invariant. -/
theorem threeColorable_iso {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) :
    ThreeColorable A ↔ ThreeColorable B :=
  ⟨threeColorable_of_iso e, threeColorable_of_iso e.symm⟩

/-- 3-colorability, as a problem on `Language.graph`-structures. -/
def ThreeCol : DecisionProblem Language.graph where
  Holds := fun V inst => @ThreeColorable V inst
  iso_invariant := fun e => threeColorable_iso e

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

end DescriptiveComplexity
