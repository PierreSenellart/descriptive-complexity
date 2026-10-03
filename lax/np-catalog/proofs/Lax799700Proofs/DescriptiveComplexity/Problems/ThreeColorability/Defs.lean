/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Lax799700Proofs.DescriptiveComplexity.Interpretation
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# 3-colorability: definition

A (directed) graph is a `FirstOrder.Language.graph`-structure (already in
Mathlib); `Lax799700Proofs.DescriptiveComplexity.ThreeColorable` is properness of some 3-coloring, and
`Lax799700Proofs.DescriptiveComplexity.ThreeCol` the bundled decision problem. On structures arising
from Mathlib's `SimpleGraph` this agrees with `SimpleGraph.Colorable`
(`Lax799700Proofs.DescriptiveComplexity.threeColorable_iff_colorable`).

The reductions to and from SAT, and NP-completeness, are in
`Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability`.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Graph

variable (V : Type) [Language.graph.Structure V]

end Graph

private theorem threeColorable_of_iso {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) (h : Lax799700.ThreeColorability.ThreeColorable A) :
    Lax799700.ThreeColorability.ThreeColorable B := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun b => c (e.symm b), fun x y hxy => ?_⟩
  exact hc (e.symm x) (e.symm y) ((relMap_equiv₂ e.symm adj x y).mp hxy)

/-- 3-colorability is isomorphism-invariant. -/
theorem threeColorable_iso {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) :
    Lax799700.ThreeColorability.ThreeColorable A ↔ Lax799700.ThreeColorability.ThreeColorable B :=
  ⟨threeColorable_of_iso e, threeColorable_of_iso e.symm⟩

/-- 3-colorability, as a problem on `Language.graph`-structures. -/
def ThreeCol : Lax904597.Problems.DecisionProblem Language.graph where
  Holds := fun V inst => @Lax799700.ThreeColorability.ThreeColorable V inst
  iso_invariant := fun e => threeColorable_iso e

end Lax799700Proofs.DescriptiveComplexity


