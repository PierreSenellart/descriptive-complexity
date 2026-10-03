/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Vocabulary
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
# 3-dimensional matching: definition

3-DIMENSIONAL MATCHING ([Karp 1972][karp1972reducibility]): given three
marked classes and a set of triples, one element from each class, is there a
set of triples covering every marked element **exactly once**?

The vocabulary `FirstOrder.Language.tripleSys` carries three unary marks
`xEl`, `yEl`, `zEl` and one ternary relation `trip`. A yes-instance is one
admitting a *matching* (`Lax799700Proofs.DescriptiveComplexity.IsMatchingOn`): a sub-relation of
`trip`, inside the three classes, that covers each marked element exactly
once. Nothing asks the three classes to be disjoint or to exhaust the
universe: elements outside them ride along, and the reduction of
`Lax799700Proofs.DescriptiveComplexity.Problems.ThreeDimMatching.Hardness` produces disjoint ones
anyway.

Perfect matchings force the three classes to have the same size, which is why
the problem is the tripartite form of Exact Cover with sets of size three, and
why it is the natural source of the exact-cover family.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The shorthands of the vocabulary -/

section Shorthands

variable {A : Type} [Lax799700.ThreeDimMatching.tripleSys.Structure A]

end Shorthands

/-! ### Matchings -/

section Matching

variable {A : Type}

end Matching

/-! ### The problem -/

section Problem

variable (A : Type) [Lax799700.ThreeDimMatching.tripleSys.Structure A]

end Problem

section Iso

variable {A B : Type} [Lax799700.ThreeDimMatching.tripleSys.Structure A] [Lax799700.ThreeDimMatching.tripleSys.Structure B]

private theorem hasThreeDimMatching_of_iso (e : A ≃[Lax799700.ThreeDimMatching.tripleSys] B)
    (h : Lax799700.ThreeDimMatching.HasThreeDimMatching A) : Lax799700.ThreeDimMatching.HasThreeDimMatching B := by
  obtain ⟨hfin, M, hsub, hx, hy, hz, hux, huy, huz⟩ := h
  have hX : ∀ a : A, Lax799700.ThreeDimMatching.TSXEl a ↔ Lax799700.ThreeDimMatching.TSXEl (e a) := fun a => relMap_equiv₁ e Lax799700.ThreeDimMatching.tsXEl a
  have hY : ∀ a : A, Lax799700.ThreeDimMatching.TSYEl a ↔ Lax799700.ThreeDimMatching.TSYEl (e a) := fun a => relMap_equiv₁ e Lax799700.ThreeDimMatching.tsYEl a
  have hZ : ∀ a : A, Lax799700.ThreeDimMatching.TSZEl a ↔ Lax799700.ThreeDimMatching.TSZEl (e a) := fun a => relMap_equiv₁ e Lax799700.ThreeDimMatching.tsZEl a
  have hT : ∀ a b c : A, Lax799700.ThreeDimMatching.TSTrip a b c ↔ Lax799700.ThreeDimMatching.TSTrip (e a) (e b) (e c) := fun a b c =>
    relMap_equiv₃ e Lax799700.ThreeDimMatching.tsTrip a b c
  refine ⟨e.toEquiv.finite_iff.mp hfin,
    fun x y z => M (e.symm x) (e.symm y) (e.symm z), fun x y z hm => ?_, fun x hx' => ?_,
    fun y hy' => ?_, fun z hz' => ?_, fun x y z y' z' h₁ h₂ => ?_,
    fun x y z x' z' h₁ h₂ => ?_, fun x y z x' y' h₁ h₂ => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hsub _ _ _ hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using (hT _ _ _).mp h₁
    · simpa using (hX _).mp h₂
    · simpa using (hY _).mp h₃
    · simpa using (hZ _).mp h₄
  · obtain ⟨y, z, hyz⟩ := hx (e.symm x) ((hX _).mpr (by simpa using hx'))
    exact ⟨e y, e z, by simpa using hyz⟩
  · obtain ⟨x, z, hxz⟩ := hy (e.symm y) ((hY _).mpr (by simpa using hy'))
    exact ⟨e x, e z, by simpa using hxz⟩
  · obtain ⟨x, y, hxy⟩ := hz (e.symm z) ((hZ _).mpr (by simpa using hz'))
    exact ⟨e x, e y, by simpa using hxy⟩
  · obtain ⟨h₃, h₄⟩ := hux _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huy _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huz _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩

/-- Having a 3-dimensional matching is isomorphism-invariant. -/
theorem hasThreeDimMatching_iso (e : A ≃[Lax799700.ThreeDimMatching.tripleSys] B) :
    Lax799700.ThreeDimMatching.HasThreeDimMatching A ↔ Lax799700.ThreeDimMatching.HasThreeDimMatching B :=
  ⟨hasThreeDimMatching_of_iso e, hasThreeDimMatching_of_iso e.symm⟩

end Iso

/-- 3-DIMENSIONAL MATCHING, as a problem on triple systems: do some of the
triples cover every marked element exactly once? -/
def ThreeDimMatching : Lax904597.Problems.DecisionProblem Lax799700.ThreeDimMatching.tripleSys where
  Holds := fun A inst => @Lax799700.ThreeDimMatching.HasThreeDimMatching A inst
  iso_invariant := fun e => hasThreeDimMatching_iso e

end Lax799700Proofs.DescriptiveComplexity


