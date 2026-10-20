/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.Problems.Coloring.Membership
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.ModelTheory.Graph
import Lax859101Proofs.DescriptiveComplexity.Interpretation
import Lax859101Proofs.DescriptiveComplexity.Counting.Class
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax859101Proofs.DescriptiveComplexity

/-!
# #3-Colorability: counting the proper 3-colorings

The counting version of `DescriptiveComplexity.ThreeCol`: the number of
proper colorings of a graph with the three colors `Fin 3`
(`DescriptiveComplexity.SharpThreeCol`). It is in `#P`
(`DescriptiveComplexity.sharpThreeCol_mem_sharpP`), the coloring being three
guessed color classes partitioning the vertices; its one-call completeness is
in `DescriptiveComplexity.Problems.ThreeColorability.CountDraw`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Kernel

/-- Kernel clause: no vertex is in two color classes. -/
noncomputable def colExclusiveClause : (kColSOLang 3).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Formula.iInf
        (fun i : Fin 3 =>
          FirstOrder.Language.Formula.iInf
            (fun j : Fin 3 =>
              (FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                ((FirstOrder.Language.Relations.formula₁ (kcColorSym j) (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                  (if i = j then ⊤ else ⊥)))))

/-- The kernel of #3-Colorability: the color classes partition the vertices
and no edge stays inside a class. -/
noncomputable def sharpThreeColKernel : (kColSOLang 3).Sentence :=
  kColKernel 3 ⊓ colExclusiveClause

variable {V : Type} [Language.graph.Structure V]

theorem realize_sharpThreeColKernel (ρ : (colorGuessBlock 3).Assignment V) :
    (@Sentence.Realize (kColSOLang 3) V
        (@sumStructure _ _ V _ ((colorGuessBlock 3).structure ρ)) sharpThreeColKernel) ↔
      ((∀ x : V, ∃ i : Fin 3, ρ i ![x]) ∧
        ∀ x y : V, RelMap adj ![x, y] → ∀ i : Fin 3, ¬(ρ i ![x] ∧ ρ i ![y])) ∧
      ∀ (x : V) (i j : Fin 3), ρ i ![x] → ρ j ![x] → i = j := by
  let := (colorGuessBlock 3).structure ρ
  have hsub : ∀ (i : Fin 3) (w : Fin 1 → V),
      RelMap (L := kColSOLang 3) (M := V) (kcColorSym i) w ↔ ρ i w :=
    fun _ _ => Iff.rfl
  have hw : ∀ w : Fin 1 → V, w = ![w 0] := fun w => funext fun k => by fin_cases k; rfl
  rw [sharpThreeColKernel, kColKernel, colExclusiveClause]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iSup, Formula.realize_iInf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  refine and_congr (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
    ⟨fun h x y hxy i => ?_, fun h i hi j => ?_⟩) ⟨fun h x i j hi hj => ?_, fun h w i j hi hj => ?_⟩
  · obtain ⟨i, hi⟩ := h fun _ => x
    exact ⟨i, hi⟩
  · obtain ⟨j, hj⟩ := h (i 0)
    exact ⟨j, by rw [hw i]; exact hj⟩
  · exact h ![x, y] (by simpa using hxy) i
  · exact h (i 0) (i 1) (by simpa using hi) j
  · have := h (fun _ => x) i j hi hj
    by_contra hij
    rw [if_neg hij] at this
    exact this
  · rw [h (w 0) i j hi hj, if_pos rfl]
    exact Formula.realize_top.mpr trivial

/-- A 3-coloring, as an assignment of the three color classes. -/
def colorAssign (χ : V → Fin 3) : (colorGuessBlock 3).Assignment V :=
  fun i (w : Fin 1 → V) => χ (w 0) = i

/-- **The proper 3-colorings are the witnesses of the kernel.** -/
noncomputable def threeColEquiv (V : Type) [Language.graph.Structure V] :
    {ρ : (colorGuessBlock 3).Assignment V //
        @Sentence.Realize (kColSOLang 3) V
          (@sumStructure _ _ V _ ((colorGuessBlock 3).structure ρ)) sharpThreeColKernel} ≃
      {χ : V → Fin 3 // ∀ x y : V, RelMap adj ![x, y] → χ x ≠ χ y} where
  toFun ρ := ⟨fun x => Classical.choose (((realize_sharpThreeColKernel ρ.1).mp ρ.2).1.1 x),
    fun x y hxy hc => by
      have h := (realize_sharpThreeColKernel ρ.1).mp ρ.2
      have hx := Classical.choose_spec (h.1.1 x)
      have hy := Classical.choose_spec (h.1.1 y)
      change Classical.choose (h.1.1 x) = Classical.choose (h.1.1 y) at hc
      rw [← hc] at hy
      exact h.1.2 x y hxy _ ⟨hx, hy⟩⟩
  invFun χ := ⟨colorAssign χ.1, (realize_sharpThreeColKernel _).mpr
    ⟨⟨fun x => ⟨χ.1 x, rfl⟩, fun x y hxy i hi => χ.2 x y hxy (hi.1.trans hi.2.symm)⟩,
      fun x i j hi hj => hi.symm.trans hj⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have h := (realize_sharpThreeColKernel ρ).mp hρ
    refine Subtype.ext (funext fun i => funext fun (w : Fin 1 → V) => propext ?_)
    have hw : w = ![w 0] := funext fun k => by fin_cases k; rfl
    have hspec := Classical.choose_spec (h.1.1 (w 0))
    constructor
    · intro hc
      change Classical.choose (h.1.1 (w 0)) = i at hc
      rw [hw, ← hc]
      exact hspec
    · intro hi
      change Classical.choose (h.1.1 (w 0)) = i
      rw [hw] at hi
      exact h.2 (w 0) _ _ hspec hi
  right_inv χ := Subtype.ext (funext fun x => by
    have h := Classical.choose_spec (⟨χ.1 x, rfl⟩ : ∃ i, colorAssign χ.1 i ![x])
    exact h.symm)

end Kernel

/-- **#3-Colorability**: the number of proper colorings of a graph with three
colors. -/
noncomputable def SharpThreeCol : Lax366625.CountingProblems.CountingProblem Language.graph where
  Count := fun V inst =>
    Nat.card {χ : V → Fin 3 // ∀ x y : V, @RelMap _ V inst _ adj ![x, y] → χ x ≠ χ y}
  iso_invariant := fun {A B} _ _ e => by
    rw [← Nat.card_congr (threeColEquiv A), ← Nat.card_congr (threeColEquiv B)]
    exact witnessCount_iso (colorGuessBlock 3) sharpThreeColKernel e

theorem sharpThreeCol_apply (V : Type) [Language.graph.Structure V] :
    SharpThreeCol V = Nat.card {χ : V → Fin 3 // ∀ x y : V, RelMap adj ![x, y] → χ x ≠ χ y} :=
  rfl

/-- **#3-Colorability is in `#P`.** -/
theorem sharpThreeCol_mem_sharpP : SharpThreeCol ∈ SharpP :=
  sharpPDefinable_congr (fun V _ _ => Nat.card_congr (threeColEquiv V))
    (sharpPDefinable_ofKernel (colorGuessBlock 3) sharpThreeColKernel)

end Lax859101Proofs.DescriptiveComplexity


