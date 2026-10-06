/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Problems.DominatingSet.Defs
import Lax280166Proofs.DescriptiveComplexity.Counting.Sized
import Lax280166Proofs.DescriptiveComplexity.Counting.Class
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

namespace Lax280166.CountingDominatingSets
end Lax280166.CountingDominatingSets

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingDominatingSets (DomOfSizeOn DomSetOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph mgAdj mgMarked)
end FirstOrder.Language

/-!
# #Dominating Set: counting the dominating sets of the threshold size

The counting version of `DescriptiveComplexity.DominatingSet`: the number of
dominating sets with *exactly* as many vertices as the marked set
(`DescriptiveComplexity.DomSetOfSize`). Its support is Dominating Set, a dominating
set smaller than the threshold extending to one of exactly that size
(`DescriptiveComplexity.sharpDominatingSet_support_iff`).

Membership in `#P` (`DescriptiveComplexity.sharpDominatingSet_mem_sharpP`) is the
generic argument for a solution of the threshold size
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), domination being first-order.
Parsimonious hardness is in
`DescriptiveComplexity.Problems.DominatingSet.CountingHardness`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The dominating sets of the threshold size transport along an equivalence
commuting with the two predicates. -/
def domOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    {D : B → Prop // Finite B ∧ Lax280166.CountingDominatingSets.DomOfSizeOn AdjB KB D} ≃
      {D : A → Prop // Finite A ∧ Lax280166.CountingDominatingSets.DomOfSizeOn AdjA KA D} where
  toFun D := ⟨fun a => D.1 (u.symm a), u.finite_iff.mp D.2.1, fun v => by
      rcases D.2.2.1 (u.symm v) with h | ⟨w, hw, hadjw⟩
      · exact Or.inl h
      · have h := (hadj w (u.symm v)).mp hadjw
        exact Or.inr ⟨u w, by simpa using hw, by simpa using h⟩,
    (ncard_setOf_symm u D.1).symm.trans (D.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1, fun v => by
      rcases T.2.2.1 (u v) with h | ⟨w, hw, hadjw⟩
      · exact Or.inl h
      · exact Or.inr ⟨u.symm w, by simpa using hw, (hadj _ _).mpr (by simpa using hadjw)⟩,
    ((ncard_setOf_equiv u (KB := fun b => T.1 (u b)) (KA := T.1) fun _ => Iff.rfl).trans
      T.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv D := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

end Generic

section Solutions

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Solutions

/-- **#Dominating Set**: the number of dominating sets with exactly as many
vertices as the marked set. -/
noncomputable def SharpDominatingSet : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {D : A → Prop // @Lax280166.CountingDominatingSets.DomSetOfSize A inst D}
  iso_invariant := fun e => Nat.card_congr
    (domOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a a')
      fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

theorem sharpDominatingSet_apply (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpDominatingSet A = Nat.card {D : A → Prop // Lax280166.CountingDominatingSets.DomSetOfSize A D} :=
  rfl

/-- **The support of #Dominating Set is Dominating Set**: a dominating set at
most as large as the marked set extends to one of exactly that size. -/
theorem sharpDominatingSet_support_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Finite A] : SharpDominatingSet.support A ↔ DominatingSet A := by
  rw [CountingProblem.support_iff, sharpDominatingSet_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨D, hfin, hdom, hcard⟩, -⟩
    exact ⟨hfin, D, hdom, hcard.le⟩
  · rintro ⟨hfin, D, hdom, hcard⟩
    obtain ⟨T, hDT, hT⟩ := exists_superset_ncard_eq hcard
      (Set.ncard_le_card {v : A | Lax799700.CliqueFamily.MGMarked v})
    refine ⟨⟨⟨fun v => v ∈ T, hfin, fun v => ?_, hT⟩⟩, inferInstance⟩
    rcases hdom v with h | ⟨u, hu, hadj⟩
    · exact Or.inl (hDT h)
    · exact Or.inr ⟨u, hDT hu, hadj⟩

/-! ### Membership -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive DomSelBlockIx where
/-- The dominating set. -/

  | sel
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.DomSelBlockIx :=
  ⟨List.toFinset [.sel], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Dominating Set: the dominating set
itself. -/
def domSelBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.DomSelBlockIx
  arity := fun i =>
    match i with
    | .sel => 1

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev domSelLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.domSelBlock)

/-- The `adj` symbol over the sum. -/
abbrev dmAdjSym : (_root_.Lax280166Proofs.DescriptiveComplexity.domSelLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev dmMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.domSelLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `sel` relation variable. -/
def dmSelRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.domSelBlock).Relations 1 :=
  ⟨.sel, rfl⟩

/-- The `sel` symbol over the sum. -/
abbrev dmSelSym : (_root_.Lax280166Proofs.DescriptiveComplexity.domSelLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.dmSelRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

instance : Subsingleton domSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Dominating Set: every vertex is in the guessed
set or has a neighbor in it. -/
noncomputable def domSelKernel : domSelLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Relations.formula₁ dmSelSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊔
        FirstOrder.Language.Formula.iExs (Fin 1)
          (FirstOrder.Language.Relations.formula₁ dmSelSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
            FirstOrder.Language.Relations.formula₂ dmAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))))

/-- Realization of the order-free kernel of #Dominating Set. -/
theorem realize_domSelKernel {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    (ρ : domSelBlock.Assignment A) :
    (@Sentence.Realize domSelLang A
        (@sumStructure _ _ A _ (domSelBlock.structure ρ)) domSelKernel) ↔
      ∀ v : A, (ρ .sel fun _ => v) ∨ ∃ u : A, (ρ .sel fun _ => u) ∧ Lax799700.CliqueFamily.MGAdj u v := by
  let := domSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := domSelLang) (M := A) dmSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [domSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_sup,
    Formula.realize_inf, Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  constructor
  · intro h v
    rcases h (fun _ => v) with h | ⟨u, hu⟩
    exacts [Or.inl h, Or.inr ⟨u 0, hu⟩]
  · intro h i
    rcases h (i 0) with h | ⟨u, hu⟩
    exacts [Or.inl h, Or.inr ⟨fun _ => u, hu⟩]

/-- **#Dominating Set is in `#P`.** -/
theorem sharpDominatingSet_mem_sharpP : SharpDominatingSet ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpDominatingSet domSelBlock Lax799700.CliqueFamily.mgMarked .sel rfl domSelKernel
    (fun A _ D => ∀ v : A, D v ∨ ∃ u : A, D u ∧ Lax799700.CliqueFamily.MGAdj u v)
    (fun _ _ ρ => realize_domSelKernel ρ)
    fun _ _ hfin => Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)

end Lax280166Proofs.DescriptiveComplexity


