/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax280166Proofs.DescriptiveComplexity.Block
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax280166Proofs.DescriptiveComplexity.SecondOrder
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

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques

namespace Lax280166Proofs.DescriptiveComplexity.CliqueOfSize
end Lax280166Proofs.DescriptiveComplexity.CliqueOfSize

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CliqueOfSize)
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
# #Clique: counting the cliques of the threshold size

The counting version of `DescriptiveComplexity.Clique`: the number of cliques having
*exactly* as many vertices as the marked set (`DescriptiveComplexity.CliqueOfSize`).
Its support is Clique, a clique at least as large as the threshold containing
one of exactly that size.

Membership in `#P` (`DescriptiveComplexity.sharpClique_mem_sharpP`) is the first in the
catalog whose kernel reads the order of the instance. The `Σ₁` definition of
Clique certifies the threshold by an injection of the marked set into the
clique, and a clique has many; even for the exact size, a bijection is one
among `k!`. The counting kernel asks for the *monotone* one, which exists and
is unique on a finite linear order. That argument is generic
(`DescriptiveComplexity.sharpPDefinable_of_sized_set`), and what this file supplies is
the order-free part: a set is a clique (`DescriptiveComplexity.cliqueSelKernel`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

variable {A} {B : Type} [Lax799700.CliqueFamily.markedGraph.Structure B]

/-- Cliques of the threshold size transport along an isomorphism. -/
theorem CliqueOfSize.map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) {S : A → Prop}
    (h : Lax280166.CountingCliques.CliqueOfSize A S) : Lax280166.CountingCliques.CliqueOfSize B fun b => S (e.toEquiv.symm b) := by
  obtain ⟨hfin, hcl, hcard⟩ := h
  refine ⟨Finite.of_equiv A e.toEquiv, fun x y hx hy hxy => ?_, ?_⟩
  · have h' := (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj (e.toEquiv.symm x) (e.toEquiv.symm y)).mp
      (hcl _ _ hx hy fun h => hxy (e.toEquiv.symm.injective h))
    have hx' : e (e.toEquiv.symm x) = x := e.toEquiv.apply_symm_apply x
    have hy' : e (e.toEquiv.symm y) = y := e.toEquiv.apply_symm_apply y
    rw [hx', hy'] at h'
    exact h'
  · exact ((ncard_setOf_symm e.toEquiv S).symm.trans hcard).trans
      (ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a)

end Solutions

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166.CountingCliques.CliqueOfSize

export Lax280166Proofs.DescriptiveComplexity.CliqueOfSize (map)

end Lax280166.CountingCliques.CliqueOfSize

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

variable {A} {B : Type} [Lax799700.CliqueFamily.markedGraph.Structure B]

end Solutions

/-! ### The order-free kernel -/

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive CliqueSelBlockIx where
/-- The clique. -/

  | sel
  deriving DecidableEq

instance : Fintype _root_.Lax280166Proofs.DescriptiveComplexity.CliqueSelBlockIx :=
  ⟨List.toFinset [.sel], by intro x; cases x <;> simp⟩

/-- The block of the counting definition of Clique: the clique itself. Its
size is certified generically, by `DescriptiveComplexity.sharpPDefinable_of_sized_set`. -/
def cliqueSelBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax280166Proofs.DescriptiveComplexity.CliqueSelBlockIx
  arity := fun i =>
    match i with
    | .sel => 1

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev cliqueSelLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.cliqueSelBlock)

/-- The `adj` symbol over the sum. -/
abbrev csAdjSym : (_root_.Lax280166Proofs.DescriptiveComplexity.cliqueSelLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev csMarkedSym : (_root_.Lax280166Proofs.DescriptiveComplexity.cliqueSelLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `sel` relation variable. -/
def csSelRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax280166Proofs.DescriptiveComplexity.cliqueSelBlock).Relations 1 :=
  ⟨.sel, rfl⟩

/-- The `sel` symbol over the sum. -/
abbrev csSelSym : (_root_.Lax280166Proofs.DescriptiveComplexity.cliqueSelLang).Relations 1 :=
  Sum.inr _root_.Lax280166Proofs.DescriptiveComplexity.csSelRel

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

instance : Subsingleton cliqueSelBlock.ι :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The order-free kernel of #Clique: the guessed set is a clique. -/
noncomputable def cliqueSelKernel : cliqueSelLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₁ csSelSym (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
              FirstOrder.Language.Relations.formula₁ csSelSym (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
            FirstOrder.Language.BoundedFormula.not
              (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1)))).imp
        (FirstOrder.Language.Relations.formula₂ csAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 1))))

/-- Realization of the order-free kernel of #Clique. -/
theorem realize_cliqueSelKernel {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    (ρ : cliqueSelBlock.Assignment A) :
    (@Sentence.Realize cliqueSelLang A
        (@sumStructure _ _ A _ (cliqueSelBlock.structure ρ)) cliqueSelKernel) ↔
      ∀ a b : A, (ρ .sel fun _ => a) → (ρ .sel fun _ => b) → a ≠ b → Lax799700.CliqueFamily.MGAdj a b := by
  let := cliqueSelBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := cliqueSelLang) (M := A) csSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [cliqueSelKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub,
    Matrix.cons_val_zero]
  exact ⟨fun h a b ha hb hab => h ![a, b] ⟨⟨ha, hb⟩, hab⟩,
    fun h i hi => h (i 0) (i 1) hi.1.1 hi.1.2 hi.2⟩

/-! ### The counting problem -/

/-- **#Clique**: the number of cliques with exactly as many vertices as the
marked set. -/
noncomputable def SharpClique : Lax366625.CountingProblems.CountingProblem Lax799700.CliqueFamily.markedGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Lax280166.CountingCliques.CliqueOfSize A inst S}
  iso_invariant := fun {A B} _ _ e => by
    refine Nat.card_congr
      { toFun := fun S => ⟨fun b => S.1 (e.toEquiv.symm b), S.2.map e⟩
        invFun := fun T => ⟨fun a => T.1 (e.toEquiv a), ?_⟩
        left_inv := fun S => Subtype.ext (funext fun a => by simp)
        right_inv := fun T => Subtype.ext (funext fun b => by simp) }
    have h := T.2.map e.symm
    exact h

theorem sharpClique_apply (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpClique A = Nat.card {S : A → Prop // Lax280166.CountingCliques.CliqueOfSize A S} :=
  rfl

/-- **The support of #Clique is Clique**: a clique at least as large as the
marked set contains one of exactly that size. -/
theorem sharpClique_support_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpClique.support A ↔ Clique A := by
  rw [CountingProblem.support_iff, sharpClique_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨S, hfin, hS, hcard⟩, -⟩
    exact ⟨hfin, S, hS, hcard.ge⟩
  · rintro ⟨hfin, S, hS, hcard⟩
    obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq hcard
    exact ⟨⟨⟨fun x => x ∈ T, hfin, fun x y hx hy hxy => hS x y (hTS hx) (hTS hy) hxy, hT⟩⟩,
      inferInstance⟩

/-- **#Clique is in `#P`**: a clique of the threshold size has exactly one
monotone bijection with the marked set. -/
theorem sharpClique_mem_sharpP : SharpClique ∈ SharpP :=
  sharpPDefinable_of_sized_set SharpClique cliqueSelBlock Lax799700.CliqueFamily.mgMarked .sel rfl cliqueSelKernel
    (fun A _ S => ∀ a b : A, S a → S b → a ≠ b → Lax799700.CliqueFamily.MGAdj a b)
    (fun _ _ ρ => realize_cliqueSelKernel ρ)
    fun _ _ hfin => Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)

end Lax280166Proofs.DescriptiveComplexity


