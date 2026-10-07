/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax794877Proofs.DescriptiveComplexity.Counting.WeightedWorlds
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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

namespace Lax794877.PossibleWorlds
end Lax794877.PossibleWorlds

namespace Lax794877.WeightedWorlds
end Lax794877.WeightedWorlds

namespace Lax799700.Common
end Lax799700.Common

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.PossibleWorlds (worldBlock worldStructure)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax794877.WeightedWorlds (Fact IsOpen WLe bitsOf weightedLang)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax799700.Common (binNum bitRank)
end Lax794877Proofs.DescriptiveComplexity

/-!
# Possible worlds are weighted worlds of weight one

The unweighted problem of `DescriptiveComplexity.Counting.PossibleWorlds`,
where every uncertain fact is present with probability `1/2`, is the case of
`DescriptiveComplexity.Counting.WeightedWorlds` in which every fact has the
weights `1` and `1`.

* `DescriptiveComplexity.unitWeightStructure`: the weighted instance of an
  ordered instance, the weight `1` being the single bit of the least position
  (`DescriptiveComplexity.binNum_isBot`);
* `DescriptiveComplexity.weightedWorlds_unitWeight`: its weighted worlds are
  counted like the worlds of the instance, every product of weights being `1`;
* `DescriptiveComplexity.possibleWorlds_ordered_parsimonious_weightedWorlds`:
  the instance is first-order definable
  (`DescriptiveComplexity.unitWeightInterp`), so counting worlds reduces
  parsimoniously to counting weighted worlds. The reduction is an *ordered*
  one: writing the number `1` means naming the least position.

So a hardness result for the unweighted problem is a hardness result for the
weighted one, at uniform probability `1/2`.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

/-- The weighted instance of an instance with certain and uncertain facts,
over a linear order: every weight is `1`, written as the single bit of the
least position. -/
@[instance_reducible]
def unitWeightStructure (A : Type) [(L.sum L).Structure A] [LinearOrder A] :
    (Lax794877.WeightedWorlds.weightedLang L).Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {n} R x =>
    match n, R, x with
    | _, .cert R, x => RelMap (L := L.sum L) (M := A) (Sum.inl R) x
    | _, .unc R, x => RelMap (L := L.sum L) (M := A) (Sum.inr R) x
    | _, .pres _, y => IsBot (y (Fin.last _))
    | _, .abs _, y => IsBot (y (Fin.last _))
    | _, .le, y => y 0 ≤ y 1

section Unit

variable {A : Type} [(L.sum L).Structure A] [LinearOrder A]

/-- The number whose only bit is at the least position is `1`. -/
theorem binNum_isBot [Finite A] [Nonempty A] :
    Lax799700.Common.binNum (fun a b : A => a ≤ b) (fun _ => True) (fun i => IsBot i) = 1 := by
  obtain ⟨b, hb⟩ : ∃ b : A, IsBot b := by
    obtain ⟨b, hb⟩ := Finite.exists_min (id : A → A)
    exact ⟨b, hb⟩
  have hset : {p : A | True ∧ IsBot p} = {b} := by
    ext p
    simp only [Set.mem_ofPred_eq, true_and, Set.mem_singleton_iff]
    exact ⟨fun hp => le_antisymm (hp b) (hb p), fun h => h ▸ hb⟩
  have hrank : Lax799700.Common.bitRank (fun a b : A => a ≤ b) (fun _ => True) b = 0 := by
    rw [Lax799700.Common.bitRank, Set.ncard_eq_zero]
    ext q
    simp only [Set.mem_ofPred_eq, true_and, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact fun hq => le_antisymm hq (hb q)
  rw [Lax799700.Common.binNum, hset, finsum_mem_singleton, hrank, pow_zero]

/-- **With every weight equal to one, counting weighted worlds is counting
worlds.** -/
theorem weightedWorlds_unitWeight [L.IsRelational] [Finite A] [Nonempty A] (φ : L.Sentence) :
    (letI := unitWeightStructure (L := L) A; WeightedWorlds φ A) = PossibleWorlds φ A := by
  let := unitWeightStructure (L := L) A
  have hle : Lax794877.WeightedWorlds.WLe L A = fun a b : A => a ≤ b := rfl
  have hlin : Lax904597.Machines.IsLinOrd (Lax794877.WeightedWorlds.WLe L A) := by
    rw [hle]
    exact ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩
  have hpres : ∀ q : Lax794877.WeightedWorlds.Fact L A, Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe L A) (fun _ => True)
      (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.pres q.1.2) q.2) = 1 := fun q => by
    have h1 : Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.pres q.1.2) q.2 = fun i : A => IsBot i := funext fun i => by
      change IsBot (Fin.snoc (α := fun _ => A) q.2 i (Fin.last _)) = IsBot i
      rw [Fin.snoc_last]
    rw [h1, hle]
    exact binNum_isBot
  have habs : ∀ q : Lax794877.WeightedWorlds.Fact L A, Lax799700.Common.binNum (Lax794877.WeightedWorlds.WLe L A) (fun _ => True)
      (Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.abs q.1.2) q.2) = 1 := fun q => by
    have h1 : Lax794877.WeightedWorlds.bitsOf (Lax794877.WeightedWorlds.WeightedRel.abs q.1.2) q.2 = fun i : A => IsBot i := funext fun i => by
      change IsBot (Fin.snoc (α := fun _ => A) q.2 i (Fin.last _)) = IsBot i
      rw [Fin.snoc_last]
    rw [h1, hle]
    exact binNum_isBot
  have hw : ∀ (ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A) (q : Lax794877.WeightedWorlds.Fact L A), factWeight ρ q = 1 := by
    intro ρ q
    by_cases ho : Lax794877.WeightedWorlds.IsOpen q <;> by_cases hρ : ρ q.1 q.2 <;>
      simp only [factWeight, ho, hρ, ↓reduceIte, hpres, habs]
  let := Fintype.ofFinite {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
    IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ}
  have hsum : (∑ᶠ ρ : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ},
      ∏ᶠ q : Lax794877.WeightedWorlds.Fact L A, factWeight ρ.1 q) =
      ∑ᶠ _ : {ρ : (Lax794877.PossibleWorlds.worldBlock L).Assignment A //
        IsWeightedWorld ρ ∧ @Sentence.Realize L A (Lax794877.PossibleWorlds.worldStructure ρ) φ}, 1 :=
    finsum_congr fun ρ => (finprod_congr fun q => hw ρ.1 q).trans finprod_one
  rw [weightedWorlds_eq_weightSum hlin, possibleWorlds_apply, hsum,
    finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun ρ =>
    and_congr_left' ⟨fun h p x => h ⟨p, x⟩, fun h q => h q.1 q.2⟩)

end Unit

/-! ### The interpretation -/

/-- The certain facts of a symbol, over the ordered expansion. -/
abbrev uwCert {n : ℕ} (R : L.Relations n) : ((L.sum L).sum Language.order).Relations n :=
  Sum.inl (Sum.inl R)

/-- The uncertain facts of a symbol, over the ordered expansion. -/
abbrev uwUnc {n : ℕ} (R : L.Relations n) : ((L.sum L).sum Language.order).Relations n :=
  Sum.inl (Sum.inr R)

/-- The order symbol of the ordered expansion. -/
abbrev uwLe (L : Language.{0, 0}) : ((L.sum L).sum Language.order).Relations 2 :=
  Sum.inr leSymb

/-- The weighted instance of weight one, drawn first-order from an ordered
instance: the facts are kept, the order of the positions is the order of the
instance, and the only bit of every weight is at the least element. -/
noncomputable def unitWeightInterp (L : Language.{0, 0}) :
    Lax904597.Interpretations.FOInterpretation ((L.sum L).sum Language.order) (Lax794877.WeightedWorlds.weightedLang L) Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .cert R => fun _ => Relations.formula (uwCert R) fun m => Term.var (m, 0)
    | _, .unc R => fun _ => Relations.formula (uwUnc R) fun m => Term.var (m, 0)
    | _, .pres _ => fun _ => Formula.iAlls Unit
        (Relations.formula₂ (uwLe L) (Term.var (Sum.inl (Fin.last _, 0))) (Term.var (Sum.inr ())))
    | _, .abs _ => fun _ => Formula.iAlls Unit
        (Relations.formula₂ (uwLe L) (Term.var (Sum.inl (Fin.last _, 0))) (Term.var (Sum.inr ())))
    | _, .le => fun _ => Relations.formula₂ (uwLe L) (Term.var (0, 0)) (Term.var (1, 0))

/-- The interpreted structure is the weighted instance of weight one. -/
noncomputable def unitWeightLEquiv (A : Type) [(L.sum L).Structure A] [LinearOrder A] :
    @Language.Equiv (Lax794877.WeightedWorlds.weightedLang L) ((unitWeightInterp L).Map A) A
      (Lax904597.Interpretations.FOInterpretation.mapStructure (unitWeightInterp L) A) (unitWeightStructure A) :=
  letI := unitWeightStructure (L := L) A
  { toEquiv := (unitWeightInterp L).mapEquivSelf A
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      rw [FOInterpretation.relMap_map]
      cases R with
      | cert R =>
        exact (Formula.realize_rel (M := A) (R := uwCert R)
          (ts := fun m => Term.var (m, (0 : Fin 1)))
          (v := fun p : Fin _ × Fin 1 => (x p.1).2 p.2)).symm
      | unc R =>
        exact (Formula.realize_rel (M := A) (R := uwUnc R)
          (ts := fun m => Term.var (m, (0 : Fin 1)))
          (v := fun p : Fin _ × Fin 1 => (x p.1).2 p.2)).symm
      | pres R =>
        refine Iff.trans ?_ Formula.realize_iAlls.symm
        simp only [Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
        exact ⟨fun h f => h (f ()), fun h a => h fun _ => a⟩
      | abs R =>
        refine Iff.trans ?_ Formula.realize_iAlls.symm
        simp only [Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
        exact ⟨fun h f => h (f ()), fun h a => h fun _ => a⟩
      | le =>
        exact (Formula.realize_rel₂ (M := A) (R := uwLe L)
          (t₁ := Term.var ((0 : Fin 2), (0 : Fin 1))) (t₂ := Term.var ((1 : Fin 2), (0 : Fin 1)))
          (v := fun p : Fin 2 × Fin 1 => (x p.1).2 p.2)).symm }

/-- **Counting possible worlds reduces parsimoniously to counting weighted
worlds**, by giving every fact the weights `1` and `1`. The reduction is
ordered: it names the least position. -/
noncomputable def possibleWorlds_ordered_parsimonious_weightedWorlds [L.IsRelational]
    (φ : L.Sentence) : PossibleWorlds φ ≤ᵖ[≤] WeightedWorlds φ where
  Tag := Unit
  dim := 1
  toInterpretation := unitWeightInterp L
  correct := fun A _ _ _ _ =>
    (weightedWorlds_unitWeight φ).symm.trans
      (@Lax366625.CountingProblems.CountingProblem.iso_invariant _ _ (WeightedWorlds φ) ((unitWeightInterp L).Map A) A
        (Lax904597.Interpretations.FOInterpretation.mapStructure (unitWeightInterp L) A) (unitWeightStructure A)
        (unitWeightLEquiv A)).symm

end Lax794877Proofs.DescriptiveComplexity


