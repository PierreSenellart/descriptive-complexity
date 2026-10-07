import Lax794877.WorldsValues
import Lax794877.WorldCount
import Lax794877.WorldsInSharpP
import Lax794877.ProbabilityRatio
import Lax794877.H0Complete
import Lax794877.HierarchicalQueryInFP
import Lax794877.ExampleDatabaseProbability
import Lax859101.BipartiteComplete
import Lax859101.BipartiteValues
import Lax859101.CountingBipartite
import Lax794877Proofs.DescriptiveComplexity.Counting.FP
import Lax794877Proofs.DescriptiveComplexity.Counting.PossibleWorlds
import Lax794877Proofs.DescriptiveComplexity.Counting.Reduction
import Lax794877Proofs.DescriptiveComplexity.Counting.SharpP
import Lax794877Proofs.DescriptiveComplexity.Counting.UnitWeights
import Lax794877Proofs.DescriptiveComplexity.Counting.WeightedWorlds
import Lax794877Proofs.DescriptiveComplexity.Examples.ProbabilisticQueries
import Lax794877Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingBipartite

/-!
# Probabilistic query evaluation, from the library's theorems

The world counts are bundled in the concepts from the numbers they count, and
agree with the library's through the invariance of these numbers. Hardness
follows the library's reductions, from #PP2DNF of the required submission.
-/

namespace Lax794877Proofs.Bridge

open Lax904597.SecondOrder
open FirstOrder
open Language Structure
open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder
open FirstOrder.Language
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic
open Lax859101.OneCallReductions Lax904597.Machines
open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- For an invariant number, the problem it gives takes that number. -/
theorem ofFun_eq {L : Language.{0, 0}} [L.IsRelational] {f : ∀ (A : Type) [L.Structure A], ℕ}
    (hf : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → f A = f B)
    (A : Type) [L.Structure A] : CountingProblem.ofFun f A = f A := by
  show sInf _ = _
  have hs : {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n} =
      {f A} := by
    ext n
    constructor
    · rintro ⟨B, i, g, rfl⟩
      exact hf g
    · intro h
      exact ⟨A, inferInstance, Language.Equiv.refl _ _, h.symm⟩
  rw [hs, csInf_singleton]

/-- One-call completeness for the library's #P, transported to the concepts
along an agreement of the problems. -/
theorem oneCallComplete_of_lib {L : Language.{0, 0}} [L.IsRelational] {C C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A], C A = C' A)
        (hc : DescriptiveComplexity.SharpP.OneCallComplete C) :
    OneCallComplete SharpP C' :=
  let ⟨⟨L'', i, D, hD, ⟨f⟩⟩, hh⟩ := hc
  ⟨⟨L'', i, D, hD, ⟨DescriptiveComplexity.OneCallReduction.congrSource (fun A _ _ => h A) f⟩⟩,
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ => h A).mp hh⟩

/-- The library's #PP2DNF and the one of the required submission have the same
values. -/
theorem sharpPP2DNF_agree (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A] :
    DescriptiveComplexity.SharpPP2DNF A = Lax859101.CountingBipartite.SharpPP2DNF A :=
  (Lax859101.BipartiteValues.sharpPP2DNF_eq A).symm

/--
---
conclusion: Lax794877.WorldsValues.possibleWorlds_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem possibleWorlds_count_iso {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence) {A B : Type}
    [(L.sum L).Structure A] [(L.sum L).Structure B] (e : A ≃[L.sum L] B) :
    Nat.card {ρ : (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A
        (worldStructure ρ) φ} =
    Nat.card {ρ : (worldBlock L).Assignment B // IsWorld ρ ∧ @Sentence.Realize L B
        (worldStructure ρ) φ} :=
  (DescriptiveComplexity.possibleWorlds_apply φ A).symm.trans
    (((DescriptiveComplexity.PossibleWorlds φ).iso_invariant e).trans
        (DescriptiveComplexity.possibleWorlds_apply φ B))

/--
---
conclusion: Lax794877.WorldsValues.possibleWorlds_eq
---
The number is invariant, by this submission's statement.
-/
theorem possibleWorlds_eq {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence) (A : Type)
    [(L.sum L).Structure A] : PossibleWorlds φ A = Nat.card {ρ :
        (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ} :=
  ofFun_eq (f := fun A _ => Nat.card {ρ :
      (worldBlock L).Assignment A // IsWorld ρ ∧ @Sentence.Realize L A (worldStructure ρ) φ})
    (fun e => Lax794877.WorldsValues.possibleWorlds_count_iso φ e) A

/-- The library's count of possible worlds and the concept's have the same
values. -/
theorem possibleWorlds_agree {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence)
    (A : Type) [(L.sum L).Structure A] :
    DescriptiveComplexity.PossibleWorlds φ A = PossibleWorlds φ A :=
  (DescriptiveComplexity.possibleWorlds_apply φ A).trans (possibleWorlds_eq φ A).symm

/--
---
conclusion: Lax794877.WorldsValues.weightedWorlds_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem weightedWorlds_count_iso {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence) {A B : Type}
    [(weightedLang L).Structure A] [(weightedLang L).Structure B] (e : A ≃[weightedLang L] B) :
    Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ} =
    Nat.card {σ : (weightBlock L).Assignment B // IsLinOrd (WLe L B) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → B), WeightCond σ p x) ∧
      @Sentence.Realize L B (worldStructure (worldOf σ)) φ} :=
  (DescriptiveComplexity.weightedWorlds_apply φ A).symm.trans
    (((DescriptiveComplexity.WeightedWorlds φ).iso_invariant e).trans
        (DescriptiveComplexity.weightedWorlds_apply φ B))

/--
---
conclusion: Lax794877.WorldsValues.weightedWorlds_eq
---
The number is invariant, by this submission's statement.
-/
theorem weightedWorlds_eq {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence) (A : Type)
    [(weightedLang L).Structure A] : WeightedWorlds φ A = Nat.card {σ :
        (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ} :=
  ofFun_eq (f := fun A _ => Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ})
    (fun e => Lax794877.WorldsValues.weightedWorlds_count_iso φ e) A

/-- The library's count of weighted worlds and the concept's have the same
values. -/
theorem weightedWorlds_agree {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence)
    (A : Type) [(weightedLang L).Structure A] :
    DescriptiveComplexity.WeightedWorlds φ A = WeightedWorlds φ A :=
  (DescriptiveComplexity.weightedWorlds_apply φ A).trans (weightedWorlds_eq φ A).symm

/--
---
conclusion: Lax794877.WorldCount.card_isWorld
---
The library's theorem.
-/
theorem card_isWorld {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]
    {A : Type} [(L.sum L).Structure A]
    [Finite A] : Nat.card {ρ : (worldBlock L).Assignment A // IsWorld ρ} =
      2 ^ Nat.card {q : Σ p : Σ n, L.Relations n, Fin p.1 → A // IsOpenFact q} :=
  DescriptiveComplexity.card_isWorld

/--
---
conclusion: Lax794877.WorldsInSharpP.possibleWorlds_mem_sharpP
---
The library's theorem, transported along the agreement of the problems.
-/
theorem possibleWorlds_mem_sharpP {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence) :
    SharpP.Mem (PossibleWorlds φ) :=
  (DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ => possibleWorlds_agree φ A).mp
    (DescriptiveComplexity.possibleWorlds_mem_sharpP φ)

/--
---
conclusion: Lax794877.WorldsInSharpP.weightedWorlds_mem_sharpP
---
The library's theorem, transported along the agreement of the problems.
-/
theorem weightedWorlds_mem_sharpP {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence) :
    SharpP.Mem (WeightedWorlds φ) :=
  (DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ => weightedWorlds_agree φ A).mp
    (DescriptiveComplexity.weightedWorlds_mem_sharpP φ)

/--
---
conclusion: Lax794877.ProbabilityRatio.worldProb_eq_ratio
---
The library's theorem, the counts replaced along the agreement.
-/
theorem worldProb_eq_ratio {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational]
    {A : Type} [(weightedLang L).Structure A]
    [Finite A] (hlin : IsLinOrd (WLe L A)) (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x) :
    worldProb φ hpos = (WeightedWorlds φ A : ℚ) / (WeightedWorlds (⊤ : L.Sentence) A : ℚ) :=
  by rw [← weightedWorlds_agree, ← weightedWorlds_agree]; exact
      DescriptiveComplexity.worldProb_eq_ratio hlin φ hpos

/--
---
conclusion: Lax794877.ProbabilityRatio.weightedWorlds_of_not_isLinOrd
---
The library's theorem, the count replaced along the agreement.
-/
theorem weightedWorlds_of_not_isLinOrd {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence) (A : Type)
    [(weightedLang L).Structure A] (h : ¬IsLinOrd (WLe L A)) : WeightedWorlds φ A = 0 :=
  (weightedWorlds_agree φ A).symm.trans (DescriptiveComplexity.weightedWorlds_of_not_isLinOrd φ A h)

/--
---
conclusion: Lax794877.H0Complete.possibleWorlds_h0_sharpP_oneCallComplete
---
Membership is the library's; hardness is #PP2DNF's, by the statement of the
required submission, carried along the library's parsimonious reduction.
-/
theorem possibleWorlds_h0_sharpP_oneCallComplete : OneCallComplete SharpP (PossibleWorlds h0) :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard DescriptiveComplexity.SharpPP2DNF :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        sharpPP2DNF_agree A).mpr
      Lax859101.BipartiteComplete.sharpPP2DNF_sharpP_oneCallComplete.2
  oneCallComplete_of_lib (possibleWorlds_agree h0)
    ⟨DescriptiveComplexity.CountingClass.OneCallMem.of_mem
        (DescriptiveComplexity.possibleWorlds_mem_sharpP h0),
      DescriptiveComplexity.CountingClass.OneCallHard.of_parsimonious
          DescriptiveComplexity.sharpPP2DNF_parsimonious_possibleWorlds_h0 hY⟩

/--
---
conclusion: Lax794877.H0Complete.weightedWorlds_h0_sharpP_oneCallComplete
---
Membership is the library's; hardness is that of the uniform case, by this
submission's statement, carried along the library's ordered parsimonious reduction.
-/
theorem weightedWorlds_h0_sharpP_oneCallComplete : OneCallComplete SharpP (WeightedWorlds h0) :=
  have hY : DescriptiveComplexity.SharpP.OneCallHard (DescriptiveComplexity.PossibleWorlds h0) :=
    (DescriptiveComplexity.CountingClass.oneCallHard_congr_finite fun A _ _ =>
        possibleWorlds_agree h0 A).mpr
      Lax794877.H0Complete.possibleWorlds_h0_sharpP_oneCallComplete.2
  oneCallComplete_of_lib (weightedWorlds_agree h0)
    ⟨DescriptiveComplexity.CountingClass.OneCallMem.of_mem
        (DescriptiveComplexity.weightedWorlds_mem_sharpP h0),
      DescriptiveComplexity.CountingClass.OneCallHard.of_orderedParsimonious
        (DescriptiveComplexity.possibleWorlds_ordered_parsimonious_weightedWorlds h0) hY⟩

/--
---
conclusion: Lax794877.HierarchicalQueryInFP.weightedWorlds_rs_mem_FP
---
The library's theorem, transported along the agreement of the problems.
-/
theorem weightedWorlds_rs_mem_FP : FP.Mem (WeightedWorlds rs) :=
  (DescriptiveComplexity.FP.mem_congr_finite fun A _ _ =>
      weightedWorlds_agree rs A).mp DescriptiveComplexity.weightedWorlds_rs_mem_FP

/--
---
conclusion: Lax794877.ExampleDatabaseProbability.probDb_worldProb_eq
---
The library's theorem: the concept's encoded structure is the library's.
-/
theorem probDb_worldProb_eq (i : ProbDb) (hpos : ∀ x : {q : @Fact rst (Fin i.n) // @IsOpen _ _
    (probDbStructure i) q},
      0 < @presWeight _ _ (probDbStructure i) x + @absWeight _ _ (probDbStructure i) x) :
    @worldProb _ _ _ _ (probDbStructure i) _ h0 hpos = (i.count : ℚ) / (i.total : ℚ) :=
  DescriptiveComplexity.probDb_worldProb_eq i hpos

end Lax794877Proofs.Bridge
