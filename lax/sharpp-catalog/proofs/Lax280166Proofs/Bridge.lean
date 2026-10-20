import Lax280166.SatVariantsValues
import Lax280166.CliquesValues
import Lax280166.DominatingSetsValues
import Lax280166.FeedbackSetsValues
import Lax280166.HamiltonCircuitsValues
import Lax280166.SetFamiliesValues
import Lax280166.KnapsacksValues
import Lax280166.SteinerTreesValues
import Lax280166.ThreeSATComplete
import Lax280166.OneInSATComplete
import Lax280166.CliqueComplete
import Lax280166.IndependentSetComplete
import Lax280166.VertexCoverComplete
import Lax280166.DominatingSetComplete
import Lax280166.FeedbackVertexSetComplete
import Lax280166.FeedbackArcSetComplete
import Lax280166.DirHamCircuitComplete
import Lax280166.HamCircuitComplete
import Lax280166.ExactCoverComplete
import Lax280166.SetPackingComplete
import Lax280166.SetCoverComplete
import Lax280166.HittingSetComplete
import Lax280166.KnapsackComplete
import Lax280166.ZeroOneIPComplete
import Lax280166.SteinerTreeComplete
import Lax366625.CountingSat
import Lax366625.SharpSatComplete
import Lax366625.SharpSatValue
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
import Lax280166Proofs.DescriptiveComplexity.Problems.DominatingSet.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.DominatingSet.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.ExactCoverCounting
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.CountingArc
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.CountingArcHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CountingUndirected
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CountingUndirectedHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.Knapsack.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.CountingFromSat
import Lax280166Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.CountingCover
import Lax280166Proofs.DescriptiveComplexity.Problems.SetFamily.CountingPacking
import Lax280166Proofs.DescriptiveComplexity.Problems.Steiner.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.Steiner.CountingHardness
import Lax280166Proofs.DescriptiveComplexity.Problems.ThreeSat.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.ThreeSat.CountingFromSat
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.ZeroOneIP.CountingHardness

/-!
# The #P catalog, from the library's theorems

The counting problems are bundled in the concepts from the numbers they count,
and the library's problems agree with them through the invariance of these
numbers. Each completeness theorem takes its membership from the library and
its hardness from the problem it is reduced from, so that the proofs follow
the library's tree of parsimonious reductions rooted at #SAT.
-/

namespace Lax280166Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

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

/-- Counting problems with the same values have the same support. -/
theorem support_congr {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A], C A = D A) (A : Type) [L.Structure A] :
    C.support A ↔ D.support A := by
  show 0 < C A ↔ 0 < D A
  rw [h A]

/-- The library's #SAT and the one of the required submission have the same
values. -/
theorem sharpSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpSAT A = Lax366625.CountingSat.SharpSAT A :=
  (Lax366625.SharpSatValue.sharpSat_eq A).symm

/--
---
conclusion: Lax280166.SatVariantsValues.sharpThreeSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpThreeSat_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν} =
        Nat.card {ν : B → Prop // WidthAtMostThree B ∧ SatModel B ν} :=
  (DescriptiveComplexity.SharpThreeSAT).iso_invariant e

/--
---
conclusion: Lax280166.SatVariantsValues.sharpThreeSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpThreeSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpThreeSAT A = Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν})
      Lax280166.SatVariantsValues.sharpThreeSat_count_iso A

/-- The library's #3SAT and the concept's have the same values. -/
theorem sharpThreeSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpThreeSAT A = SharpThreeSAT A :=
  (sharpThreeSat_eq A).symm

/--
---
conclusion: Lax280166.SatVariantsValues.sharpOneInSat_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpOneInSat_count_iso {A B : Type} [Lax904597.Sat.sat.Structure A]
    [Lax904597.Sat.sat.Structure B]
    (e : A ≃[Lax904597.Sat.sat] B) : Nat.card {ν : A → Prop // OneInModel A ν} = Nat.card {ν : B →
        Prop // OneInModel B ν} :=
  (DescriptiveComplexity.SharpOneInSAT).iso_invariant e

/--
---
conclusion: Lax280166.SatVariantsValues.sharpOneInSat_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpOneInSat_eq (A : Type) [Lax904597.Sat.sat.Structure A] :
    SharpOneInSAT A = Nat.card {ν : A → Prop // OneInModel A ν} :=
  ofFun_eq (f := fun A _ => Nat.card {ν : A → Prop // OneInModel A ν})
      Lax280166.SatVariantsValues.sharpOneInSat_count_iso A

/-- The library's #1-in-SAT and the concept's have the same values. -/
theorem sharpOneInSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] :
    DescriptiveComplexity.SharpOneInSAT A = SharpOneInSAT A :=
  (sharpOneInSat_eq A).symm

/--
---
conclusion: Lax280166.CliquesValues.sharpClique_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpClique_count_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Lax799700.CliqueFamily.markedGraph.Structure B]
    (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) : Nat.card {S : A → Prop // CliqueOfSize A S} =
        Nat.card {S : B → Prop // CliqueOfSize B S} :=
  (DescriptiveComplexity.SharpClique).iso_invariant e

/--
---
conclusion: Lax280166.CliquesValues.sharpClique_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpClique_eq (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpClique A = Nat.card {S : A → Prop // CliqueOfSize A S} :=
  ofFun_eq (f := fun A _ => Nat.card {S : A → Prop // CliqueOfSize A S})
      Lax280166.CliquesValues.sharpClique_count_iso A

/-- The library's #Clique and the concept's have the same values. -/
theorem sharpClique_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpClique A = SharpClique A :=
  (sharpClique_eq A).symm

/--
---
conclusion: Lax280166.CliquesValues.sharpIndependentSet_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpIndependentSet_count_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Lax799700.CliqueFamily.markedGraph.Structure B]
    (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) : Nat.card {S : A → Prop // IndepOfSize A S} =
        Nat.card {S : B → Prop // IndepOfSize B S} :=
  (DescriptiveComplexity.SharpIndependentSet).iso_invariant e

/--
---
conclusion: Lax280166.CliquesValues.sharpIndependentSet_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpIndependentSet_eq (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpIndependentSet A = Nat.card {S : A → Prop // IndepOfSize A S} :=
  ofFun_eq (f := fun A _ => Nat.card {S : A → Prop // IndepOfSize A S})
      Lax280166.CliquesValues.sharpIndependentSet_count_iso A

/-- The library's #Independent Set and the concept's have the same values. -/
theorem sharpIndependentSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpIndependentSet A = SharpIndependentSet A :=
  (sharpIndependentSet_eq A).symm

/--
---
conclusion: Lax280166.CliquesValues.sharpVertexCover_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpVertexCover_count_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Lax799700.CliqueFamily.markedGraph.Structure B]
    (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) : Nat.card {C : A → Prop // CoverOfSize A C} =
        Nat.card {C : B → Prop // CoverOfSize B C} :=
  (DescriptiveComplexity.SharpVertexCover).iso_invariant e

/--
---
conclusion: Lax280166.CliquesValues.sharpVertexCover_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpVertexCover_eq (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpVertexCover A = Nat.card {C : A → Prop // CoverOfSize A C} :=
  ofFun_eq (f := fun A _ => Nat.card {C : A → Prop // CoverOfSize A C})
      Lax280166.CliquesValues.sharpVertexCover_count_iso A

/-- The library's #Vertex Cover and the concept's have the same values. -/
theorem sharpVertexCover_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpVertexCover A = SharpVertexCover A :=
  (sharpVertexCover_eq A).symm

/--
---
conclusion: Lax280166.DominatingSetsValues.sharpDominatingSet_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpDominatingSet_count_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    [Lax799700.CliqueFamily.markedGraph.Structure B]
    (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) : Nat.card {D : A → Prop // DomSetOfSize A D} =
        Nat.card {D : B → Prop // DomSetOfSize B D} :=
  (DescriptiveComplexity.SharpDominatingSet).iso_invariant e

/--
---
conclusion: Lax280166.DominatingSetsValues.sharpDominatingSet_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpDominatingSet_eq (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpDominatingSet A = Nat.card {D : A → Prop // DomSetOfSize A D} :=
  ofFun_eq (f := fun A _ => Nat.card {D : A → Prop // DomSetOfSize A D})
      Lax280166.DominatingSetsValues.sharpDominatingSet_count_iso A

/-- The library's #Dominating Set and the concept's have the same values. -/
theorem sharpDominatingSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpDominatingSet A = SharpDominatingSet A :=
  (sharpDominatingSet_eq A).symm

/--
---
conclusion: Lax280166.FeedbackSetsValues.sharpFeedbackVertexSet_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpFeedbackVertexSet_count_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure
    A] [Lax799700.CliqueFamily.markedGraph.Structure B]
    (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) : Nat.card {C : A → Prop // FvsOfSize A C} =
        Nat.card {C : B → Prop // FvsOfSize B C} :=
  (DescriptiveComplexity.SharpFeedbackVertexSet).iso_invariant e

/--
---
conclusion: Lax280166.FeedbackSetsValues.sharpFeedbackVertexSet_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpFeedbackVertexSet_eq (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    SharpFeedbackVertexSet A = Nat.card {C : A → Prop // FvsOfSize A C} :=
  ofFun_eq (f := fun A _ => Nat.card {C : A → Prop // FvsOfSize A C})
      Lax280166.FeedbackSetsValues.sharpFeedbackVertexSet_count_iso A

/-- The library's #Feedback Vertex Set and the concept's have the same values. -/
theorem sharpFeedbackVertexSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] :
    DescriptiveComplexity.SharpFeedbackVertexSet A = SharpFeedbackVertexSet A :=
  (sharpFeedbackVertexSet_eq A).symm

/--
---
conclusion: Lax280166.FeedbackSetsValues.sharpFeedbackArcSet_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpFeedbackArcSet_count_iso {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A]
    [Lax799700.Feedback.markedArcGraph.Structure B]
    (e : A ≃[Lax799700.Feedback.markedArcGraph] B) : Nat.card {F : A → A → Prop // FasOfSize A F} =
        Nat.card {F : B → B → Prop // FasOfSize B F} :=
  (DescriptiveComplexity.SharpFeedbackArcSet).iso_invariant e

/--
---
conclusion: Lax280166.FeedbackSetsValues.sharpFeedbackArcSet_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpFeedbackArcSet_eq (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] :
    SharpFeedbackArcSet A = Nat.card {F : A → A → Prop // FasOfSize A F} :=
  ofFun_eq (f := fun A _ => Nat.card {F : A → A → Prop // FasOfSize A F})
      Lax280166.FeedbackSetsValues.sharpFeedbackArcSet_count_iso A

/-- The library's #Feedback Arc Set and the concept's have the same values. -/
theorem sharpFeedbackArcSet_agree (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] :
    DescriptiveComplexity.SharpFeedbackArcSet A = SharpFeedbackArcSet A :=
  (sharpFeedbackArcSet_eq A).symm

/--
---
conclusion: Lax280166.HamiltonCircuitsValues.sharpDirHamCircuit_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpDirHamCircuit_count_iso {A B : Type} [Lax799700.Hamilton.digraph.Structure A]
    [Lax799700.Hamilton.digraph.Structure B]
    (e : A ≃[Lax799700.Hamilton.digraph] B) : Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt} =
        Nat.card {Nxt : B → B → Prop // DirCircuit B Nxt} :=
  (DescriptiveComplexity.SharpDirHamCircuit).iso_invariant e

/--
---
conclusion: Lax280166.HamiltonCircuitsValues.sharpDirHamCircuit_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpDirHamCircuit_eq (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    SharpDirHamCircuit A = Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt} :=
  ofFun_eq (f := fun A _ => Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt})
      Lax280166.HamiltonCircuitsValues.sharpDirHamCircuit_count_iso A

/-- The library's #Directed Hamilton Circuit and the concept's have the same values. -/
theorem sharpDirHamCircuit_agree (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    DescriptiveComplexity.SharpDirHamCircuit A = SharpDirHamCircuit A :=
  (sharpDirHamCircuit_eq A).symm

/--
---
conclusion: Lax280166.HamiltonCircuitsValues.sharpHamCircuit_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpHamCircuit_count_iso {A B : Type} [Lax799700.Hamilton.digraph.Structure A]
    [Lax799700.Hamilton.digraph.Structure B]
    (e : A ≃[Lax799700.Hamilton.digraph] B) : Nat.card {E : A → A → Prop // UCircuit A E} =
        Nat.card {E : B → B → Prop // UCircuit B E} :=
  (DescriptiveComplexity.SharpHamCircuit).iso_invariant e

/--
---
conclusion: Lax280166.HamiltonCircuitsValues.sharpHamCircuit_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpHamCircuit_eq (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    SharpHamCircuit A = Nat.card {E : A → A → Prop // UCircuit A E} :=
  ofFun_eq (f := fun A _ => Nat.card {E : A → A → Prop // UCircuit A E})
      Lax280166.HamiltonCircuitsValues.sharpHamCircuit_count_iso A

/-- The library's #Hamilton Circuit and the concept's have the same values. -/
theorem sharpHamCircuit_agree (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    DescriptiveComplexity.SharpHamCircuit A = SharpHamCircuit A :=
  (sharpHamCircuit_eq A).symm

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpExactCover_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpExactCover_count_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
    [Lax799700.SetFamily.setSystem.Structure B]
    (e : A ≃[Lax799700.SetFamily.setSystem] B) : Nat.card {G : A → Prop // ExactCoverBy (SSElem
        (A := A)) SSFam SSMem G} = Nat.card {G : B → Prop // ExactCoverBy (SSElem
            (A := B)) SSFam SSMem G} :=
  (DescriptiveComplexity.SharpExactCover).iso_invariant e

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpExactCover_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpExactCover_eq (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpExactCover A = Nat.card {G : A → Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G} :=
  ofFun_eq (f := fun A _ => Nat.card {G : A → Prop // ExactCoverBy (SSElem
      (A := A)) SSFam SSMem G}) Lax280166.SetFamiliesValues.sharpExactCover_count_iso A

/-- The library's #Exact Cover and the concept's have the same values. -/
theorem sharpExactCover_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SharpExactCover A = SharpExactCover A :=
  (sharpExactCover_eq A).symm

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpSetPacking_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSetPacking_count_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
    [Lax799700.SetFamily.setSystem.Structure B]
    (e : A ≃[Lax799700.SetFamily.setSystem] B) : Nat.card {G : A → Prop // PackingOfSize A G} =
        Nat.card {G : B → Prop // PackingOfSize B G} :=
  (DescriptiveComplexity.SharpSetPacking).iso_invariant e

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpSetPacking_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSetPacking_eq (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpSetPacking A = Nat.card {G : A → Prop // PackingOfSize A G} :=
  ofFun_eq (f := fun A _ => Nat.card {G : A → Prop // PackingOfSize A G})
      Lax280166.SetFamiliesValues.sharpSetPacking_count_iso A

/-- The library's #Set Packing and the concept's have the same values. -/
theorem sharpSetPacking_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SharpSetPacking A = SharpSetPacking A :=
  (sharpSetPacking_eq A).symm

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpSetCover_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSetCover_count_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
    [Lax799700.SetFamily.setSystem.Structure B]
    (e : A ≃[Lax799700.SetFamily.setSystem] B) : Nat.card {G : A → Prop // SetCoverOfSize A G} =
        Nat.card {G : B → Prop // SetCoverOfSize B G} :=
  (DescriptiveComplexity.SharpSetCover).iso_invariant e

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpSetCover_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSetCover_eq (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpSetCover A = Nat.card {G : A → Prop // SetCoverOfSize A G} :=
  ofFun_eq (f := fun A _ => Nat.card {G : A → Prop // SetCoverOfSize A G})
      Lax280166.SetFamiliesValues.sharpSetCover_count_iso A

/-- The library's #Set Cover and the concept's have the same values. -/
theorem sharpSetCover_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SharpSetCover A = SharpSetCover A :=
  (sharpSetCover_eq A).symm

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpHittingSet_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpHittingSet_count_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
    [Lax799700.SetFamily.setSystem.Structure B]
    (e : A ≃[Lax799700.SetFamily.setSystem] B) : Nat.card {H : A → Prop // HittingSetOfSize A H} =
        Nat.card {H : B → Prop // HittingSetOfSize B H} :=
  (DescriptiveComplexity.SharpHittingSet).iso_invariant e

/--
---
conclusion: Lax280166.SetFamiliesValues.sharpHittingSet_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpHittingSet_eq (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    SharpHittingSet A = Nat.card {H : A → Prop // HittingSetOfSize A H} :=
  ofFun_eq (f := fun A _ => Nat.card {H : A → Prop // HittingSetOfSize A H})
      Lax280166.SetFamiliesValues.sharpHittingSet_count_iso A

/-- The library's #Hitting Set and the concept's have the same values. -/
theorem sharpHittingSet_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] :
    DescriptiveComplexity.SharpHittingSet A = SharpHittingSet A :=
  (sharpHittingSet_eq A).symm

/--
---
conclusion: Lax280166.KnapsacksValues.sharpKnapsack_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpKnapsack_count_iso {A B : Type} [Lax799700.Knapsack.binWeights.Structure A]
    [Lax799700.Knapsack.binWeights.Structure B]
    (e : A ≃[Lax799700.Knapsack.binWeights] B) : Nat.card {S : A → Prop // KnapsackSol A S} =
        Nat.card {S : B → Prop // KnapsackSol B S} :=
  (DescriptiveComplexity.SharpKnapsack).iso_invariant e

/--
---
conclusion: Lax280166.KnapsacksValues.sharpKnapsack_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpKnapsack_eq (A : Type) [Lax799700.Knapsack.binWeights.Structure A] :
    SharpKnapsack A = Nat.card {S : A → Prop // KnapsackSol A S} :=
  ofFun_eq (f := fun A _ => Nat.card {S : A → Prop // KnapsackSol A S})
      Lax280166.KnapsacksValues.sharpKnapsack_count_iso A

/-- The library's #Knapsack and the concept's have the same values. -/
theorem sharpKnapsack_agree (A : Type) [Lax799700.Knapsack.binWeights.Structure A] :
    DescriptiveComplexity.SharpKnapsack A = SharpKnapsack A :=
  (sharpKnapsack_eq A).symm

/--
---
conclusion: Lax280166.KnapsacksValues.sharpZeroOneIP_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpZeroOneIP_count_iso {A B : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A]
    [Lax799700.ZeroOneIP.zeroOneIP.Structure B]
    (e : A ≃[Lax799700.ZeroOneIP.zeroOneIP] B) : Nat.card {x : A → Prop // ZeroOneSol A x} =
        Nat.card {x : B → Prop // ZeroOneSol B x} :=
  (DescriptiveComplexity.SharpZeroOneIP).iso_invariant e

/--
---
conclusion: Lax280166.KnapsacksValues.sharpZeroOneIP_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpZeroOneIP_eq (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] :
    SharpZeroOneIP A = Nat.card {x : A → Prop // ZeroOneSol A x} :=
  ofFun_eq (f := fun A _ => Nat.card {x : A → Prop // ZeroOneSol A x})
      Lax280166.KnapsacksValues.sharpZeroOneIP_count_iso A

/-- The library's #0-1 Integer Programming and the concept's have the same values. -/
theorem sharpZeroOneIP_agree (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] :
    DescriptiveComplexity.SharpZeroOneIP A = SharpZeroOneIP A :=
  (sharpZeroOneIP_eq A).symm

/--
---
conclusion: Lax280166.SteinerTreesValues.sharpSteinerTree_count_iso
---
The invariance the library proves when it bundles the problem.
-/
theorem sharpSteinerTree_count_iso {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A]
    [Lax799700.Steiner.steinerGraph.Structure B]
    (e : A ≃[Lax799700.Steiner.steinerGraph] B) : Nat.card {S : A → Prop // SteinerOfSize A S} =
        Nat.card {S : B → Prop // SteinerOfSize B S} :=
  (DescriptiveComplexity.SharpSteinerTree).iso_invariant e

/--
---
conclusion: Lax280166.SteinerTreesValues.sharpSteinerTree_eq
---
The number is invariant, by this submission's statement.
-/
theorem sharpSteinerTree_eq (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] :
    SharpSteinerTree A = Nat.card {S : A → Prop // SteinerOfSize A S} :=
  ofFun_eq (f := fun A _ => Nat.card {S : A → Prop // SteinerOfSize A S})
      Lax280166.SteinerTreesValues.sharpSteinerTree_count_iso A

/-- The library's #Steiner Tree and the concept's have the same values. -/
theorem sharpSteinerTree_agree (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] :
    DescriptiveComplexity.SharpSteinerTree A = SharpSteinerTree A :=
  (sharpSteinerTree_eq A).symm

/--
---
conclusion: Lax280166.ThreeSATComplete.sharpThreeSat_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpThreeSat_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpThreeSAT :=
  have hs : SharpP.ParsimoniousHard SharpSAT :=
    Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpThreeSat_agree A).mp DescriptiveComplexity.sharpThreeSat_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpThreeSat_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpSat_ordered_parsimonious_sharpThreeSat
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.ThreeSATComplete.sharpThreeSat_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpThreeSat_support_iff (A : Type) [Lax904597.Sat.sat.Structure A] [Finite A] :
    SharpThreeSAT.support A ↔ Lax799700.ThreeSat.ThreeSAT A :=
  ((support_congr sharpThreeSat_agree A).symm.trans
      (DescriptiveComplexity.sharpThreeSat_support_iff A)).trans
    (Lax799700.ThreeSat.threeSat_iff A).symm

/--
---
conclusion: Lax280166.OneInSATComplete.sharpOneInSat_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpOneInSat_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpOneInSAT :=
  have hs : SharpP.ParsimoniousHard SharpSAT :=
    Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpOneInSat_agree A).mp DescriptiveComplexity.sharpOneInSat_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpOneInSat_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpSat_ordered_parsimonious_sharpOneInSat
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.OneInSATComplete.sharpOneInSat_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpOneInSat_support_iff (A : Type) [Lax904597.Sat.sat.Structure A] [Finite A] :
    SharpOneInSAT.support A ↔ Lax799700.OneInSat.OneInSAT A :=
  ((support_congr sharpOneInSat_agree A).symm.trans
      (DescriptiveComplexity.sharpOneInSat_support_iff A)).trans
    (Lax799700.OneInSat.oneInSat_iff A).symm

/--
---
conclusion: Lax280166.CliqueComplete.sharpClique_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #1-in-SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpClique_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpClique :=
  have hs : SharpP.ParsimoniousHard SharpOneInSAT :=
    Lax280166.OneInSATComplete.sharpOneInSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpClique_agree A).mp DescriptiveComplexity.sharpClique_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ => sharpClique_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpOneInSat_ordered_parsimonious_sharpClique
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpOneInSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.CliqueComplete.sharpClique_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpClique_support_iff
    (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpClique.support A ↔ Lax799700.CliqueFamily.Clique A :=
  ((support_congr sharpClique_agree A).symm.trans
      (DescriptiveComplexity.sharpClique_support_iff A)).trans
    (Lax799700.CliqueFamily.clique_iff A).symm

/--
---
conclusion: Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Clique, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpIndependentSet_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpIndependentSet :=
  have hs : SharpP.ParsimoniousHard SharpClique :=
    Lax280166.CliqueComplete.sharpClique_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpIndependentSet_agree A).mp DescriptiveComplexity.sharpIndependentSet_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpIndependentSet_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpClique_parsimonious_sharpIndependentSet
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpClique_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.IndependentSetComplete.sharpIndependentSet_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpIndependentSet_support_iff
    (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpIndependentSet.support A ↔ Lax799700.CliqueFamily.IndependentSet A :=
  ((support_congr sharpIndependentSet_agree A).symm.trans
      (DescriptiveComplexity.sharpIndependentSet_support_iff A)).trans
    (Lax799700.CliqueFamily.indSet_iff A).symm

/--
---
conclusion: Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Independent Set, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpVertexCover_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpVertexCover :=
  have hs : SharpP.ParsimoniousHard SharpIndependentSet :=
    Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpVertexCover_agree A).mp DescriptiveComplexity.sharpVertexCover_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpVertexCover_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpIndependentSet_parsimonious_sharpVertexCover
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpIndependentSet_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.VertexCoverComplete.sharpVertexCover_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpVertexCover_support_iff
    (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpVertexCover.support A ↔ Lax799700.CliqueFamily.VertexCover A :=
  ((support_congr sharpVertexCover_agree A).symm.trans
      (DescriptiveComplexity.sharpVertexCover_support_iff A)).trans
    (Lax799700.CliqueFamily.vertexCover_iff A).symm

/--
---
conclusion: Lax280166.DominatingSetComplete.sharpDominatingSet_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpDominatingSet_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpDominatingSet :=
  have hs : SharpP.ParsimoniousHard SharpSAT :=
    Lax366625.SharpSatComplete.sharpSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpDominatingSet_agree A).mp DescriptiveComplexity.sharpDominatingSet_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpDominatingSet_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpSat_parsimonious_sharpDominatingSet
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.DominatingSetComplete.sharpDominatingSet_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpDominatingSet_support_iff
    (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpDominatingSet.support A ↔ Lax799700.DominatingSet.DominatingSet A :=
  ((support_congr sharpDominatingSet_agree A).symm.trans
      (DescriptiveComplexity.sharpDominatingSet_support_iff A)).trans
    (Lax799700.DominatingSet.dominatingSet_iff A).symm

/--
---
conclusion: Lax280166.FeedbackVertexSetComplete.sharpFeedbackVertexSet_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Vertex Cover, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpFeedbackVertexSet_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpFeedbackVertexSet :=
  have hs : SharpP.ParsimoniousHard SharpVertexCover :=
    Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpFeedbackVertexSet_agree A).mp DescriptiveComplexity.sharpFeedbackVertexSet_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpFeedbackVertexSet_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpVertexCover_parsimonious_sharpFeedbackVertexSet
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpVertexCover_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.FeedbackVertexSetComplete.sharpFeedbackVertexSet_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpFeedbackVertexSet_support_iff
    (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A] :
    SharpFeedbackVertexSet.support A ↔ Lax799700.Feedback.FeedbackVertexSet A :=
  ((support_congr sharpFeedbackVertexSet_agree A).symm.trans
      (DescriptiveComplexity.sharpFeedbackVertexSet_support_iff A)).trans
    (Lax799700.Feedback.feedbackVertexSet_iff A).symm

/--
---
conclusion: Lax280166.FeedbackArcSetComplete.sharpFeedbackArcSet_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #1-in-SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpFeedbackArcSet_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpFeedbackArcSet :=
  have hs : SharpP.ParsimoniousHard SharpOneInSAT :=
    Lax280166.OneInSATComplete.sharpOneInSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpFeedbackArcSet_agree A).mp DescriptiveComplexity.sharpFeedbackArcSet_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpFeedbackArcSet_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpOneInSat_ordered_parsimonious_sharpFeedbackArcSet
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpOneInSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.FeedbackArcSetComplete.sharpFeedbackArcSet_support_iff
---
The library's lemma, with the supports matched.
-/
theorem sharpFeedbackArcSet_support_iff
    (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] [Finite A] :
    SharpFeedbackArcSet.support A ↔ ∃ F : A → A → Prop, FasOfSize A F :=
  (support_congr sharpFeedbackArcSet_agree A).symm.trans
      (DescriptiveComplexity.sharpFeedbackArcSet_support_iff A)

/--
---
conclusion: Lax280166.FeedbackArcSetComplete.feedbackArcSet_of_sharpFeedbackArcSet_support
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem feedbackArcSet_of_sharpFeedbackArcSet_support
    (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] [Finite A]
    (h : SharpFeedbackArcSet.support A) : Lax799700.Feedback.FeedbackArcSet A :=
  (Lax799700.Feedback.feedbackArcSet_iff A).mpr
      (DescriptiveComplexity.feedbackArcSet_of_sharpFeedbackArcSet_support A
          ((support_congr sharpFeedbackArcSet_agree A).mpr h))

/--
---
conclusion: Lax280166.DirHamCircuitComplete.sharpDirHamCircuit_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #1-in-SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpDirHamCircuit_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpDirHamCircuit :=
  have hs : SharpP.ParsimoniousHard SharpOneInSAT :=
    Lax280166.OneInSATComplete.sharpOneInSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpDirHamCircuit_agree A).mp DescriptiveComplexity.sharpDirHamCircuit_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpDirHamCircuit_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_relOrderedParsimonious
          DescriptiveComplexity.sharpOneInSat_rel_ordered_parsimonious_sharpDirHamCircuit
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpOneInSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.DirHamCircuitComplete.sharpDirHamCircuit_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpDirHamCircuit_support_iff
    (A : Type) [Lax799700.Hamilton.digraph.Structure A] [Finite A] :
    SharpDirHamCircuit.support A ↔ Lax799700.Hamilton.DirHamCircuit A :=
  ((support_congr sharpDirHamCircuit_agree A).symm.trans
      (DescriptiveComplexity.sharpDirHamCircuit_support_iff A)).trans
    (Lax799700.Hamilton.dirHamCircuit_iff A).symm

/--
---
conclusion: Lax280166.HamCircuitComplete.sharpHamCircuit_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Directed Hamilton Circuit, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpHamCircuit_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpHamCircuit :=
  have hs : SharpP.ParsimoniousHard SharpDirHamCircuit :=
    Lax280166.DirHamCircuitComplete.sharpDirHamCircuit_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpHamCircuit_agree A).mp DescriptiveComplexity.sharpHamCircuit_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpHamCircuit_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpDirHamCircuit_parsimonious_sharpHamCircuit
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpDirHamCircuit_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.HamCircuitComplete.sharpHamCircuit_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpHamCircuit_support_iff (A : Type) [Lax799700.Hamilton.digraph.Structure A] [Finite A] :
    SharpHamCircuit.support A ↔ Lax799700.Hamilton.HamCircuit A :=
  ((support_congr sharpHamCircuit_agree A).symm.trans
      (DescriptiveComplexity.sharpHamCircuit_support_iff A)).trans
    (Lax799700.Hamilton.hamCircuit_iff A).symm

/--
---
conclusion: Lax280166.ExactCoverComplete.sharpExactCover_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #1-in-SAT, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpExactCover_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpExactCover :=
  have hs : SharpP.ParsimoniousHard SharpOneInSAT :=
    Lax280166.OneInSATComplete.sharpOneInSat_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpExactCover_agree A).mp DescriptiveComplexity.sharpExactCover_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpExactCover_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpOneInSat_parsimonious_sharpExactCover
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpOneInSat_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.ExactCoverComplete.sharpExactCover_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpExactCover_support_iff
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpExactCover.support A ↔ Lax799700.SetFamily.ExactCover A :=
  ((support_congr sharpExactCover_agree A).symm.trans
      (DescriptiveComplexity.sharpExactCover_support_iff A)).trans
    (Lax799700.SetFamily.exactCover_iff A).symm

/--
---
conclusion: Lax280166.SetPackingComplete.sharpSetPacking_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Independent Set, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpSetPacking_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpSetPacking :=
  have hs : SharpP.ParsimoniousHard SharpIndependentSet :=
    Lax280166.IndependentSetComplete.sharpIndependentSet_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpSetPacking_agree A).mp DescriptiveComplexity.sharpSetPacking_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpSetPacking_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpIndependentSet_parsimonious_sharpSetPacking
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpIndependentSet_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.SetPackingComplete.sharpSetPacking_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpSetPacking_support_iff
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpSetPacking.support A ↔ Lax799700.SetFamily.SetPacking A :=
  ((support_congr sharpSetPacking_agree A).symm.trans
      (DescriptiveComplexity.sharpSetPacking_support_iff A)).trans
    (Lax799700.SetFamily.setPacking_iff A).symm

/--
---
conclusion: Lax280166.SetCoverComplete.sharpSetCover_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Vertex Cover, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpSetCover_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpSetCover :=
  have hs : SharpP.ParsimoniousHard SharpVertexCover :=
    Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpSetCover_agree A).mp DescriptiveComplexity.sharpSetCover_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpSetCover_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpVertexCover_parsimonious_sharpSetCover
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpVertexCover_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.SetCoverComplete.sharpSetCover_support_iff
---
The library's lemma, with the supports matched.
-/
theorem sharpSetCover_support_iff
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpSetCover.support A ↔ ∃ G : A → Prop, SetCoverOfSize A G :=
  (support_congr sharpSetCover_agree A).symm.trans
      (DescriptiveComplexity.sharpSetCover_support_iff A)

/--
---
conclusion: Lax280166.SetCoverComplete.setCover_of_sharpSetCover_support
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem setCover_of_sharpSetCover_support
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A]
    (h : SharpSetCover.support A) : Lax799700.SetFamily.SetCover A :=
  (Lax799700.SetFamily.setCover_iff A).mpr
      (DescriptiveComplexity.setCover_of_sharpSetCover_support A
          ((support_congr sharpSetCover_agree A).mpr h))

/--
---
conclusion: Lax280166.HittingSetComplete.sharpHittingSet_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Set Cover, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpHittingSet_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpHittingSet :=
  have hs : SharpP.ParsimoniousHard SharpSetCover :=
    Lax280166.SetCoverComplete.sharpSetCover_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpHittingSet_agree A).mp DescriptiveComplexity.sharpHittingSet_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpHittingSet_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_parsimonious
          DescriptiveComplexity.sharpSetCover_parsimonious_sharpHittingSet
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpSetCover_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.HittingSetComplete.sharpHittingSet_support_iff
---
The library's lemma, with the supports matched.
-/
theorem sharpHittingSet_support_iff
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A] :
    SharpHittingSet.support A ↔ ∃ H : A → Prop, HittingSetOfSize A H :=
  (support_congr sharpHittingSet_agree A).symm.trans
      (DescriptiveComplexity.sharpHittingSet_support_iff A)

/--
---
conclusion: Lax280166.HittingSetComplete.hittingSet_of_sharpHittingSet_support
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem hittingSet_of_sharpHittingSet_support
    (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A]
    (h : SharpHittingSet.support A) : Lax799700.SetFamily.HittingSet A :=
  (Lax799700.SetFamily.hittingSet_iff A).mpr
      (DescriptiveComplexity.hittingSet_of_sharpHittingSet_support A
          ((support_congr sharpHittingSet_agree A).mpr h))

/--
---
conclusion: Lax280166.KnapsackComplete.sharpKnapsack_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Exact Cover, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpKnapsack_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpKnapsack :=
  have hs : SharpP.ParsimoniousHard SharpExactCover :=
    Lax280166.ExactCoverComplete.sharpExactCover_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpKnapsack_agree A).mp DescriptiveComplexity.sharpKnapsack_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpKnapsack_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpExactCover_ordered_parsimonious_sharpKnapsack
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpExactCover_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.KnapsackComplete.sharpKnapsack_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpKnapsack_support_iff
    (A : Type) [Lax799700.Knapsack.binWeights.Structure A] [Finite A] :
    SharpKnapsack.support A ↔ Lax799700.Knapsack.Knapsack A :=
  ((support_congr sharpKnapsack_agree A).symm.trans
      (DescriptiveComplexity.sharpKnapsack_support_iff A)).trans
    (Lax799700.Knapsack.knapsack_iff A).symm

/--
---
conclusion: Lax280166.ZeroOneIPComplete.sharpZeroOneIP_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Knapsack, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpZeroOneIP_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpZeroOneIP :=
  have hs : SharpP.ParsimoniousHard SharpKnapsack :=
    Lax280166.KnapsackComplete.sharpKnapsack_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpZeroOneIP_agree A).mp DescriptiveComplexity.sharpZeroOneIP_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpZeroOneIP_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpKnapsack_ordered_parsimonious_sharpZeroOneIP
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpKnapsack_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.ZeroOneIPComplete.sharpZeroOneIP_support_iff
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem sharpZeroOneIP_support_iff
    (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] [Finite A] :
    SharpZeroOneIP.support A ↔ Lax799700.ZeroOneIP.ZeroOneIP A :=
  ((support_congr sharpZeroOneIP_agree A).symm.trans
      (DescriptiveComplexity.sharpZeroOneIP_support_iff A)).trans
    (Lax799700.ZeroOneIP.zeroOneIP_iff A).symm

/--
---
conclusion: Lax280166.SteinerTreeComplete.sharpSteinerTree_sharpP_parsimoniousComplete
---
Membership is the library's; hardness is carried from #Vertex Cover, by this
submission's statement or the one it requires, along the library's reduction.
-/
theorem sharpSteinerTree_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete
    SharpSteinerTree :=
  have hs : SharpP.ParsimoniousHard SharpVertexCover :=
    Lax280166.VertexCoverComplete.sharpVertexCover_sharpP_parsimoniousComplete.2
  ⟨(DescriptiveComplexity.SharpP.mem_congr_finite fun A _ _ =>
      sharpSteinerTree_agree A).mp DescriptiveComplexity.sharpSteinerTree_mem_sharpP,
    (DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
        sharpSteinerTree_agree A).mp
      (DescriptiveComplexity.SharpP.parsimoniousHard_of_orderedParsimonious
          DescriptiveComplexity.sharpVertexCover_ordered_parsimonious_sharpSteinerTree
        ((DescriptiveComplexity.SharpP.parsimoniousHard_congr_finite fun A _ _ =>
            sharpVertexCover_agree A).mpr hs))⟩

/--
---
conclusion: Lax280166.SteinerTreeComplete.sharpSteinerTree_support_iff
---
The library's lemma, with the supports matched.
-/
theorem sharpSteinerTree_support_iff
    (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] [Finite A] :
    SharpSteinerTree.support A ↔ ∃ S : A → Prop, SteinerOfSize A S :=
  (support_congr sharpSteinerTree_agree A).symm.trans
      (DescriptiveComplexity.sharpSteinerTree_support_iff A)

/--
---
conclusion: Lax280166.SteinerTreeComplete.steinerTree_of_sharpSteinerTree_support
---
The library's lemma, with the supports and the decision problems matched.
-/
theorem steinerTree_of_sharpSteinerTree_support
    (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] [Finite A]
    (h : SharpSteinerTree.support A) : Lax799700.Steiner.SteinerTree A :=
  (Lax799700.Steiner.steinerTree_iff A).mpr
      (DescriptiveComplexity.steinerTree_of_sharpSteinerTree_support A
          ((support_congr sharpSteinerTree_agree A).mpr h))

end Lax280166Proofs.Bridge
