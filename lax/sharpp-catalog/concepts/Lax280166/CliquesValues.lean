import Lax904597.Problems
import Lax904597.Sat
import Lax799700.CliqueFamily
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.Knapsack
import Lax799700.OneInSat
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax280166.CountingSatVariants
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingSetFamilies
import Lax280166.CountingKnapsacks
import Lax280166.CountingSteinerTrees

/-!
---
title: The values of #Clique, #Independent Set, #Vertex Cover
type: lemma
---
The number counted by each of #Clique, #Independent Set, #Vertex Cover is invariant under
    isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.CliquesValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Clique is isomorphism-invariant. -/
axiom sharpClique_count_iso :
  ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
      [Lax799700.CliqueFamily.markedGraph.Structure B],
    (A ≃[Lax799700.CliqueFamily.markedGraph] B) → Nat.card {S : A → Prop // CliqueOfSize A S} =
        Nat.card {S : B → Prop // CliqueOfSize B S}

/-- The value of #Clique is the number it counts. -/
axiom sharpClique_eq :
  ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], SharpClique A = Nat.card {S : A →
      Prop // CliqueOfSize A S}

/-- The number counted by #Independent Set is isomorphism-invariant. -/
axiom sharpIndependentSet_count_iso :
  ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
      [Lax799700.CliqueFamily.markedGraph.Structure B],
    (A ≃[Lax799700.CliqueFamily.markedGraph] B) → Nat.card {S : A → Prop // IndepOfSize A S} =
        Nat.card {S : B → Prop // IndepOfSize B S}

/-- The value of #Independent Set is the number it counts. -/
axiom sharpIndependentSet_eq :
  ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], SharpIndependentSet A = Nat.card
      {S : A → Prop // IndepOfSize A S}

/-- The number counted by #Vertex Cover is isomorphism-invariant. -/
axiom sharpVertexCover_count_iso :
  ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
      [Lax799700.CliqueFamily.markedGraph.Structure B],
    (A ≃[Lax799700.CliqueFamily.markedGraph] B) → Nat.card {C : A → Prop // CoverOfSize A C} =
        Nat.card {C : B → Prop // CoverOfSize B C}

/-- The value of #Vertex Cover is the number it counts. -/
axiom sharpVertexCover_eq :
  ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], SharpVertexCover A = Nat.card {C :
      A → Prop // CoverOfSize A C}

end Lax280166.CliquesValues
