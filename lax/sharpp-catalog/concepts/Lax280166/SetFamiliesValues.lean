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
title: The values of #Exact Cover, #Set Packing, #Set Cover, #Hitting Set
type: lemma
---
The number counted by each of #Exact Cover, #Set Packing, #Set Cover, #Hitting Set is invariant
    under isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.SetFamiliesValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Exact Cover is isomorphism-invariant. -/
axiom sharpExactCover_count_iso :
  ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
      [Lax799700.SetFamily.setSystem.Structure B],
    (A ≃[Lax799700.SetFamily.setSystem] B) → Nat.card {G : A → Prop // ExactCoverBy (SSElem
        (A := A)) SSFam SSMem G} = Nat.card {G : B → Prop // ExactCoverBy (SSElem
            (A := B)) SSFam SSMem G}

/-- The value of #Exact Cover is the number it counts. -/
axiom sharpExactCover_eq :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SharpExactCover A = Nat.card {G : A →
      Prop // ExactCoverBy (SSElem (A := A)) SSFam SSMem G}

/-- The number counted by #Set Packing is isomorphism-invariant. -/
axiom sharpSetPacking_count_iso :
  ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
      [Lax799700.SetFamily.setSystem.Structure B],
    (A ≃[Lax799700.SetFamily.setSystem] B) → Nat.card {G : A → Prop // PackingOfSize A G} =
        Nat.card {G : B → Prop // PackingOfSize B G}

/-- The value of #Set Packing is the number it counts. -/
axiom sharpSetPacking_eq :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SharpSetPacking A = Nat.card {G : A →
      Prop // PackingOfSize A G}

/-- The number counted by #Set Cover is isomorphism-invariant. -/
axiom sharpSetCover_count_iso :
  ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
      [Lax799700.SetFamily.setSystem.Structure B],
    (A ≃[Lax799700.SetFamily.setSystem] B) → Nat.card {G : A → Prop // SetCoverOfSize A G} =
        Nat.card {G : B → Prop // SetCoverOfSize B G}

/-- The value of #Set Cover is the number it counts. -/
axiom sharpSetCover_eq :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SharpSetCover A = Nat.card {G : A →
      Prop // SetCoverOfSize A G}

/-- The number counted by #Hitting Set is isomorphism-invariant. -/
axiom sharpHittingSet_count_iso :
  ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
      [Lax799700.SetFamily.setSystem.Structure B],
    (A ≃[Lax799700.SetFamily.setSystem] B) → Nat.card {H : A → Prop // HittingSetOfSize A H} =
        Nat.card {H : B → Prop // HittingSetOfSize B H}

/-- The value of #Hitting Set is the number it counts. -/
axiom sharpHittingSet_eq :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SharpHittingSet A = Nat.card {H : A →
      Prop // HittingSetOfSize A H}

end Lax280166.SetFamiliesValues
