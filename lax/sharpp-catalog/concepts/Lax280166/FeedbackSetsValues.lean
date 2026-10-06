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
title: The values of #Feedback Vertex Set, #Feedback Arc Set
type: lemma
---
The number counted by each of #Feedback Vertex Set, #Feedback Arc Set is invariant under
    isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.FeedbackSetsValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Feedback Vertex Set is isomorphism-invariant. -/
axiom sharpFeedbackVertexSet_count_iso :
  ∀ {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
      [Lax799700.CliqueFamily.markedGraph.Structure B],
    (A ≃[Lax799700.CliqueFamily.markedGraph] B) → Nat.card {C : A → Prop // FvsOfSize A C} =
        Nat.card {C : B → Prop // FvsOfSize B C}

/-- The value of #Feedback Vertex Set is the number it counts. -/
axiom sharpFeedbackVertexSet_eq :
  ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A], SharpFeedbackVertexSet A =
      Nat.card {C : A → Prop // FvsOfSize A C}

/-- The number counted by #Feedback Arc Set is isomorphism-invariant. -/
axiom sharpFeedbackArcSet_count_iso :
  ∀ {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A]
      [Lax799700.Feedback.markedArcGraph.Structure B],
    (A ≃[Lax799700.Feedback.markedArcGraph] B) → Nat.card {F : A → A → Prop // FasOfSize A F} =
        Nat.card {F : B → B → Prop // FasOfSize B F}

/-- The value of #Feedback Arc Set is the number it counts. -/
axiom sharpFeedbackArcSet_eq :
  ∀ (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A], SharpFeedbackArcSet A = Nat.card {F
      : A → A → Prop // FasOfSize A F}

end Lax280166.FeedbackSetsValues
