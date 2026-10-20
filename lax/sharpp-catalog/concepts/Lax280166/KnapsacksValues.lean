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
title: The values of #Knapsack, #0-1 Integer Programming
type: lemma
---
The number counted by each of #Knapsack, #0-1 Integer Programming is invariant under isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.KnapsacksValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Knapsack is isomorphism-invariant. -/
axiom sharpKnapsack_count_iso :
  ∀ {A B : Type} [Lax799700.Knapsack.binWeights.Structure A]
      [Lax799700.Knapsack.binWeights.Structure B],
    (A ≃[Lax799700.Knapsack.binWeights] B) → Nat.card {S : A → Prop // KnapsackSol A S} = Nat.card
        {S : B → Prop // KnapsackSol B S}

/-- The value of #Knapsack is the number it counts. -/
axiom sharpKnapsack_eq :
  ∀ (A : Type) [Lax799700.Knapsack.binWeights.Structure A], SharpKnapsack A = Nat.card {S : A →
      Prop // KnapsackSol A S}

/-- The number counted by #0-1 Integer Programming is isomorphism-invariant. -/
axiom sharpZeroOneIP_count_iso :
  ∀ {A B : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A]
      [Lax799700.ZeroOneIP.zeroOneIP.Structure B],
    (A ≃[Lax799700.ZeroOneIP.zeroOneIP] B) → Nat.card {x : A → Prop // ZeroOneSol A x} = Nat.card
        {x : B → Prop // ZeroOneSol B x}

/-- The value of #0-1 Integer Programming is the number it counts. -/
axiom sharpZeroOneIP_eq :
  ∀ (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A], SharpZeroOneIP A = Nat.card {x : A →
      Prop // ZeroOneSol A x}

end Lax280166.KnapsacksValues
