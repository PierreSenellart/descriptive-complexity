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
title: The values of #Directed Hamilton Circuit, #Hamilton Circuit
type: lemma
---
The number counted by each of #Directed Hamilton Circuit, #Hamilton Circuit is invariant under
    isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.HamiltonCircuitsValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Directed Hamilton Circuit is isomorphism-invariant. -/
axiom sharpDirHamCircuit_count_iso :
  ∀ {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B],
    (A ≃[Lax799700.Hamilton.digraph] B) → Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt} =
        Nat.card {Nxt : B → B → Prop // DirCircuit B Nxt}

/-- The value of #Directed Hamilton Circuit is the number it counts. -/
axiom sharpDirHamCircuit_eq :
  ∀ (A : Type) [Lax799700.Hamilton.digraph.Structure A], SharpDirHamCircuit A = Nat.card {Nxt : A →
      A → Prop // DirCircuit A Nxt}

/-- The number counted by #Hamilton Circuit is isomorphism-invariant. -/
axiom sharpHamCircuit_count_iso :
  ∀ {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B],
    (A ≃[Lax799700.Hamilton.digraph] B) → Nat.card {E : A → A → Prop // UCircuit A E} = Nat.card {E
        : B → B → Prop // UCircuit B E}

/-- The value of #Hamilton Circuit is the number it counts. -/
axiom sharpHamCircuit_eq :
  ∀ (A : Type) [Lax799700.Hamilton.digraph.Structure A], SharpHamCircuit A = Nat.card {E : A → A →
      Prop // UCircuit A E}

end Lax280166.HamiltonCircuitsValues
