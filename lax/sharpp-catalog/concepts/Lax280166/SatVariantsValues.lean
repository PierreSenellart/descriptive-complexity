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
title: The values of #3SAT, #1-in-SAT
type: lemma
---
The number counted by each of #3SAT, #1-in-SAT is invariant under isomorphism of
instances, so the value of each problem on an instance is the number it
counts.
-/

namespace Lax280166.SatVariantsValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #3SAT is isomorphism-invariant. -/
axiom sharpThreeSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop // WidthAtMostThree A ∧ SatModel A ν} =
        Nat.card {ν : B → Prop // WidthAtMostThree B ∧ SatModel B ν}

/-- The value of #3SAT is the number it counts. -/
axiom sharpThreeSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpThreeSAT A = Nat.card {ν : A → Prop //
      WidthAtMostThree A ∧ SatModel A ν}

/-- The number counted by #1-in-SAT is isomorphism-invariant. -/
axiom sharpOneInSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop // OneInModel A ν} = Nat.card {ν : B → Prop
        // OneInModel B ν}

/-- The value of #1-in-SAT is the number it counts. -/
axiom sharpOneInSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpOneInSAT A = Nat.card {ν : A → Prop //
      OneInModel A ν}

end Lax280166.SatVariantsValues
