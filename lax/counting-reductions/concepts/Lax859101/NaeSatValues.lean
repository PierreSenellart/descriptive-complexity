import Lax904597.Problems
import Lax904597.Sat
import Mathlib.ModelTheory.Graph
import Lax799700.SetFamily
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite

/-!
---
title: The values of #NAE-SAT and #Set Splitting
type: lemma
---
The number counted by each of #NAE-SAT and #Set Splitting is invariant under
isomorphism of instances, so the value of each problem on an instance is the
number it counts.
-/

namespace Lax859101.NaeSatValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #NAE-SAT is isomorphism-invariant. -/
axiom sharpNaeSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop // NAEModel A ν} = Nat.card
        {ν : B → Prop // NAEModel B ν}

/-- The value of #NAE-SAT is the number it counts. -/
axiom sharpNaeSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpNAESAT A = Nat.card
      {ν : A → Prop // NAEModel A ν}

/-- The number counted by #Set Splitting is isomorphism-invariant. -/
axiom sharpSetSplitting_count_iso :
  ∀ {A B : Type} [Lax799700.SetFamily.setSystem.Structure A]
      [Lax799700.SetFamily.setSystem.Structure B],
    (A ≃[Lax799700.SetFamily.setSystem] B) → Nat.card
        {S : A → Prop // SplitColoring A S} = Nat.card {S : B → Prop // SplitColoring B S}

/-- The value of #Set Splitting is the number it counts. -/
axiom sharpSetSplitting_eq :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A], SharpSetSplitting A = Nat.card
      {S : A → Prop // SplitColoring A S}

end Lax859101.NaeSatValues
