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
title: The values of #BIS and #PP2DNF
type: lemma
---
The number counted by each of #BIS and #PP2DNF is invariant under
isomorphism of instances, so the value of each problem on an instance is the
number it counts.
-/

namespace Lax859101.BipartiteValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #BIS is isomorphism-invariant. -/
axiom sharpBIS_count_iso :
  ∀ {A B : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]
      [Lax859101.CountingBipartite.bipGraph.Structure B],
    (A ≃[Lax859101.CountingBipartite.bipGraph] B) → Nat.card
        {S : A → Prop // BipIndep A S} = Nat.card {S : B → Prop // BipIndep B S}

/-- The value of #BIS is the number it counts. -/
axiom sharpBIS_eq :
  ∀ (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A], SharpBIS A = Nat.card
      {S : A → Prop // BipIndep A S}

/-- The number counted by #PP2DNF is isomorphism-invariant. -/
axiom sharpPP2DNF_count_iso :
  ∀ {A B : Type} [Lax859101.CountingBipartite.bipGraph.Structure A]
      [Lax859101.CountingBipartite.bipGraph.Structure B],
    (A ≃[Lax859101.CountingBipartite.bipGraph] B) → Nat.card
        {S : A → Prop // Pp2dnfModel A S} = Nat.card {S : B → Prop // Pp2dnfModel B S}

/-- The value of #PP2DNF is the number it counts. -/
axiom sharpPP2DNF_eq :
  ∀ (A : Type) [Lax859101.CountingBipartite.bipGraph.Structure A], SharpPP2DNF A = Nat.card
      {S : A → Prop // Pp2dnfModel A S}

end Lax859101.BipartiteValues
