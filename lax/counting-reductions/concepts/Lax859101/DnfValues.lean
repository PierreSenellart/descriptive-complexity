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
title: The values of #DNF
type: lemma
---
The number counted by #DNF is invariant under isomorphism of instances, so
the value of the problem on an instance is the number it counts.
-/

namespace Lax859101.DnfValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #DNF is isomorphism-invariant. -/
axiom sharpDnf_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop // DnfModel A ν} = Nat.card
        {ν : B → Prop // DnfModel B ν}

/-- The value of #DNF is the number it counts. -/
axiom sharpDnf_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpDNF A = Nat.card {ν : A → Prop // DnfModel A ν}

end Lax859101.DnfValues
