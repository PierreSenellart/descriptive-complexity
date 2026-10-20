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
title: The values of #2SAT, #HORN-SAT, and #Monotone-2SAT
type: lemma
---
The number counted by each of #2SAT, #HORN-SAT, and #Monotone-2SAT is
invariant under isomorphism of instances, so the value of each problem on an
instance is the number it counts.
-/

namespace Lax859101.RestrictedSatValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #2SAT is isomorphism-invariant. -/
axiom sharpTwoSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card
        {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν} = Nat.card
            {ν : B → Prop // WidthAtMostTwo B ∧ SatModel B ν}

/-- The value of #2SAT is the number it counts. -/
axiom sharpTwoSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpTwoSAT A = Nat.card
      {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν}

/-- The number counted by #HORN-SAT is isomorphism-invariant. -/
axiom sharpHornSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card
        {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν} = Nat.card
            {ν : B → Prop // AtMostOnePositive B ∧ SatModel B ν}

/-- The value of #HORN-SAT is the number it counts. -/
axiom sharpHornSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpHornSAT A = Nat.card
      {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν}

/-- The number counted by #Monotone-2SAT is isomorphism-invariant. -/
axiom sharpMonotoneTwoSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop //
        (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν} = Nat.card {ν : B → Prop //
            (WidthAtMostTwo B ∧ NoNegative B) ∧ SatModel B ν}

/-- The value of #Monotone-2SAT is the number it counts. -/
axiom sharpMonotoneTwoSat_eq :
  ∀ (A : Type) [Lax904597.Sat.sat.Structure A], SharpMonotoneTwoSAT A = Nat.card {ν : A → Prop //
      (WidthAtMostTwo A ∧ NoNegative A) ∧ SatModel A ν}

end Lax859101.RestrictedSatValues
