import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: Invariance and characterization of 3-DNF-TAUT and 3-UNSAT
type: lemma
---
Being a DNF tautology of width at most three, and being an unsatisfiable
CNF formula of width at most three, are invariant under isomorphism of
instances; an instance is a yes-instance of 3-DNF-TAUT, respectively of
3-UNSAT, exactly when it has the corresponding property.
-/

namespace Lax564036.ThreeDnfTautologyInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Being a tautology of width at most three is isomorphism-invariant. -/
axiom threeDnfTautology_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (ThreeDnfTautology A ↔ ThreeDnfTautology B)

/-- Being unsatisfiable of width at most three is isomorphism-invariant. -/
axiom threeUnsatisfiable_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (ThreeUnsatisfiable A ↔ ThreeUnsatisfiable B)

/-- The yes-instances of 3-DNF-TAUT are exactly the tautologies of width at
most three. -/
axiom threeDnfTaut_iff : ∀ (A : Type) [sat.Structure A],
  ThreeDnfTAUT A ↔ ThreeDnfTautology A

/-- The yes-instances of 3-UNSAT are exactly the unsatisfiable instances of
width at most three. -/
axiom threeUnsat_iff : ∀ (A : Type) [sat.Structure A],
  ThreeUNSAT A ↔ ThreeUnsatisfiable A

end Lax564036.ThreeDnfTautologyInvariance
