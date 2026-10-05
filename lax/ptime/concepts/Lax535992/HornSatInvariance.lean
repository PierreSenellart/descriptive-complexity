import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.HornFragment
import Lax535992.LeastFixedPoint
import Lax535992.InflationaryFixedPoint
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.Game
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME

/-!
---
title: Invariance and characterization of HORN-SAT
type: lemma
---
Being a satisfiable Horn instance is invariant under isomorphism of CNF
instances, and an instance is a yes-instance of HORN-SAT exactly when it is
Horn and satisfiable.
-/

namespace Lax535992.HornSatInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Being Horn and satisfiable is isomorphism-invariant. -/
axiom hornSatisfiable_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (HornSatisfiable A ↔ HornSatisfiable B)

/-- The yes-instances of HORN-SAT are exactly the instances with the defining
property. -/
axiom hornSat_iff : ∀ (A : Type) [sat.Structure A], HORNSAT A ↔ HornSatisfiable A

end Lax535992.HornSatInvariance
