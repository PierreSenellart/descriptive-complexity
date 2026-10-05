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
title: Invariance and characterization of deterministic machine acceptance
type: lemma
---
Being a well-formed, deterministic and accepting machine instance is
invariant under isomorphism of instances, and an instance is a yes-instance
of deterministic machine acceptance exactly when it is well-formed,
deterministic and accepting.
-/

namespace Lax535992.DeterministicMachineInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Being well-formed, deterministic and accepting is isomorphism-invariant. -/
axiom dtmAccepts_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) →
    (((tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts) ↔
      ((tmData B).WellFormed ∧ TMData.Deterministic (tmData B) ∧ (tmData B).Accepts))

/-- The yes-instances of deterministic machine acceptance are exactly the
well-formed, deterministic and accepting instances. -/
axiom dtmAccept_iff : ∀ (A : Type) [turing.Structure A],
  DTMAccept A ↔
    ((tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ (tmData A).Accepts)

end Lax535992.DeterministicMachineInvariance
