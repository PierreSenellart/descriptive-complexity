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
title: Invariance and characterization of the circuit value problem
type: lemma
---
Acceptance of a circuit is invariant under isomorphism of circuits, and a
circuit is a yes-instance of CVP exactly when some output gate derives the
value true.
-/

namespace Lax535992.CircuitValueInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Acceptance of a circuit is isomorphism-invariant. -/
axiom circuitAccepts_iso : ∀ {A B : Type} [circuit.Structure A] [circuit.Structure B],
  (A ≃[circuit] B) → (CircuitAccepts A ↔ CircuitAccepts B)

/-- The yes-instances of CVP are exactly the instances with the defining
property. -/
axiom cvp_iff : ∀ (A : Type) [circuit.Structure A], CVP A ↔ CircuitAccepts A

end Lax535992.CircuitValueInvariance
