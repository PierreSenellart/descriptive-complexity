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
title: HORN-SAT is PTIME-complete
type: theorem
---
HORN-SAT is PTIME-complete under first-order reductions. It is SO-Horn
definable, by a Horn program that computes unit propagation and assembles
the unbounded body of an input clause along the order; and every SO-Horn
definable problem reduces to it by an ordered first-order reduction that
emits one propositional Horn clause per clause of the program and per
valuation of its first-order variables. This is the polynomial-time
counterpart of the Cook–Levin theorem.
-/

namespace Lax535992.HornSatPTIMEComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- HORN-SAT is PTIME-complete. -/
axiom hornSat_PTIME_complete : PTIME.Complete HORNSAT

end Lax535992.HornSatPTIMEComplete
