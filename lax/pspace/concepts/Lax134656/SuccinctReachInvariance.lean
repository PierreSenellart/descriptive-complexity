import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.InflationaryFixedPoint
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SuccinctReach
import Lax134656.SpaceBoundedMachines
import Lax134656.ClassPSPACE

/-!
---
title: Invariance and characterization of SUCCINCT-REACH
type: lemma
---
Reachability of a target state from a source state in a succinctly
described transition system is invariant under isomorphism of instances,
and an instance is a yes-instance of SUCCINCT-REACH exactly when some target
state is reachable from some source state.
-/

namespace Lax134656.SuccinctReachInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Succinct reachability is isomorphism-invariant. -/
axiom succinctReachable_iso : ∀ {A B : Type} [transSys.Structure A] [transSys.Structure B],
  (A ≃[transSys] B) → (SuccinctReachable A ↔ SuccinctReachable B)

/-- The yes-instances are exactly the instances with the defining property. -/
axiom succinctReach_iff : ∀ (A : Type) [transSys.Structure A], SUCCINCTREACH A ↔ SuccinctReachable A

end Lax134656.SuccinctReachInvariance
