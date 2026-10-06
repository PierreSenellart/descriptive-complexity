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
title: SUCCINCT-REACH is PSPACE-complete
type: theorem
---
SUCCINCT-REACH is PSPACE-complete under first-order reductions. It is
SO(TC) definable, a state of the system being an assignment of a unary
relation variable; and every SO(TC) definable problem reduces to it, the
three sentences of a specification becoming the three groups of clauses of
a transition system, as the first-order kernel of a definition becomes a
CNF formula in the Cook–Levin theorem.
-/

namespace Lax134656.SuccinctReachPSPACEComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- The problem is PSPACE-complete. -/
axiom succinctReach_PSPACE_complete : PSPACE.Complete SUCCINCTREACH

end Lax134656.SuccinctReachPSPACEComplete
