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
title: PSPACE = coPSPACE
type: theorem
---
The classes PSPACE and coPSPACE are equal: a problem is SO(TC) definable if
and only if its complement is. The complement of a walk is not a walk, so
the closure is not syntactic. Every SO(TC) definable problem reduces to
QSAT, and the walk that decides QSAT is deterministic, computing the value
of the formula; reading its answer the other way round decides the
complement.
-/

namespace Lax134656.PSPACEEqCoPSPACE

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- The complement of an SO(TC) definable problem is SO(TC) definable. -/
axiom sotcDefinable_compl : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  SOTCDefinable P → SOTCDefinable (DecisionProblem.compl P)

/-- PSPACE is closed under complement. -/
axiom PSPACE_eq_coPSPACE : PSPACE = coPSPACE

end Lax134656.PSPACEEqCoPSPACE
