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
title: SO(TC) does not need an order
type: theorem
---
A decision problem is SO(TC) definable if and only if it is order-free
SO(TC) definable, so PSPACE is the class of the order-free SO(TC) definable
problems. A walk can guess its order: one more binary relation variable of
the state holds a candidate order, the source sentence checks that it is
linear, every step keeps it unchanged, and the three sentences read it in
place of the order symbol. The deterministic and the clausal logics of the
classes below cannot do this.
-/

namespace Lax134656.TransitiveClosureWithoutOrder

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- SO(TC) definability and its order-free form coincide. -/
axiom sotcDefinable_iff_free : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  SOTCDefinable P ↔ SOTCDefinableFree P

/-- PSPACE is order-free SO(TC) definability. -/
axiom mem_PSPACE_iff_sotcDefinableFree :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PSPACE.Mem P ↔ SOTCDefinableFree P

end Lax134656.TransitiveClosureWithoutOrder
