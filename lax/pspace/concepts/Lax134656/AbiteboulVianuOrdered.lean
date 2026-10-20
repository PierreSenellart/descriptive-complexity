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
title: The Abiteboul–Vianu theorem on ordered structures
type: theorem
---
On ordered structures, the inflationary and the partial fixed-point logics
define the same problems if and only if PTIME = PSPACE: FO($\le$, IFP)
captures PTIME and FO($\le$, PFP) captures PSPACE.
-/

namespace Lax134656.AbiteboulVianuOrdered

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- FO(≤, IFP) = FO(≤, PFP) exactly when PTIME = PSPACE. -/
axiom ifpDefinable_eq_pfpDefinable_iff_ptime_eq_pspace :
  (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    IFPDefinable P ↔ PFPDefinable P) ↔ PTIME = PSPACE

end Lax134656.AbiteboulVianuOrdered
