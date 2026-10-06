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
title: FO(≤, PFP) = SO(TC) = PSPACE
type: theorem
---
On ordered structures, a decision problem is FO($\le$, PFP) definable if
and only if it is SO(TC) definable, that is, in PSPACE: the capture of
polynomial space by partial fixed points, due to Abiteboul and Vianu. A
partial iteration is a deterministic walk on the assignments of
its own block, which gives one direction. Conversely, a partial fixed point
iterates the deterministic machine problem complete for PSPACE: it loads
the initial configuration, takes the unique step while there is one, and
stutters on accepting or stuck configurations, so that a halting run is a
converging iteration; every problem of PSPACE pulls that definition back
along its reduction to the machine problem.
-/

namespace Lax134656.PartialFixedPointCapture

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Every FO(≤, PFP) definable problem is SO(TC) definable. -/
axiom pfpDefinable_sotcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  PFPDefinable P → SOTCDefinable P

/-- Every problem of PSPACE is FO(≤, PFP) definable. -/
axiom pfpDefinable_of_mem_PSPACE : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  PSPACE.Mem P → PFPDefinable P

/-- FO(≤, PFP) definability is membership in PSPACE. -/
axiom pfpDefinable_iff_mem_PSPACE :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PFPDefinable P ↔ PSPACE.Mem P

end Lax134656.PartialFixedPointCapture
