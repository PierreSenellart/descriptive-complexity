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
title: PSPACE by Turing machines in bounded space
type: theorem
---
Machine acceptance in bounded space and its deterministic variant are both
PSPACE-complete under first-order reductions, and every problem of PSPACE
reduces to the deterministic one: the class defined by SO(TC) is polynomial
space on Turing machines, deterministic or not, which is PSPACE = NPSPACE
in this setting. A configuration is an assignment of a block of three
relation variables and a step a first-order condition on two consecutive
assignments, which gives membership. Hardness is proved for the
deterministic problem, by a machine that evaluates a quantified Boolean
formula with one bit of recursion stack per variable.
-/

namespace Lax134656.SpaceMachinesPSPACEComplete

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
axiom dtmAcceptSpace_PSPACE_complete : PSPACE.Complete DTMAcceptSpace

/-- The problem is PSPACE-complete. -/
axiom ntmAcceptSpace_PSPACE_complete : PSPACE.Complete NTMAcceptSpace

/-- Every problem of PSPACE reduces to deterministic acceptance in bounded space. -/
axiom le_dtmAcceptSpace_of_mem_PSPACE :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PSPACE.Mem P → Nonempty (RelOrderedFOReduction P DTMAcceptSpace)

end Lax134656.SpaceMachinesPSPACEComplete
