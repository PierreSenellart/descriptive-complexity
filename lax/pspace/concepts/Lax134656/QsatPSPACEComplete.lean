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
title: QSAT is PSPACE-complete
type: theorem
---
QSAT is PSPACE-complete under first-order reductions, a theorem of
Stockmeyer and Meyer, and hence also coPSPACE-complete. It is SO(TC)
definable, by a deterministic walk that computes the value of the formula.
Hardness goes through SUCCINCT-REACH and the recursive doubling of
Savitch's theorem: a path of length $2^m$ between two states is a
quantified formula with $m$ alternations asking for a midpoint and for both
halves.
-/

namespace Lax134656.QsatPSPACEComplete

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
axiom qsat_PSPACE_complete : PSPACE.Complete QSAT

/-- QSAT is coPSPACE-complete. -/
axiom qsat_coPSPACE_complete : coPSPACE.Complete QSAT

end Lax134656.QsatPSPACEComplete
