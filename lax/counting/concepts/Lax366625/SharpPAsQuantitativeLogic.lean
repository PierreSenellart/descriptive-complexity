import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.SecondOrderCounting
import Lax366625.QuantitativeLogic
import Lax366625.CountingSat
import Lax366625.MachineNumbers
import Lax366625.CountingRuns
import Lax366625.NumberedCircuits
import Lax366625.HornNumbers

/-!
---
title: #P = ΣQSO(FO)
type: theorem
---
A counting problem is in #P if and only if it is ΣQSO(FO)-definable: the
witness counts of existential second-order sentences are exactly the values
of the terms of ΣQSO(FO), as Arenas, Muñoz, and Riveros showed. A witness
count is the term that sums the indicator of the kernel over the assignments
of the block; conversely every construction of the logic is a closure
property of witness counts.
-/

namespace Lax366625.SharpPAsQuantitativeLogic

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- #P is ΣQSO(FO) definability. -/
axiom mem_sharpP_iff_sqDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L),
  SharpP.Mem C ↔ SQDefinable C

end Lax366625.SharpPAsQuantitativeLogic
