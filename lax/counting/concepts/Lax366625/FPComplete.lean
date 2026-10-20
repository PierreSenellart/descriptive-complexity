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
title: FP-complete problems
type: theorem
---
The number written by a circuit, the number written by unit propagation on
a Horn formula, and the number written by a deterministic Turing machine are
parsimoniously FP-complete, and a counting problem is in FP if and only if
it reduces to the machine problem by an ordered parsimonious reduction: FP
is the class of the numbers written by deterministic polynomial-time
machines.
-/

namespace Lax366625.FPComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The number written by a circuit is parsimoniously FP-complete. -/
axiom circuitNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete CircuitNumber

/-- The number written by unit propagation is parsimoniously FP-complete. -/
axiom hornNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete HornNumber

/-- The number written by a deterministic machine is parsimoniously FP-complete. -/
axiom dtmNumber_FP_parsimoniousComplete : FP.ParsimoniousComplete DTMNumber

/-- FP is reducibility to the number written by a deterministic machine. -/
axiom mem_FP_iff_le_dtmNumber : ∀ {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L),
  FP.Mem C ↔ Nonempty (OrderedParsimoniousReduction C DTMNumber)

end Lax366625.FPComplete
