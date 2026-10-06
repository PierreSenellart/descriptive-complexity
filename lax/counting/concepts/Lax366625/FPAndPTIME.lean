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
title: FP and PTIME
type: theorem
---
The support of a problem of FP is in PTIME. Hence a problem of FP that is
parsimoniously #P-hard gives NP ⊆ PTIME.
-/

namespace Lax366625.FPAndPTIME

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The support of a problem of FP is in PTIME. -/
axiom support_mem_PTIME_of_mem_FP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
  FP.Mem C → PTIME.Mem C.support

/-- A parsimoniously #P-hard problem in FP gives NP ⊆ PTIME. -/
axiom NP_subset_PTIME_of_mem_FP_of_parsimoniousHard :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
  FP.Mem C → SharpP.ParsimoniousHard C →
    ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'), NP.Mem P → PTIME.Mem P

end Lax366625.FPAndPTIME
