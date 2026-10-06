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
title: #P by counting the accepting runs of a Turing machine
type: theorem
---
Counting accepting runs is parsimoniously #P-complete, and a counting problem
is in #P if and only if it reduces to it by an ordered parsimonious
reduction: #P is the class of the numbers of accepting runs of
nondeterministic polynomial-time machines. Membership counts the tableaux of
the runs, which the runs determine; hardness builds the machine of the
Cook–Levin theorem, which guesses only at the variables of a formula, so
that its accepting runs are the models.
-/

namespace Lax366625.CountingRunsComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- Counting accepting runs is parsimoniously #P-complete. -/
axiom sharpNtmAccept_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpNTMAccept

/-- #P is reducibility to counting accepting runs. -/
axiom mem_sharpP_iff_le_sharpNtmAccept :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L),
  SharpP.Mem C ↔ Nonempty (OrderedParsimoniousReduction C SharpNTMAccept)

end Lax366625.CountingRunsComplete
