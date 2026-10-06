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
title: #SAT is parsimoniously #P-complete
type: theorem
---
#SAT is parsimoniously #P-complete, a theorem of Valiant: it is in #P, and
every problem of #P reduces to it by an ordered parsimonious reduction. The
reduction is that of the Cook–Levin theorem, made parsimonious: the
assignments of a block satisfying a first-order kernel are in bijection with
the models of the formula it produces, the auxiliary variables of the
Tseitin encoding being determined.
-/

namespace Lax366625.SharpSatComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- #SAT is parsimoniously #P-complete. -/
axiom sharpSat_sharpP_parsimoniousComplete : SharpP.ParsimoniousComplete SharpSAT

end Lax366625.SharpSatComplete
