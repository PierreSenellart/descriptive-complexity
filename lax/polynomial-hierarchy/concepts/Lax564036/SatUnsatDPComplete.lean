import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: SAT-UNSAT is DP-complete
type: theorem
---
SAT-UNSAT is DP-complete under first-order reductions, a theorem of
Papadimitriou and Yannakakis. It is in DP, each side projecting onto a
plain CNF instance; and every DP-definable problem reduces to it, by running
the Cook–Levin reduction of its NP half and of the complement of its coNP
half side by side into one paired instance.
-/

namespace Lax564036.SatUnsatDPComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- SAT-UNSAT is DP-complete. -/
axiom satUnsat_DP_complete : DP.Complete SATUNSAT

end Lax564036.SatUnsatDPComplete
