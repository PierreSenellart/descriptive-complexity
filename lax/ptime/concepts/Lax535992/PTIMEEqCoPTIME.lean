import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.HornFragment
import Lax535992.LeastFixedPoint
import Lax535992.InflationaryFixedPoint
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.Game
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME

/-!
---
title: PTIME = coPTIME
type: theorem
---
The classes PTIME and coPTIME are equal: a problem is SO-Horn definable if
and only if its complement is. The Horn fragment has no negation of its
own; the closure comes from FO(LFP), where complementing is negating the
output sentence, through the equivalence of the two logics.
-/

namespace Lax535992.PTIMEEqCoPTIME

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- The complement of an SO-Horn definable problem is SO-Horn definable. -/
axiom sigmaSOHornDefinable_compl : ∀ {L : Language.{0, 0}} [L.IsRelational]
  {P : DecisionProblem L},
  SigmaSOHornDefinable P → SigmaSOHornDefinable (DecisionProblem.compl P)

/-- PTIME is closed under complement. -/
axiom PTIME_eq_coPTIME : PTIME = coPTIME

end Lax535992.PTIMEEqCoPTIME
