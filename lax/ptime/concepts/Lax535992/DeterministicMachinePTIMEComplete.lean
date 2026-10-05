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
title: PTIME by deterministic Turing machines
type: theorem
---
Deterministic machine acceptance is PTIME-complete under first-order
reductions, and a decision problem is in PTIME if and only if it reduces to
deterministic machine acceptance by an ordered first-order reduction: the
class defined by the Horn fragment is polynomial time on deterministic
Turing machines, the reduction supplying the machine, its input and its
polynomial bound. Membership is an FO(LFP) definition of the unique run;
hardness builds, inside the instance, the machine that runs unit
propagation on a Horn formula.
-/

namespace Lax535992.DeterministicMachinePTIMEComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Deterministic machine acceptance is PTIME-complete. -/
axiom dtmAccept_PTIME_complete : PTIME.Complete DTMAccept

/-- PTIME is reducibility to deterministic machine acceptance. -/
axiom mem_PTIME_iff_le_dtmAccept : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PTIME.Mem P ↔ Nonempty (OrderedFOReduction P DTMAccept)

end Lax535992.DeterministicMachinePTIMEComplete
