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
title: The Immerman–Vardi theorem: PTIME = FO(LFP)
type: theorem
---
A decision problem is in PTIME if and only if it is FO(LFP) definable, on
ordered structures. With PTIME defined by the Horn fragment, this is the
Immerman–Vardi theorem read through the equivalence of SO-Horn and
FO(LFP).
-/

namespace Lax535992.ImmermanVardi

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- FO(LFP) definability is membership in PTIME. -/
axiom lfpDefinable_iff_mem_PTIME : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  LFPDefinable P ↔ PTIME.Mem P

end Lax535992.ImmermanVardi
