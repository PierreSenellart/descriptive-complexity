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
title: PTIME ⊆ NP
type: theorem
---
Every problem of PTIME is in NP: every SO-Horn definable problem is
definable in existential second-order logic. The guards of a Horn program
being over the ordered expansion of the vocabulary, the inclusion is not
read off the syntax; every problem of PTIME reduces to HORN-SAT, which is in
NP, and NP is closed under ordered first-order reductions.
-/

namespace Lax535992.PTIMESubsetNP

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- PTIME is contained in NP. -/
axiom PTIME_subset_NP : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PTIME.Mem P → NP.Mem P

end Lax535992.PTIMESubsetNP
