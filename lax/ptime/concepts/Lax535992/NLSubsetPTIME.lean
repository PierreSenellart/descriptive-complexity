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
title: L ⊆ NL ⊆ PTIME
type: theorem
---
Every problem of NL is in PTIME, and hence so is every problem of L. A Krom
program is not a Horn program, Krom clauses having possibly two positive
literals, so the inclusion is not syntactic: every problem of NL reduces to
2SAT, which a Horn program defines by deriving reachability in the
implication graph and rejecting when a variable reaches its negation and
back.
-/

namespace Lax535992.NLSubsetPTIME

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- NL is contained in PTIME. -/
axiom NL_subset_PTIME : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NL.Mem P → PTIME.Mem P

/-- L is contained in PTIME. -/
axiom LOGSPACE_subset_PTIME : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  LOGSPACE.Mem P → PTIME.Mem P

end Lax535992.NLSubsetPTIME
