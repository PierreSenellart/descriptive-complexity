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
title: SO-Horn = FO(LFP)
type: theorem
---
A decision problem is SO-Horn definable if and only if it is FO(LFP)
definable. A Horn program is a rule system and its goal clauses an output
sentence, which gives one direction. Conversely, an FO(LFP) definition is
compiled into a Horn program that derives the complement of the fixed point
stage by stage along the order and evaluates the output sentence clause by
clause. This is the equivalence of the two logics on ordered structures, due
to Grädel.
-/

namespace Lax535992.HornIsLeastFixedPoint

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Every SO-Horn definable problem is FO(LFP) definable. -/
axiom sigmaSOHornDefinable_lfpDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  SigmaSOHornDefinable P → LFPDefinable P

/-- Every FO(LFP) definable problem is SO-Horn definable. -/
axiom lfpDefinable_sigmaSOHornDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  LFPDefinable P → SigmaSOHornDefinable P

end Lax535992.HornIsLeastFixedPoint
