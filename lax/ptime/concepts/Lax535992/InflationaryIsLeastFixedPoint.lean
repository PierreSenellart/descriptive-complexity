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
title: FO(≤, IFP) = FO(LFP) = PTIME
type: theorem
---
On ordered structures, a decision problem is FO($\le$, IFP) definable if
and only if it is FO(LFP) definable, hence if and only if it is in PTIME.
A rule system is one simultaneous step, inflation supplying the
monotonicity, which gives one direction. Conversely, an inflationary
induction is compiled into FO(LFP) by walking its stages along the order,
with an evaluator that derives positively both the truth and the falsity of
the subformulas of the step formulas at each stage; inflation is what makes
the complement of a stage advance positively.
-/

namespace Lax535992.InflationaryIsLeastFixedPoint

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Every FO(LFP) definable problem is FO(≤, IFP) definable. -/
axiom lfpDefinable_ifpDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  LFPDefinable P → IFPDefinable P

/-- Every FO(≤, IFP) definable problem is FO(LFP) definable. -/
axiom ifpDefinable_lfpDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  IFPDefinable P → LFPDefinable P

/-- FO(≤, IFP) definability is membership in PTIME. -/
axiom ifpDefinable_iff_mem_PTIME : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  IFPDefinable P ↔ PTIME.Mem P

end Lax535992.InflationaryIsLeastFixedPoint
