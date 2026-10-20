import Mathlib.ModelTheory.Order
import Mathlib.Order.Defs.LinearOrder
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax485149.Problems
import Lax485149.FirstOrderDefinability
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.InflationaryFixedPoint
import Lax535992.ClassPTIME
import Lax134656.PartialFixedPoint
import Lax895169.ArithmeticLogic
import Lax945089.OrderFreeFirstOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.PebbleGames
import Lax945089.Even
import Lax945089.Parity
import Lax945089.TransitiveClosureReductions

/-!
---
title: FO(≤) ⊊ FO(DTC): EVEN is a deterministic walk
type: theorem
---
EVEN is FO(DTC) definable, hence FO(TC) definable, in NL and in PTIME: one
deterministic walk along the order, stepping to the successor and flipping
a bit, decides the parity of the universe. Since EVEN is not FO($\le$)
definable, the inclusion of FO($\le$) in FO(TC) is strict, with no
complexity-theoretic assumption.
-/

namespace Lax945089.FirstOrderBelowTransitiveClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes
open Lax485149.Problems Lax485149.FirstOrderDefinability Lax485149.TransitiveClosure
open Lax485149.DeterministicTransitiveClosure Lax485149.ClassNL Lax485149.ClassL
open Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME
open Lax134656.PartialFixedPoint Lax895169.ArithmeticLogic
open Lax945089.OrderFreeFirstOrder Lax945089.EhrenfeuchtGames Lax945089.PebbleGames
open Lax945089.Even Lax945089.Parity
open Lax945089.TransitiveClosureReductions

/-- EVEN is FO(DTC) definable. -/
axiom even_dtcDefinable : DTCDefinable EVEN

/-- EVEN is FO(TC) definable. -/
axiom even_tcDefinable : TCDefinable EVEN

/-- EVEN is in NL. -/
axiom even_mem_NL : NL.Mem EVEN

/-- EVEN is in PTIME. -/
axiom even_mem_PTIME : PTIME.Mem EVEN

/-- Some FO(TC) definable problem is not FO(≤) definable. -/
axiom exists_tcDefinable_not_foDefinable :
  ∃ P : DecisionProblem Language.empty, TCDefinable P ∧ ¬FODefinable P

end Lax945089.FirstOrderBelowTransitiveClosure
