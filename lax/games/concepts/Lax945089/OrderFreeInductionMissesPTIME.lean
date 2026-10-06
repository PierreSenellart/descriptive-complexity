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
title: Order-free FO(IFP) does not capture PTIME
type: theorem
---
EVEN is not order-free FO(IFP) definable: an inflationary induction with
variable budget $k$ cannot separate two bare sets with at least $k$
elements, by the $k$-pebble game. EVEN being in PTIME, the inflationary
fixed-point logic without an order does not capture polynomial time; the
order in the capture theorems is necessary.
-/

namespace Lax945089.OrderFreeInductionMissesPTIME

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

/-- EVEN is not order-free FO(IFP) definable. -/
axiom even_not_ifpDefinableFree : ¬IFPDefinableFree EVEN

/-- Some problem of PTIME is not order-free FO(IFP) definable. -/
axiom exists_mem_PTIME_not_ifpDefinableFree :
  ∃ P : DecisionProblem Language.empty, PTIME.Mem P ∧ ¬IFPDefinableFree P

end Lax945089.OrderFreeInductionMissesPTIME
