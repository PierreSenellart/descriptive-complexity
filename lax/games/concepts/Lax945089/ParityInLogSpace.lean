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
title: PARITY is in L and not first-order definable
type: theorem
---
PARITY is in L, by one deterministic walk along the order that carries a
bit and flips it at each marked element. It is not FO($\le$) definable:
EVEN reduces to it by a first-order reduction that marks every element, and
FO($\le$) definability is closed under such reductions. That PARITY is not
AC⁰ definable is the switching lemma, which is not proved here.
-/

namespace Lax945089.ParityInLogSpace

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

/-- PARITY is in L. -/
axiom parity_mem_LOGSPACE : LOGSPACE.Mem PARITY

/-- EVEN reduces to PARITY by a first-order reduction. -/
axiom even_fo_reduction_parity : Nonempty (FOReduction EVEN PARITY)

/-- PARITY is not FO(≤) definable. -/
axiom parity_not_foDefinable : ¬FODefinable PARITY

end Lax945089.ParityInLogSpace
