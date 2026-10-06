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
title: Characterization of EVEN and PARITY
type: lemma
---
A bare set is a yes-instance of EVEN exactly when it has an even number of
elements, and a set with a marked subset is a yes-instance of PARITY exactly
when the number of marked elements is even: both properties are invariant
under isomorphism.
-/

namespace Lax945089.EvenInvariance

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

/-- The yes-instances of EVEN are exactly the sets of even size. -/
axiom even_iff : ∀ (A : Type) [Language.empty.Structure A], EVEN A ↔ Even (Nat.card A)

/-- The yes-instances of PARITY are exactly the sets with an even marked subset. -/
axiom parity_iff : ∀ (A : Type) [markedSet.Structure A], PARITY A ↔ Even (Marked A).ncard

end Lax945089.EvenInvariance
