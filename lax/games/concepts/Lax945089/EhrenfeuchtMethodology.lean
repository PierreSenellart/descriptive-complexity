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
title: The Ehrenfeucht–Fraïssé method
type: theorem
---
If two structures over a relational vocabulary are $n$-round equivalent,
they satisfy the same first-order sentences of quantifier depth at most
$n$. Every inexpressibility result below is a contrapositive of this.
-/

namespace Lax945089.EhrenfeuchtMethodology

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

/-- `n`-round equivalent structures satisfy the same sentences of depth at most `n`. -/
axiom realize_sentence_of_efEquiv :
  ∀ {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N] {n : ℕ} [L.IsRelational],
  EFEquiv L M N n → ∀ (φ : L.Sentence), qdepth φ ≤ n → (M ⊨ φ ↔ N ⊨ φ)

end Lax945089.EhrenfeuchtMethodology
