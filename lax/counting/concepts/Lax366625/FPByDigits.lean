import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.SecondOrderCounting
import Lax366625.QuantitativeLogic
import Lax366625.CountingSat
import Lax366625.MachineNumbers
import Lax366625.CountingRuns
import Lax366625.NumberedCircuits
import Lax366625.HornNumbers

/-!
---
title: FP by binary digits and by quantitative terms
type: theorem
---
A counting problem is in FP if and only if it is digit-definable: its binary
digits are relations of a least fixed point. And the value of a closed QFO
term, with no fixed point at all, defines a problem in FP.
-/

namespace Lax366625.FPByDigits

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- FP is digit definability. -/
axiom digitDefinable_iff_mem_FP : ∀ {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L),
  DigitDefinable C ↔ FP.Mem C

/-- The value of a closed quantitative first-order term is in FP. -/
axiom fpDefinable_of_qfo :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L} (t : QTerm
    (L.sum Language.order) Empty),
  (∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], C A = t.value A) →
    FP.Mem C

end Lax366625.FPByDigits
