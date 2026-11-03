import Lax832283.StringProblems
import Lax904597.Classes
import Lax535992.ClassPTIME
import Lax751879.FixedPointSemantics
import Lax988886.ExistentialSecondOrder

/-!
---
title: NP and PTIME against the logics of the two entries
type: theorem
---
A decision problem is in NP exactly when it reads as a property defined by an existential
second-order sentence of the Fagin entry, and in PTIME exactly when it reads as a query
defined by an FO(LFP) formula of the Immerman–Vardi entry. Neither statement mentions a
machine, and neither proof assumes a capture theorem. The second is the substance of this
submission: the formulas of the entry may nest, negate, and parameterize their fixed points,
whereas the definitions of the library have one simultaneous fixed point.
-/

namespace Lax832283.LogicalBridge

open FirstOrder Lax904597.Problems Lax904597.Classes Lax535992.ClassPTIME
open Lax832283.StringProblems

/-- NP, against the existential second-order logic of the Fagin entry. -/
axiom mem_NP_iff_definable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    NP.Mem P ↔ Lax988886.ExistentialSecondOrder.Definable (toProperty V P)

/-- PTIME, against the FO(LFP) of the Immerman–Vardi entry. -/
axiom mem_PTIME_iff_definable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) :
    PTIME.Mem P ↔ Lax751879.FixedPointSemantics.Definable (toQuery V P)

end Lax832283.LogicalBridge
