import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: Invariance and characterization of SAT-UNSAT
type: lemma
---
Satisfiability of either formula of a pair is invariant under isomorphism
of instances, and an instance is a yes-instance of SAT-UNSAT exactly when
its first formula is satisfiable and its second is not.
-/

namespace Lax564036.SatUnsatInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Satisfiability of a side of the pair is isomorphism-invariant. -/
axiom satWith_iso : ∀ {A B : Type} [satPair.Structure A] [satPair.Structure B],
  (A ≃[satPair] B) → ∀ (isCl : satPair.Relations 1) (pos neg : satPair.Relations 2),
    (SatWith A isCl pos neg ↔ SatWith B isCl pos neg)

/-- The yes-instances of SAT-UNSAT are exactly the pairs whose first formula is
satisfiable and whose second is not. -/
axiom satUnsat_iff : ∀ (A : Type) [satPair.Structure A],
  SATUNSAT A ↔ (SatWith A spIsCl₁ spPos₁ spNeg₁ ∧ ¬SatWith A spIsCl₂ spPos₂ spNeg₂)

end Lax564036.SatUnsatInvariance
