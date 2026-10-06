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
title: Invariance and characterization of TAUT
type: lemma
---
Being a DNF tautology is invariant under isomorphism of instances, and an
instance is a yes-instance of TAUT exactly when it is a tautology.
-/

namespace Lax564036.TautologyInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Being a tautology is isomorphism-invariant. -/
axiom tautology_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (Tautology A ↔ Tautology B)

/-- The yes-instances of TAUT are exactly the tautologies. -/
axiom taut_iff : ∀ (A : Type) [sat.Structure A], TAUT A ↔ Tautology A

end Lax564036.TautologyInvariance
