import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.InflationaryFixedPoint
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SuccinctReach
import Lax134656.SpaceBoundedMachines
import Lax134656.ClassPSPACE

/-!
---
title: Invariance and characterization of QSAT
type: lemma
---
Being a well-formed true quantified Boolean formula is invariant under
isomorphism of instances, and an instance is a yes-instance of QSAT exactly
when it is well formed and true.
-/

namespace Lax134656.QsatInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Being well formed and true is isomorphism-invariant. -/
axiom qsatHolds_iso : ∀ {A B : Type} [qsat.Structure A] [qsat.Structure B],
  (A ≃[qsat] B) → (QsatHolds A ↔ QsatHolds B)

/-- The yes-instances are exactly the instances with the defining property. -/
axiom qsat_iff : ∀ (A : Type) [qsat.Structure A], QSAT A ↔ QsatHolds A

end Lax134656.QsatInvariance
