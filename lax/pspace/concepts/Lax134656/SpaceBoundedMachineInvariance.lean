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
title: Invariance and characterization of machine acceptance in bounded space
type: lemma
---
Being a well-formed machine instance accepting in bounded space, and being
moreover deterministic, are invariant under isomorphism of instances; an
instance is a yes-instance of machine acceptance in bounded space,
respectively of its deterministic variant, exactly when it has the
corresponding property.
-/

namespace Lax134656.SpaceBoundedMachineInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Being well-formed and accepting in bounded space is isomorphism-invariant. -/
axiom ntmAcceptsSpace_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → (NTMAcceptsSpace A ↔ NTMAcceptsSpace B)

/-- Being well-formed, deterministic and accepting in bounded space is
isomorphism-invariant. -/
axiom dtmAcceptsSpace_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → (DTMAcceptsSpace A ↔ DTMAcceptsSpace B)

/-- The yes-instances of acceptance in bounded space. -/
axiom ntmAcceptSpace_iff : ∀ (A : Type) [turing.Structure A], NTMAcceptSpace A ↔ NTMAcceptsSpace A

/-- The yes-instances of deterministic acceptance in bounded space. -/
axiom dtmAcceptSpace_iff : ∀ (A : Type) [turing.Structure A], DTMAcceptSpace A ↔ DTMAcceptsSpace A

end Lax134656.SpaceBoundedMachineInvariance
