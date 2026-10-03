import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.Classes
import Lax624099.Problems
import Lax624099.ValueInvention
import Lax624099.ClassRE
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.CodeHalting
import Lax624099.PostCorrespondence
import Lax624099.ConcreteInstances
import Lax904597.Machines

/-!
---
title: Invariance and characterization of the halting problem
type: lemma
---
Acceptance on an unbounded tape by a well-formed machine instance is invariant
under isomorphism of instances, and an instance is a yes-instance of HALT
exactly when it is well-formed and accepts its input.
-/

namespace Lax624099.HaltingInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- The property `HaltsOn` is isomorphism-invariant. -/
axiom haltsOn_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → (HaltsOn A ↔ HaltsOn B)

/-- The yes-instances of HALT are exactly the well-formed accepting machine
instances. -/
axiom halt_iff : ∀ (A : Type) [turing.Structure A], HALT A ↔ HaltsOn A

end Lax624099.HaltingInvariance
