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
title: Invariance and characterization of code halting
type: lemma
---
Halting of the code drawn at the root is invariant under isomorphism of
instances, and an instance is a yes-instance of CODEHALT exactly when its root
draws a code that halts on zero.
-/

namespace Lax624099.CodeHaltingInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- The property `CodeHaltsOn` is isomorphism-invariant. -/
axiom codeHaltsOn_iso : ∀ {A B : Type} [code.Structure A] [code.Structure B],
  (A ≃[code] B) → (CodeHaltsOn A ↔ CodeHaltsOn B)

/-- The yes-instances of CODEHALT are exactly the instances whose root draws a
halting code. -/
axiom codehalt_iff : ∀ (A : Type) [code.Structure A], CODEHALT A ↔ CodeHaltsOn A

end Lax624099.CodeHaltingInvariance
