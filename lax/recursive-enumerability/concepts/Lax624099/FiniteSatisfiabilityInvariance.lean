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
title: Invariance and characterization of finite satisfiability
type: lemma
---
Finite satisfiability of an encoded sentence is invariant under isomorphism of
instances, and an instance is a yes-instance of FINSAT exactly when its
encoded sentence has a finite model.
-/

namespace Lax624099.FiniteSatisfiabilityInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- The property `FinSat.FinSatOn` is isomorphism-invariant. -/
axiom finSatOn_iso : ∀ {A B : Type} [finsat.Structure A] [finsat.Structure B],
  (A ≃[finsat] B) → (FinSat.FinSatOn A ↔ FinSat.FinSatOn B)

/-- The yes-instances of FINSAT are exactly the satisfiable encoded
sentences. -/
axiom finsat_iff : ∀ (A : Type) [finsat.Structure A], FINSAT A ↔ FinSat.FinSatOn A

end Lax624099.FiniteSatisfiabilityInvariance
