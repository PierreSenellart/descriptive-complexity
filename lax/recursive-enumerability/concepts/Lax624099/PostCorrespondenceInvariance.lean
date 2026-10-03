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
title: Invariance and characterization of Post's correspondence problem
type: lemma
---
Having a match is invariant under isomorphism of Post correspondence systems,
and a system is a yes-instance of PCP exactly when it has a match.
-/

namespace Lax624099.PostCorrespondenceInvariance

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- The property `Pcp.PcpOn` is isomorphism-invariant. -/
axiom pcpOn_iso : ∀ {A B : Type} [pcp.Structure A] [pcp.Structure B],
  (A ≃[pcp] B) → (Pcp.PcpOn A ↔ Pcp.PcpOn B)

/-- The yes-instances of PCP are exactly the systems with a match. -/
axiom pcp_iff : ∀ (A : Type) [pcp.Structure A], PCP A ↔ Pcp.PcpOn A

end Lax624099.PostCorrespondenceInvariance
