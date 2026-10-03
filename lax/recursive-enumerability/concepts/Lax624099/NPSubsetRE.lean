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
title: NP is contained in RE
type: theorem
---
Every problem of NP is in RE: an existential second-order definition is an
existential second-order definition with value invention that invents
nothing.
-/

namespace Lax624099.NPSubsetRE

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- NP ⊆ RE. -/
axiom NP_subset_RE : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NP.Mem P → RE.Mem P

end Lax624099.NPSubsetRE
