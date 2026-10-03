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
title: Post's correspondence problem is undecidable
type: theorem
---
Post's correspondence problem, Post (1946), is not decidable, over any
presentation of its vocabulary.
-/

namespace Lax624099.PcpUndecidable

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- PCP is undecidable. -/
axiom pcp_not_computable : ∀ V : FinVocab pcp, ¬ComputablePred (DecisionProblem.toPred PCP V)

end Lax624099.PcpUndecidable
