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
title: RE is recursive enumerability
type: theorem
---
A decision problem is in RE exactly when the set of its concrete instances,
over any presentation of its vocabulary, is recursively enumerable in the
sense of Mathlib's computability theory.
-/

namespace Lax624099.REIsRecursivelyEnumerable

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- RE is exactly the recursively enumerable properties of finite
structures. -/
axiom mem_RE_iff_rePred : ∀ {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
  (P : DecisionProblem L), RE.Mem P ↔ REPred (DecisionProblem.toPred P V)

end Lax624099.REIsRecursivelyEnumerable
