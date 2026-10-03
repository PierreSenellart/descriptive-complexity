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
title: The halting problems are undecidable
type: theorem
---
The halting problem of machine instances is not decidable, over any
presentation of the machine vocabulary, and neither is the halting of a drawn
partial recursive code.
-/

namespace Lax624099.HaltingUndecidable

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- The halting problem is undecidable. -/
axiom halt_not_computable : ∀ V : FinVocab turing, ¬ComputablePred (DecisionProblem.toPred HALT V)

/-- Halting of a drawn code is undecidable. -/
axiom codehalt_not_computable : ¬ComputablePred (DecisionProblem.toPred CODEHALT codeVocab)

end Lax624099.HaltingUndecidable
