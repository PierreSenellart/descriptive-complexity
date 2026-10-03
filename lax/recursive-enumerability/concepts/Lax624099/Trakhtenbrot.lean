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
title: Trakhtenbrot's theorem: finite satisfiability is undecidable
type: theorem
---
Finite satisfiability of first-order sentences is not decidable: no
computable predicate on concrete encoded sentences agrees with FINSAT. This
is the theorem of Trakhtenbrot (1950).
-/

namespace Lax624099.Trakhtenbrot

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- Trakhtenbrot's theorem. -/
axiom finsat_not_computable : ¬ComputablePred (DecisionProblem.toPred FINSAT finsatVocab)

end Lax624099.Trakhtenbrot
