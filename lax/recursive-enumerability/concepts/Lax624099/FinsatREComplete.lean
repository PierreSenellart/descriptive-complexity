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
title: Trakhtenbrot's theorem: finite satisfiability is RE-complete
type: theorem
---
FINSAT is RE-complete: it is definable in existential second-order logic
with value invention, and every problem of RE reduces to it by an ordered
first-order reduction, the generic reduction that writes the definition of a
problem as a sentence whose finite models are its certificates. This is the
logical form of Trakhtenbrot's theorem.
-/

namespace Lax624099.FinsatREComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- FINSAT is RE-complete. -/
axiom finsat_RE_complete : RE.Complete FINSAT

end Lax624099.FinsatREComplete
