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
title: Code halting is RE-complete
type: theorem
---
CODEHALT is RE-complete: a drawn code halting on zero is recognized by
guessing its computation in existential second-order logic with value
invention, and every problem of RE reduces to CODEHALT by an ordered
first-order reduction that draws the instance as the program running a
semi-decision procedure for the problem on it.
-/

namespace Lax624099.CodehaltREComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- CODEHALT is RE-complete. -/
axiom codehalt_RE_complete : RE.Complete CODEHALT

end Lax624099.CodehaltREComplete
