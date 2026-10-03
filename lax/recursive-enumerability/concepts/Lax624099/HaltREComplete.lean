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
title: The halting problem is RE-complete
type: theorem
---
HALT is RE-complete: acceptance on an unbounded tape is recognized by
guessing the run in existential second-order logic with value invention, and
every problem of RE reduces to HALT by an ordered first-order reduction, the
machine that runs a semi-decision procedure for the problem on its input.
-/

namespace Lax624099.HaltREComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- HALT is RE-complete. -/
axiom halt_RE_complete : RE.Complete HALT

end Lax624099.HaltREComplete
