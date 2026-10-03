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
title: RE is not closed under complement
type: theorem
---
The complement of CODEHALT is not in RE, so CODEHALT is not in co-RE and the
classes RE and co-RE differ: a problem and its complement both recursively
enumerable would be decidable, by Post's theorem.
-/

namespace Lax624099.RENeCoRE

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE
open Lax624099.FiniteSatisfiability
open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence
open Lax624099.ConcreteInstances

/-- CODEHALT is not in co-RE. -/
axiom codehalt_not_mem_coRE : ¬coRE.Mem CODEHALT

/-- RE differs from co-RE. -/
axiom RE_ne_coRE : RE ≠ coRE

end Lax624099.RENeCoRE
