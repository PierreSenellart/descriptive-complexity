import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Difference
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax564036.SatUnsat
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.AlternatingMachines

/-!
---
title: 3-DNF-TAUT and 3-UNSAT are coNP-complete
type: theorem
---
3-DNF-TAUT and 3-UNSAT are coNP-complete under first-order reductions. The
clause-splitting reduction of SAT to 3SAT reduces the complement of SAT to
3-UNSAT, on the CNF side where the width bound is available, and the sign
swap carries 3-UNSAT to 3-DNF-TAUT.
-/

namespace Lax564036.ThreeDnfTautCoNPComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology
open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- 3-DNF-TAUT is coNP-complete. -/
axiom threeDnfTaut_coNP_complete : coNP.Complete ThreeDnfTAUT

/-- 3-UNSAT is coNP-complete. -/
axiom threeUnsat_coNP_complete : coNP.Complete ThreeUNSAT

end Lax564036.ThreeDnfTautCoNPComplete
