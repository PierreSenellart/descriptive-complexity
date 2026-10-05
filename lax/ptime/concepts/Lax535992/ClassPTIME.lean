import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Complement
import Lax535992.HornFragment

/-!
---
title: The classes PTIME and coPTIME
type: definition
---
PTIME is the class of decision problems definable in the Horn fragment of
existential second-order logic, which captures polynomial time on ordered
structures by a theorem of Grädel. Hardness is the cofinal hardness of the
NP core: a problem is PTIME-hard when every problem it reduces to, by a
relativized ordered first-order reduction, is reduced to by every problem of
PTIME. coPTIME is the class of problems whose complement is in PTIME.
PTIME-completeness is membership together with PTIME-hardness, under
first-order reductions. No machine enters the definition.
-/

namespace Lax535992.ClassPTIME

open Lax904597.Problems Lax904597.Classes Lax485149.Complement Lax535992.HornFragment

/-- **PTIME**: the class of the SO-Horn definable problems, with cofinal
hardness. -/
def PTIME : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOHornDefinable P

/-- **coPTIME**: the problems whose complement is in PTIME. -/
def coPTIME : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOHornDefinable (DecisionProblem.compl P)

end Lax535992.ClassPTIME
