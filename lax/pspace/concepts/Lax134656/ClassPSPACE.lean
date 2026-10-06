import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Complement
import Lax134656.SecondOrderTransitiveClosure

/-!
---
title: The classes PSPACE and coPSPACE
type: definition
---
PSPACE is the class of decision problems definable in second-order logic
with a transitive closure, SO(TC), which captures polynomial space on
ordered structures. Hardness is the cofinal hardness of the NP core, under
relativized ordered first-order reductions, and coPSPACE is the class of
problems whose complement is in PSPACE. PSPACE-completeness is membership
together with PSPACE-hardness, under first-order reductions. No machine
enters the definition.
-/

namespace Lax134656.ClassPSPACE

open Lax904597.Problems Lax904597.Classes Lax485149.Complement
open Lax134656.SecondOrderTransitiveClosure

/-- **PSPACE**: the class of the SO(TC) definable problems, with cofinal
hardness. -/
def PSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SOTCDefinable P

/-- **coPSPACE**: the problems whose complement is in PSPACE. -/
def coPSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SOTCDefinable (DecisionProblem.compl P)

end Lax134656.ClassPSPACE
