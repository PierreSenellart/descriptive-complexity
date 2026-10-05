import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Complement
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure

/-!
---
title: The classes L and coL
type: definition
---
L, deterministic logarithmic space, is the class of decision problems
definable in first-order logic with a deterministic transitive closure,
which captures it on ordered structures by a theorem of Immerman. Hardness
is the cofinal hardness of the NP core, under relativized ordered
first-order reductions, and coL is the class of problems whose complement is
in L. L-completeness is membership together with L-hardness. No machine
enters the definition.
-/

namespace Lax485149.ClassL

open Lax904597.Problems Lax904597.Classes Lax485149.Complement
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure

/-- **L**: the class of the FO(DTC) definable problems, with cofinal
hardness. -/
def LOGSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => DTCDefinable P

/-- **coL**: the problems whose complement is in L. -/
def coLOGSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => DTCDefinable (DecisionProblem.compl P)

end Lax485149.ClassL
