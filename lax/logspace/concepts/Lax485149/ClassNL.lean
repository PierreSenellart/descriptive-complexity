import Lax904597.Problems
import Lax904597.Classes
import Lax485149.Complement
import Lax485149.KromFragment

/-!
---
title: The classes NL and coNL
type: definition
---
NL is the class of decision problems definable in the Krom fragment of
existential second-order logic, which captures nondeterministic logarithmic
space on ordered structures by a theorem of Grädel. Hardness is the cofinal
hardness of the NP core: a problem is NL-hard when every problem it reduces
to, by a relativized ordered first-order reduction, is reduced to by every
problem of NL. coNL is the class of problems whose complement is in NL.
NL-completeness is membership together with NL-hardness. No machine enters
the definition.
-/

namespace Lax485149.ClassNL

open Lax904597.Problems Lax904597.Classes Lax485149.Complement Lax485149.KromFragment

/-- **NL**: the class of the SO-Krom definable problems, with cofinal
hardness. -/
def NL : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOKromDefinable P

/-- **coNL**: the problems whose complement is in NL. -/
def coNL : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOKromDefinable (DecisionProblem.compl P)

end Lax485149.ClassNL
