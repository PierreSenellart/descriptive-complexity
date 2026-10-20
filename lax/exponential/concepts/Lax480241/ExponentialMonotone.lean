import Lax904597.Problems
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.ClassNL
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.AlternatingMachines
import Lax134656.ClassPSPACE
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax480241.AlternatingSpace
import Lax480241.ExponentialClasses

/-!
---
title: The exponential of classes is monotone
type: theorem
---
If every problem of a class $C$ is in a class $D$, every problem of
$C^{\exp}$ is in $D^{\exp}$: the same expansion serves.
-/

namespace Lax480241.ExponentialMonotone

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- The exponential of classes is monotone. -/
axiom expClass_mono :
  ∀ {C D : ComplexityClass},
    (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L), C.Mem P → D.Mem P) →
    ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L), (expClass C).Mem P →
        (expClass D).Mem P

end Lax480241.ExponentialMonotone
