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
title: APSPACE = EXPTIME
type: theorem
---
Acceptance by alternating Turing machines in bounded space is
EXPTIME-complete: APSPACE = EXPTIME. Membership expands the instance to its
configurations, on which acceptance is the game problem of PTIME; hardness
runs a second-order alternating game, which defines every problem of
EXPTIME, on an alternating machine whose tape holds two block assignments.
-/

namespace Lax480241.APSPACEIsEXPTIME

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax485149.Complement Lax485149.ClassNL
open Lax535992.ClassPTIME Lax564036.Hierarchy Lax564036.AlternatingMachines Lax134656.ClassPSPACE
open Lax480241.Expansions Lax480241.SecondOrderFixedPoints Lax480241.AlternatingSpace
    Lax480241.ExponentialClasses

/-- Alternating acceptance in bounded space is EXPTIME-complete. -/
axiom atmAcceptSpace_EXPTIME_complete :
  EXPTIME.Complete ATMAcceptSpace

end Lax480241.APSPACEIsEXPTIME
