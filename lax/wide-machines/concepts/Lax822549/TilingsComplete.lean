import Lax904597.Problems
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax535992.DeterministicMachines
import Lax134656.SpaceBoundedMachines
import Lax480241.ExponentialClasses
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings

/-!
---
title: Tilings one exponential up are complete
type: theorem
---
Square tiling one exponential up is NEXPTIME-complete and corridor tiling
one exponential up is EXPSPACE-complete, the classical second complete
problems of the two classes beside a machine: the rows of a tiling are the
configurations of a wide machine.
-/

namespace Lax822549.TilingsComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax480241.ExponentialClasses
open Lax822549.WideMachines Lax822549.WideRegChannel Lax822549.WideTilings

/-- Square tiling one exponential up is NEXPTIME-complete. -/
axiom wideTiling_NEXPTIME_complete :
  NEXPTIME.Complete WideTiling

/-- Corridor tiling one exponential up is EXPSPACE-complete. -/
axiom wideCorridor_EXPSPACE_complete :
  EXPSPACE.Complete WideCorridor

end Lax822549.TilingsComplete
