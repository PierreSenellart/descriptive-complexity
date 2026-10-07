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
title: Wide machines are complete for NEXPTIME and EXPSPACE
type: theorem
---
Wide acceptance is in NEXPTIME, and wide acceptance with a regular channel
is NEXPTIME-complete: a wide machine is an ordinary machine read over an
exponential expansion, and hardness lays the computation of a problem of
NEXPTIME out along the addresses, block by block. Wide acceptance in space
is EXPSPACE-complete, deterministic or not. The three wide acceptance
problems have yes-instances.
-/

namespace Lax822549.WideMachinesComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax480241.ExponentialClasses
open Lax822549.WideMachines Lax822549.WideRegChannel Lax822549.WideTilings

/-- Wide acceptance is in NEXPTIME. -/
axiom wideAccept_mem_NEXPTIME :
  NEXPTIME.Mem WideAccept

/-- Wide acceptance with a regular channel is NEXPTIME-complete. -/
axiom wideRegAccept_NEXPTIME_complete :
  NEXPTIME.Complete WideRegAccept

/-- Wide acceptance in space is EXPSPACE-complete. -/
axiom wideAcceptSpace_EXPSPACE_complete :
  EXPSPACE.Complete WideAcceptSpace

/-- Deterministic wide acceptance in space is EXPSPACE-complete. -/
axiom dwideAcceptSpace_EXPSPACE_complete :
  EXPSPACE.Complete DWideAcceptSpace

/-- WideAccept has a finite yes-instance. -/
axiom wideAccept_nonvacuous :
  ∃ (A : Type) (_ : wide.Structure A), Finite A ∧ WideAccept A

/-- WideAcceptSpace has a finite yes-instance. -/
axiom wideAcceptSpace_nonvacuous :
  ∃ (A : Type) (_ : wide.Structure A), Finite A ∧ WideAcceptSpace A

/-- DWideAcceptSpace has a finite yes-instance. -/
axiom dwideAcceptSpace_nonvacuous :
  ∃ (A : Type) (_ : wide.Structure A), Finite A ∧ DWideAcceptSpace A

end Lax822549.WideMachinesComplete
