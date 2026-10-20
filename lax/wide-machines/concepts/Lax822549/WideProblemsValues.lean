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
title: The wide problems, characterized
type: lemma
---
The conditions of the wide machine and tiling problems are invariant under
isomorphism of instances, so each problem holds of an instance exactly when
its conditions do.
-/

namespace Lax822549.WideProblemsValues

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax480241.ExponentialClasses
open Lax822549.WideMachines Lax822549.WideRegChannel Lax822549.WideTilings

/-- The problem holds exactly when its conditions do. -/
axiom wideAccept_iff :
  ∀ (A : Type) [wide.Structure A],
    WideAccept A ↔ TMData.WellFormed (wideData A) ∧ TMData.Accepts (wideData A)

/-- The problem holds exactly when its conditions do. -/
axiom wideAcceptSpace_iff :
  ∀ (A : Type) [wide.Structure A],
    WideAcceptSpace A ↔ TMData.WellFormed (wideData A) ∧
      Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A)

/-- The problem holds exactly when its conditions do. -/
axiom dwideAcceptSpace_iff :
  ∀ (A : Type) [wide.Structure A],
    DWideAcceptSpace A ↔ TMData.WellFormed
        (wideData A) ∧ Lax535992.DeterministicMachines.TMData.Deterministic (wideData A) ∧
      Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A)

/-- The problem holds exactly when its conditions do. -/
axiom wideRegAccept_iff :
  ∀ (A : Type) [wide.Structure A],
    WideRegAccept A ↔ TMData.WellFormed (wideRegData A) ∧ TMData.Accepts (wideRegData A)

/-- The problem holds exactly when its conditions do. -/
axiom wideTiling_iff :
  ∀ (A : Type) [wtile.Structure A],
    WideTiling A ↔ (wideTileData A).WellFormed ∧ (wideTileData A).Tileable

/-- The problem holds exactly when its conditions do. -/
axiom wideCorridor_iff :
  ∀ (A : Type) [wtile.Structure A],
    WideCorridor A ↔ (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable

end Lax822549.WideProblemsValues
