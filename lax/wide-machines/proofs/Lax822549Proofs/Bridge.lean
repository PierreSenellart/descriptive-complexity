import Lax822549.WideProblemsValues
import Lax822549.WideMachinesComplete
import Lax822549.TilingsComplete
import Lax822549Proofs.DescriptiveComplexity.Complexity
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Corridor
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.CorridorHard
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Defs
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Instance
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Membership
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Reduce
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannel
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannelReduce
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Tiling
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.TilingHard

/-!
# Wide machines and tilings, from the library's theorems

The problems are defined in the concepts from their conditions, which are the
library's, and agree with the library's problems through the invariance of
these conditions; the classes are those of the required submission.
-/

namespace Lax822549Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax480241.ExponentialClasses
open Lax822549.WideMachines Lax822549.WideRegChannel Lax822549.WideTilings

/-- A problem given by an isomorphism-invariant property holds exactly when the
property does. -/
theorem ofPred_iff {L : Language.{0, 0}} [L.IsRelational] {Q : ∀ (A : Type) [L.Structure A], Prop}
    (hQ : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → (Q A ↔ Q B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred Q V ↔ Q V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hQ f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

/-- Completeness for a class of the library, transported along an agreement of
the finite instances. -/
theorem complete_congr (C : DescriptiveComplexity.ComplexityClass)
    {L : Language.{0, 0}} [L.IsRelational]
    {Q Q' : DecisionProblem L} (h : ∀ (A : Type) [L.Structure A] [Finite A], Q A ↔ Q' A)
    (hc : C.Complete Q) : C.Mem Q' ∧ C.Hard Q' :=
  ⟨(C.mem_congr_finite h).mp hc.1, (C.hard_congr_finite h).mp hc.2⟩

/--
---
conclusion: Lax822549.WideProblemsValues.wideAccept_iff
---
The library's problem is invariant.
-/
theorem wideAccept_iff (A : Type) [wide.Structure A] :
    WideAccept A ↔ TMData.WellFormed (wideData A) ∧ TMData.Accepts (wideData A) :=
  ofPred_iff (fun e => (DescriptiveComplexity.WideAccept).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem wideAccept_agree (A : Type) [wide.Structure A] :
    DescriptiveComplexity.WideAccept A ↔ WideAccept A :=
  (wideAccept_iff A).symm

/--
---
conclusion: Lax822549.WideProblemsValues.wideAcceptSpace_iff
---
The library's problem is invariant.
-/
theorem wideAcceptSpace_iff (A : Type) [wide.Structure A] :
    WideAcceptSpace A ↔ TMData.WellFormed (wideData A) ∧
      Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A) :=
  ofPred_iff (fun e => (DescriptiveComplexity.WideAcceptSpace).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem wideAcceptSpace_agree (A : Type) [wide.Structure A] :
    DescriptiveComplexity.WideAcceptSpace A ↔ WideAcceptSpace A :=
  (wideAcceptSpace_iff A).symm

/--
---
conclusion: Lax822549.WideProblemsValues.dwideAcceptSpace_iff
---
The library's problem is invariant.
-/
theorem dwideAcceptSpace_iff (A : Type) [wide.Structure A] :
    DWideAcceptSpace A ↔ TMData.WellFormed
        (wideData A) ∧ Lax535992.DeterministicMachines.TMData.Deterministic (wideData A) ∧
      Lax134656.SpaceBoundedMachines.TMData.AcceptsSpace (wideData A) :=
  ofPred_iff (fun e => (DescriptiveComplexity.DWideAcceptSpace).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem dwideAcceptSpace_agree (A : Type) [wide.Structure A] :
    DescriptiveComplexity.DWideAcceptSpace A ↔ DWideAcceptSpace A :=
  (dwideAcceptSpace_iff A).symm

/--
---
conclusion: Lax822549.WideProblemsValues.wideRegAccept_iff
---
The library's problem is invariant.
-/
theorem wideRegAccept_iff (A : Type) [wide.Structure A] :
    WideRegAccept A ↔ TMData.WellFormed (wideRegData A) ∧ TMData.Accepts (wideRegData A) :=
  ofPred_iff (fun e => (DescriptiveComplexity.WideRegAccept).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem wideRegAccept_agree (A : Type) [wide.Structure A] :
    DescriptiveComplexity.WideRegAccept A ↔ WideRegAccept A :=
  (wideRegAccept_iff A).symm

/--
---
conclusion: Lax822549.WideProblemsValues.wideTiling_iff
---
The library's problem is invariant.
-/
theorem wideTiling_iff (A : Type) [wtile.Structure A] :
    WideTiling A ↔ (wideTileData A).WellFormed ∧ (wideTileData A).Tileable :=
  ofPred_iff (fun e => (DescriptiveComplexity.WideTiling).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem wideTiling_agree (A : Type) [wtile.Structure A] :
    DescriptiveComplexity.WideTiling A ↔ WideTiling A :=
  (wideTiling_iff A).symm

/--
---
conclusion: Lax822549.WideProblemsValues.wideCorridor_iff
---
The library's problem is invariant.
-/
theorem wideCorridor_iff (A : Type) [wtile.Structure A] :
    WideCorridor A ↔ (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable :=
  ofPred_iff (fun e => (DescriptiveComplexity.WideCorridor).iso_invariant e) A

/-- The library's problem and the concept's agree. -/
theorem wideCorridor_agree (A : Type) [wtile.Structure A] :
    DescriptiveComplexity.WideCorridor A ↔ WideCorridor A :=
  (wideCorridor_iff A).symm

/--
---
conclusion: Lax822549.WideMachinesComplete.wideAccept_mem_NEXPTIME
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem wideAccept_mem_NEXPTIME : NEXPTIME.Mem WideAccept :=
  (DescriptiveComplexity.NEXPTIME.mem_congr_finite fun A _ _ =>
      wideAccept_agree A).mp DescriptiveComplexity.wideAccept_mem_NEXPTIME

/--
---
conclusion: Lax822549.WideMachinesComplete.wideRegAccept_NEXPTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem wideRegAccept_NEXPTIME_complete : NEXPTIME.Complete WideRegAccept :=
  complete_congr _ (fun A _ _ => wideRegAccept_agree A)
      DescriptiveComplexity.wideRegAccept_NEXPTIME_complete

/--
---
conclusion: Lax822549.WideMachinesComplete.wideAcceptSpace_EXPSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem wideAcceptSpace_EXPSPACE_complete : EXPSPACE.Complete WideAcceptSpace :=
  complete_congr _ (fun A _ _ => wideAcceptSpace_agree A)
      DescriptiveComplexity.wideAcceptSpace_EXPSPACE_complete

/--
---
conclusion: Lax822549.WideMachinesComplete.dwideAcceptSpace_EXPSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem dwideAcceptSpace_EXPSPACE_complete : EXPSPACE.Complete DWideAcceptSpace :=
  complete_congr _ (fun A _ _ => dwideAcceptSpace_agree A)
      DescriptiveComplexity.dwideAcceptSpace_EXPSPACE_complete

/--
---
conclusion: Lax822549.WideMachinesComplete.wideAccept_nonvacuous
---
The library's two-element instance.
-/
theorem wideAccept_nonvacuous : ∃ (A : Type) (_ : wide.Structure A), Finite A ∧ WideAccept A :=
  ⟨Fin 2, inferInstance, inferInstance, (wideAccept_agree
      (Fin 2)).mp DescriptiveComplexity.wideAccept_nonvacuous⟩

/--
---
conclusion: Lax822549.WideMachinesComplete.wideAcceptSpace_nonvacuous
---
The library's two-element instance.
-/
theorem wideAcceptSpace_nonvacuous : ∃ (A : Type)
    (_ : wide.Structure A), Finite A ∧ WideAcceptSpace A :=
  ⟨Fin 2, inferInstance, inferInstance, (wideAcceptSpace_agree
      (Fin 2)).mp DescriptiveComplexity.wideAcceptSpace_nonvacuous⟩

/--
---
conclusion: Lax822549.WideMachinesComplete.dwideAcceptSpace_nonvacuous
---
The library's two-element instance.
-/
theorem dwideAcceptSpace_nonvacuous : ∃ (A : Type)
    (_ : wide.Structure A), Finite A ∧ DWideAcceptSpace A :=
  ⟨Fin 2, inferInstance, inferInstance, (dwideAcceptSpace_agree
      (Fin 2)).mp DescriptiveComplexity.dwideAcceptSpace_nonvacuous⟩

/--
---
conclusion: Lax822549.TilingsComplete.wideTiling_NEXPTIME_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem wideTiling_NEXPTIME_complete : NEXPTIME.Complete WideTiling :=
  complete_congr _ (fun A _ _ => wideTiling_agree A)
      DescriptiveComplexity.wideTiling_NEXPTIME_complete

/--
---
conclusion: Lax822549.TilingsComplete.wideCorridor_EXPSPACE_complete
---
The library's theorem, transported to the concept's problem along the
agreement.
-/
theorem wideCorridor_EXPSPACE_complete : EXPSPACE.Complete WideCorridor :=
  complete_congr _ (fun A _ _ => wideCorridor_agree A)
      DescriptiveComplexity.wideCorridor_EXPSPACE_complete

end Lax822549Proofs.Bridge
