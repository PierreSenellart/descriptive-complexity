import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.SetFamily
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.FromGraphs
import Lax799700Proofs.Bridge.CliqueFamily
import Lax799700Proofs.DescriptiveComplexity.Problems.ExactCover
import Lax799700Proofs.Bridge.OneInSat
import Lax799700Proofs.DescriptiveComplexity.Problems.SetFamily.Reductions
import Lax799700Proofs.DescriptiveComplexity.Problems.SetSplitting
import Lax799700Proofs.Bridge.NaeSat

namespace Lax799700Proofs.Bridge.SetFamily

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.SetFamily

/--
---
conclusion: Lax799700.SetFamily.hasSmallSetCover_iso
---
The library's invariance theorem for HasSmallSetCover.
-/
theorem hasSmallSetCover_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B] (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    HasSmallSetCover A ↔ HasSmallSetCover B :=
  DescriptiveComplexity.hasSmallSetCover_iso e

/--
---
conclusion: Lax799700.SetFamily.setCover_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem setCover_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : SetCover A ↔ HasSmallSetCover A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallSetCover_iso A

/-- The library's bundled SetCover and the catalog's agree on every structure. -/
theorem setCover_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : DescriptiveComplexity.SetCover A ↔ SetCover A :=
  (setCover_iff A).symm

/--
---
conclusion: Lax799700.SetFamily.setCover_NP_complete
---
Membership from the library's existential second-order definition of SetCover; hardness from the library's reduction out of
VertexCover, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem setCover_NP_complete : NP.Complete SetCover :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => setCover_agree A).mp DescriptiveComplexity.setCover_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.vertexCover_agree setCover_agree DescriptiveComplexity.vertexCover_fo_reduction_setCover) Lax799700.CliqueFamily.vertexCover_NP_complete.2⟩

/--
---
conclusion: Lax799700.SetFamily.hasExactCover_iso
---
The library's invariance theorem for HasExactCover.
-/
theorem hasExactCover_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B] (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    HasExactCover A ↔ HasExactCover B :=
  DescriptiveComplexity.hasExactCover_iso e

/--
---
conclusion: Lax799700.SetFamily.exactCover_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem exactCover_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : ExactCover A ↔ HasExactCover A :=
  Common.ofPred_iff @DescriptiveComplexity.hasExactCover_iso A

/-- The library's bundled ExactCover and the catalog's agree on every structure. -/
theorem exactCover_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : DescriptiveComplexity.ExactCover A ↔ ExactCover A :=
  (exactCover_iff A).symm

/--
---
conclusion: Lax799700.SetFamily.exactCover_NP_complete
---
Membership from the library's existential second-order definition of ExactCover; hardness from the library's reduction out of
OneInSAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem exactCover_NP_complete : NP.Complete ExactCover :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => exactCover_agree A).mp DescriptiveComplexity.exactCover_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.OneInSat.oneInSat_agree exactCover_agree DescriptiveComplexity.oneInSat_fo_reduction_exactCover) Lax799700.OneInSat.oneInSat_NP_complete.2⟩

/--
---
conclusion: Lax799700.SetFamily.hasSmallHittingSet_iso
---
The library's invariance theorem for HasSmallHittingSet.
-/
theorem hasSmallHittingSet_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B] (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    HasSmallHittingSet A ↔ HasSmallHittingSet B :=
  DescriptiveComplexity.hasSmallHittingSet_iso e

/--
---
conclusion: Lax799700.SetFamily.hittingSet_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem hittingSet_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : HittingSet A ↔ HasSmallHittingSet A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallHittingSet_iso A

/-- The library's bundled HittingSet and the catalog's agree on every structure. -/
theorem hittingSet_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : DescriptiveComplexity.HittingSet A ↔ HittingSet A :=
  (hittingSet_iff A).symm

/--
---
conclusion: Lax799700.SetFamily.hittingSet_NP_complete
---
Membership from the library's reduction of HittingSet to SetCover, which is in NP; hardness from the library's reduction out of
SetCover, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem hittingSet_NP_complete : NP.Complete HittingSet :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr hittingSet_agree Lax799700Proofs.Bridge.SetFamily.setCover_agree DescriptiveComplexity.hittingSet_fo_reduction_setCover) Lax799700.SetFamily.setCover_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.SetFamily.setCover_agree hittingSet_agree DescriptiveComplexity.setCover_fo_reduction_hittingSet) Lax799700.SetFamily.setCover_NP_complete.2⟩

/--
---
conclusion: Lax799700.SetFamily.hasLargeSetPacking_iso
---
The library's invariance theorem for HasLargeSetPacking.
-/
theorem hasLargeSetPacking_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B] (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    HasLargeSetPacking A ↔ HasLargeSetPacking B :=
  DescriptiveComplexity.hasLargeSetPacking_iso e

/--
---
conclusion: Lax799700.SetFamily.setPacking_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem setPacking_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : SetPacking A ↔ HasLargeSetPacking A :=
  Common.ofPred_iff @DescriptiveComplexity.hasLargeSetPacking_iso A

/-- The library's bundled SetPacking and the catalog's agree on every structure. -/
theorem setPacking_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : DescriptiveComplexity.SetPacking A ↔ SetPacking A :=
  (setPacking_iff A).symm

/--
---
conclusion: Lax799700.SetFamily.setPacking_NP_complete
---
Membership from the library's existential second-order definition of SetPacking; hardness from the library's reduction out of
IndependentSet, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem setPacking_NP_complete : NP.Complete SetPacking :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => setPacking_agree A).mp DescriptiveComplexity.setPacking_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.indSet_agree setPacking_agree DescriptiveComplexity.indSet_fo_reduction_setPacking) Lax799700.CliqueFamily.indSet_NP_complete.2⟩

/--
---
conclusion: Lax799700.SetFamily.hasSetSplitting_iso
---
The library's invariance theorem for HasSetSplitting.
-/
theorem hasSetSplitting_iso {A B : Type} [Lax799700.SetFamily.setSystem.Structure A] [Lax799700.SetFamily.setSystem.Structure B] (e : A ≃[Lax799700.SetFamily.setSystem] B) :
    HasSetSplitting A ↔ HasSetSplitting B :=
  DescriptiveComplexity.hasSetSplitting_iso e

/--
---
conclusion: Lax799700.SetFamily.setSplitting_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem setSplitting_iff (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : SetSplitting A ↔ HasSetSplitting A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSetSplitting_iso A

/-- The library's bundled SetSplitting and the catalog's agree on every structure. -/
theorem setSplitting_agree (A : Type) [Lax799700.SetFamily.setSystem.Structure A] : DescriptiveComplexity.SetSplitting A ↔ SetSplitting A :=
  (setSplitting_iff A).symm

/--
---
conclusion: Lax799700.SetFamily.setSplitting_NP_complete
---
Membership from the library's existential second-order definition of SetSplitting; hardness from the library's reduction out of
NAESAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem setSplitting_NP_complete : NP.Complete SetSplitting :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => setSplitting_agree A).mp DescriptiveComplexity.setSplitting_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.NaeSat.naeSat_agree setSplitting_agree DescriptiveComplexity.naeSat_fo_reduction_setSplitting) Lax799700.NaeSat.naeSat_NP_complete.2⟩

end Lax799700Proofs.Bridge.SetFamily
