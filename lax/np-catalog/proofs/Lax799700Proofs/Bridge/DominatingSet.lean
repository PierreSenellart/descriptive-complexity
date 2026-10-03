import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.DominatingSet
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.DominatingSet.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.DominatingSet.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.DominatingSet.Reduction
import Lax799700Proofs.Bridge.SetFamily

namespace Lax799700Proofs.Bridge.DominatingSet

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.DominatingSet

/--
---
conclusion: Lax799700.DominatingSet.hasSmallDominatingSet_iso
---
The library's invariance theorem for HasSmallDominatingSet.
-/
theorem hasSmallDominatingSet_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasSmallDominatingSet A ↔ HasSmallDominatingSet B :=
  DescriptiveComplexity.hasSmallDominatingSet_iso e

/--
---
conclusion: Lax799700.DominatingSet.dominatingSet_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem dominatingSet_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DominatingSet A ↔ HasSmallDominatingSet A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallDominatingSet_iso A

/-- The library's bundled DominatingSet and the catalog's agree on every structure. -/
theorem dominatingSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.DominatingSet A ↔ DominatingSet A :=
  (dominatingSet_iff A).symm

/--
---
conclusion: Lax799700.DominatingSet.dominatingSet_NP_complete
---
Membership from the library's existential second-order definition of
DominatingSet; hardness from the library's reduction out of SetCover, which is
NP-hard by the catalog’s statement for it. Both are transported to the
catalog's problems along the agreements.
-/
theorem dominatingSet_NP_complete : NP.Complete DominatingSet :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => dominatingSet_agree A).mp DescriptiveComplexity.dominatingSet_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.SetFamily.setCover_agree dominatingSet_agree DescriptiveComplexity.DomRed.setCover_fo_reduction_dominatingSet) Lax799700.SetFamily.setCover_NP_complete.2⟩

end Lax799700Proofs.Bridge.DominatingSet
