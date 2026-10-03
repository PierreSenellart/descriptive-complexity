import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.MaxCut
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.MaxCut.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.MaxCut.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.MaxCut.Reduction
import Lax799700Proofs.Bridge.NaeThreeSat

namespace Lax799700Proofs.Bridge.MaxCut

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.MaxCut

/--
---
conclusion: Lax799700.MaxCut.hasLargeCut_iso
---
The library's invariance theorem for HasLargeCut.
-/
theorem hasLargeCut_iso {A B : Type} [Lax799700.Feedback.markedArcGraph.Structure A] [Lax799700.Feedback.markedArcGraph.Structure B] (e : A ≃[Lax799700.Feedback.markedArcGraph] B) :
    HasLargeCut A ↔ HasLargeCut B :=
  DescriptiveComplexity.hasLargeCut_iso e

/--
---
conclusion: Lax799700.MaxCut.maxCut_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem maxCut_iff (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] : MaxCut A ↔ HasLargeCut A :=
  Common.ofPred_iff @DescriptiveComplexity.hasLargeCut_iso A

/-- The library's bundled MaxCut and the catalog's agree on every structure. -/
theorem maxCut_agree (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A] : DescriptiveComplexity.MaxCut A ↔ MaxCut A :=
  (maxCut_iff A).symm

/--
---
conclusion: Lax799700.MaxCut.maxCut_NP_complete
---
Membership from the library's existential second-order definition of MaxCut;
hardness from the library's reduction out of NAE3SAT, which is NP-hard by the
catalog’s statement for it. Both are transported to the catalog's problems
along the agreements.
-/
theorem maxCut_NP_complete : NP.Complete MaxCut :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => maxCut_agree A).mp DescriptiveComplexity.maxCut_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.NaeThreeSat.nae3Sat_agree maxCut_agree DescriptiveComplexity.MaxCutRed.nae3Sat_ordered_fo_reduction_maxCut) Lax799700.NaeThreeSat.nae3Sat_NP_complete.2⟩

end Lax799700Proofs.Bridge.MaxCut
