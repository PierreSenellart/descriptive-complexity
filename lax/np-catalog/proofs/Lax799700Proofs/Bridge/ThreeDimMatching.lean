import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.ThreeDimMatching
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeDimMatching.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeDimMatching.Hardness

namespace Lax799700Proofs.Bridge.ThreeDimMatching

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.ThreeDimMatching

/--
---
conclusion: Lax799700.ThreeDimMatching.hasThreeDimMatching_iso
---
The library's invariance theorem for HasThreeDimMatching.
-/
theorem hasThreeDimMatching_iso {A B : Type} [Lax799700.ThreeDimMatching.tripleSys.Structure A] [Lax799700.ThreeDimMatching.tripleSys.Structure B] (e : A ≃[Lax799700.ThreeDimMatching.tripleSys] B) :
    HasThreeDimMatching A ↔ HasThreeDimMatching B :=
  DescriptiveComplexity.hasThreeDimMatching_iso e

/--
---
conclusion: Lax799700.ThreeDimMatching.threeDimMatching_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem threeDimMatching_iff (A : Type) [Lax799700.ThreeDimMatching.tripleSys.Structure A] : ThreeDimMatching A ↔ HasThreeDimMatching A :=
  Common.ofPred_iff @DescriptiveComplexity.hasThreeDimMatching_iso A

/-- The library's bundled ThreeDimMatching and the catalog's agree on every structure. -/
theorem threeDimMatching_agree (A : Type) [Lax799700.ThreeDimMatching.tripleSys.Structure A] : DescriptiveComplexity.ThreeDimMatching A ↔ ThreeDimMatching A :=
  (threeDimMatching_iff A).symm

/--
---
conclusion: Lax799700.ThreeDimMatching.threeDimMatching_NP_complete
---
Membership from the library's existential second-order definition of ThreeDimMatching; hardness from the library's reduction out of
SAT, which is NP-hard by the
NP core's Cook–Levin theorem. Both are
transported to the catalog's problems along the agreements.
-/
theorem threeDimMatching_NP_complete : NP.Complete ThreeDimMatching :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => threeDimMatching_agree A).mp DescriptiveComplexity.threeDimMatching_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr (fun _ _ => Iff.rfl) threeDimMatching_agree DescriptiveComplexity.sat_ordered_fo_reduction_threeDimMatching) Lax904597.CookLevin.SAT_NP_complete.2⟩

end Lax799700Proofs.Bridge.ThreeDimMatching
