import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.OneInSat
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.OneInSat.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.OneInSat.Reduction
import Lax799700Proofs.Bridge.ThreeSat

namespace Lax799700Proofs.Bridge.OneInSat

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.OneInSat

/--
---
conclusion: Lax799700.OneInSat.oneInSatisfiable_iso
---
The library's invariance theorem for OneInSatisfiable.
-/
theorem oneInSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    OneInSatisfiable A ↔ OneInSatisfiable B :=
  DescriptiveComplexity.oneInSatisfiable_iso e

/--
---
conclusion: Lax799700.OneInSat.oneInSat_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem oneInSat_iff (A : Type) [Lax904597.Sat.sat.Structure A] : OneInSAT A ↔ OneInSatisfiable A :=
  Common.ofPred_iff @DescriptiveComplexity.oneInSatisfiable_iso A

/-- The library's bundled OneInSAT and the catalog's agree on every structure. -/
theorem oneInSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] : DescriptiveComplexity.OneInSAT A ↔ OneInSAT A :=
  (oneInSat_iff A).symm

/--
---
conclusion: Lax799700.OneInSat.oneInSat_NP_complete
---
Membership from the library's existential second-order definition of OneInSAT; hardness from the library's reduction out of
ThreeSAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem oneInSat_NP_complete : NP.Complete OneInSAT :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => oneInSat_agree A).mp DescriptiveComplexity.oneInSat_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.ThreeSat.threeSat_agree oneInSat_agree DescriptiveComplexity.OneInRed.threeSat_ordered_fo_reduction_oneInSat) Lax799700.ThreeSat.threeSat_NP_complete.2⟩

end Lax799700Proofs.Bridge.OneInSat
