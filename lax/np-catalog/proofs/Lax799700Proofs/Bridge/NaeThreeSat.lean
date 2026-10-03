import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.NaeThreeSat
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.NaeThreeSat
import Lax799700Proofs.Bridge.NaeSat

namespace Lax799700Proofs.Bridge.NaeThreeSat

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.NaeThreeSat

/--
---
conclusion: Lax799700.NaeThreeSat.naeThreeSatisfiable_iso
---
The library's invariance theorem for NAEThreeSatisfiable.
-/
theorem naeThreeSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    NAEThreeSatisfiable A ↔ NAEThreeSatisfiable B :=
  DescriptiveComplexity.naeThreeSatisfiable_iso e

/--
---
conclusion: Lax799700.NaeThreeSat.nae3Sat_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem nae3Sat_iff (A : Type) [Lax904597.Sat.sat.Structure A] : NAE3SAT A ↔ NAEThreeSatisfiable A :=
  Common.ofPred_iff @DescriptiveComplexity.naeThreeSatisfiable_iso A

/-- The library's bundled NAE3SAT and the catalog's agree on every structure. -/
theorem nae3Sat_agree (A : Type) [Lax904597.Sat.sat.Structure A] : DescriptiveComplexity.NAE3SAT A ↔ NAE3SAT A :=
  (nae3Sat_iff A).symm

/--
---
conclusion: Lax799700.NaeThreeSat.nae3Sat_NP_complete
---
Membership from the library's reduction of NAE3SAT to NAESAT, which is in NP; hardness from the library's reduction out of
NAESAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem nae3Sat_NP_complete : NP.Complete NAE3SAT :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr nae3Sat_agree Lax799700Proofs.Bridge.NaeSat.naeSat_agree DescriptiveComplexity.nae3Sat_fo_reduction_naeSat) Lax799700.NaeSat.naeSat_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.NaeSat.naeSat_agree nae3Sat_agree DescriptiveComplexity.naeSat_ordered_fo_reduction_nae3Sat) Lax799700.NaeSat.naeSat_NP_complete.2⟩

end Lax799700Proofs.Bridge.NaeThreeSat
