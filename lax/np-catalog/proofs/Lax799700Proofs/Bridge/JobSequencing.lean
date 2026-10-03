import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.JobSequencing
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.JobSequencing.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.JobSequencing.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.JobSequencing.Hardness
import Lax799700Proofs.Bridge.NaeThreeSat

namespace Lax799700Proofs.Bridge.JobSequencing

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.JobSequencing

/--
---
conclusion: Lax799700.JobSequencing.hasGoodSchedule_iso
---
The library's invariance theorem for HasGoodSchedule.
-/
theorem hasGoodSchedule_iso {A B : Type} [Lax799700.JobSequencing.jobSeq.Structure A] [Lax799700.JobSequencing.jobSeq.Structure B] (e : A ≃[Lax799700.JobSequencing.jobSeq] B) :
    HasGoodSchedule A ↔ HasGoodSchedule B :=
  DescriptiveComplexity.hasGoodSchedule_iso e

/--
---
conclusion: Lax799700.JobSequencing.jobSequencing_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem jobSequencing_iff (A : Type) [Lax799700.JobSequencing.jobSeq.Structure A] : JobSequencing A ↔ HasGoodSchedule A :=
  Common.ofPred_iff @DescriptiveComplexity.hasGoodSchedule_iso A

/-- The library's bundled JobSequencing and the catalog's agree on every structure. -/
theorem jobSequencing_agree (A : Type) [Lax799700.JobSequencing.jobSeq.Structure A] : DescriptiveComplexity.JobSequencing A ↔ JobSequencing A :=
  (jobSequencing_iff A).symm

/--
---
conclusion: Lax799700.JobSequencing.jobSequencing_NP_complete
---
Membership from the library's existential second-order definition of JobSequencing; hardness from the library's reduction out of
NAE3SAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem jobSequencing_NP_complete : NP.Complete JobSequencing :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => jobSequencing_agree A).mp DescriptiveComplexity.jobSequencing_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.NaeThreeSat.nae3Sat_agree jobSequencing_agree DescriptiveComplexity.nae3Sat_ordered_fo_reduction_jobSequencing) Lax799700.NaeThreeSat.nae3Sat_NP_complete.2⟩

end Lax799700Proofs.Bridge.JobSequencing
