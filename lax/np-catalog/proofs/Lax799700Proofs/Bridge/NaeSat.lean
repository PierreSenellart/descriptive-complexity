import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.NaeSat
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.NaeSat

namespace Lax799700Proofs.Bridge.NaeSat

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.NaeSat

/--
---
conclusion: Lax799700.NaeSat.naeSatisfiable_iso
---
The library's invariance theorem for NAESatisfiable.
-/
theorem naeSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    NAESatisfiable A ↔ NAESatisfiable B :=
  DescriptiveComplexity.naeSatisfiable_iso e

/--
---
conclusion: Lax799700.NaeSat.naeSat_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem naeSat_iff (A : Type) [Lax904597.Sat.sat.Structure A] : NAESAT A ↔ NAESatisfiable A :=
  Common.ofPred_iff @DescriptiveComplexity.naeSatisfiable_iso A

/-- The library's bundled NAESAT and the catalog's agree on every structure. -/
theorem naeSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] : DescriptiveComplexity.NAESAT A ↔ NAESAT A :=
  (naeSat_iff A).symm

/--
---
conclusion: Lax799700.NaeSat.naeSat_NP_complete
---
Membership from the library's existential second-order definition of NAESAT; hardness from the library's reduction out of
SAT, which is NP-hard by the
NP core's Cook–Levin theorem. Both are
transported to the catalog's problems along the agreements.
-/
theorem naeSat_NP_complete : NP.Complete NAESAT :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => naeSat_agree A).mp DescriptiveComplexity.naeSat_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr (fun _ _ => Iff.rfl) naeSat_agree DescriptiveComplexity.sat_ordered_fo_reduction_naeSat) Lax904597.CookLevin.SAT_NP_complete.2⟩

end Lax799700Proofs.Bridge.NaeSat
