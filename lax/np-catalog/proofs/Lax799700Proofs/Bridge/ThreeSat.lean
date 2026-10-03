import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.ThreeSat
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeSat.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeSat.ToSat
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeSat.FromSat

namespace Lax799700Proofs.Bridge.ThreeSat

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.ThreeSat

/--
---
conclusion: Lax799700.ThreeSat.threeSatisfiable_iso
---
The library's invariance theorem for ThreeSatisfiable.
-/
theorem threeSatisfiable_iso {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B] (e : A ≃[Lax904597.Sat.sat] B) :
    ThreeSatisfiable A ↔ ThreeSatisfiable B :=
  DescriptiveComplexity.threeSatisfiable_iso e

/--
---
conclusion: Lax799700.ThreeSat.threeSat_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem threeSat_iff (A : Type) [Lax904597.Sat.sat.Structure A] : ThreeSAT A ↔ ThreeSatisfiable A :=
  Common.ofPred_iff @DescriptiveComplexity.threeSatisfiable_iso A

/-- The library's bundled ThreeSAT and the catalog's agree on every structure. -/
theorem threeSat_agree (A : Type) [Lax904597.Sat.sat.Structure A] : DescriptiveComplexity.ThreeSAT A ↔ ThreeSAT A :=
  (threeSat_iff A).symm

/--
---
conclusion: Lax799700.ThreeSat.threeSat_NP_complete
---
Membership from the library's reduction of ThreeSAT to SAT, which is in NP; hardness from the library's reduction out of
SAT, which is NP-hard by the
NP core's Cook–Levin theorem. Both are
transported to the catalog's problems along the agreements.
-/
theorem threeSat_NP_complete : NP.Complete ThreeSAT :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr threeSat_agree (fun _ _ => Iff.rfl) DescriptiveComplexity.threeSat_fo_reduction_sat) Lax904597.CookLevin.SAT_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr (fun _ _ => Iff.rfl) threeSat_agree DescriptiveComplexity.sat_ordered_fo_reduction_threeSat) Lax904597.CookLevin.SAT_NP_complete.2⟩

end Lax799700Proofs.Bridge.ThreeSat
