import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.ThreeColorability
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability.ToSat
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability.FromSat

namespace Lax799700Proofs.Bridge.ThreeColorability

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.ThreeColorability

/--
---
conclusion: Lax799700.ThreeColorability.threeColorable_iso
---
The library's invariance theorem for ThreeColorable.
-/
theorem threeColorable_iso {A B : Type} [FirstOrder.Language.graph.Structure A] [FirstOrder.Language.graph.Structure B] (e : A ≃[FirstOrder.Language.graph] B) :
    ThreeColorable A ↔ ThreeColorable B :=
  DescriptiveComplexity.threeColorable_iso e

/--
---
conclusion: Lax799700.ThreeColorability.threeCol_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem threeCol_iff (A : Type) [FirstOrder.Language.graph.Structure A] : ThreeCol A ↔ ThreeColorable A :=
  Common.ofPred_iff @DescriptiveComplexity.threeColorable_iso A

/-- The library's bundled ThreeCol and the catalog's agree on every structure. -/
theorem threeCol_agree (A : Type) [FirstOrder.Language.graph.Structure A] : DescriptiveComplexity.ThreeCol A ↔ ThreeCol A :=
  (threeCol_iff A).symm

/--
---
conclusion: Lax799700.ThreeColorability.threeCol_NP_complete
---
Membership from the library's reduction of ThreeCol to SAT, which is in NP; hardness from the library's reduction out of
SAT, which is NP-hard by the
NP core's Cook–Levin theorem. Both are
transported to the catalog's problems along the agreements.
-/
theorem threeCol_NP_complete : NP.Complete ThreeCol :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr threeCol_agree (fun _ _ => Iff.rfl) DescriptiveComplexity.threeCol_fo_reduction_sat) Lax904597.CookLevin.SAT_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr (fun _ _ => Iff.rfl) threeCol_agree DescriptiveComplexity.sat_ordered_fo_reduction_threeCol) Lax904597.CookLevin.SAT_NP_complete.2⟩

end Lax799700Proofs.Bridge.ThreeColorability
