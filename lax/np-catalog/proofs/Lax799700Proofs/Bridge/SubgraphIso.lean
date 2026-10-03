import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.SubgraphIso
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.SubgraphIso
import Lax799700Proofs.Bridge.CliqueFamily

namespace Lax799700Proofs.Bridge.SubgraphIso

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.SubgraphIso

/--
---
conclusion: Lax799700.SubgraphIso.hasSubgraphIso_iso
---
The library's invariance theorem for HasSubgraphIso.
-/
theorem hasSubgraphIso_iso {A B : Type} [Lax799700.SubgraphIso.twoGraphs.Structure A] [Lax799700.SubgraphIso.twoGraphs.Structure B] (e : A ≃[Lax799700.SubgraphIso.twoGraphs] B) :
    HasSubgraphIso A ↔ HasSubgraphIso B :=
  DescriptiveComplexity.hasSubgraphIso_iso e

/--
---
conclusion: Lax799700.SubgraphIso.subgraphIso_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem subgraphIso_iff (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A] : SubgraphIso A ↔ HasSubgraphIso A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSubgraphIso_iso A

/-- The library's bundled SubgraphIso and the catalog's agree on every structure. -/
theorem subgraphIso_agree (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A] : DescriptiveComplexity.SubgraphIso A ↔ SubgraphIso A :=
  (subgraphIso_iff A).symm

/--
---
conclusion: Lax799700.SubgraphIso.subgraphIso_NP_complete
---
Membership from the library's existential second-order definition of
SubgraphIso; hardness from the library's reduction out of Clique, which is NP-
hard by the catalog’s statement for it. Both are transported to the catalog's
problems along the agreements.
-/
theorem subgraphIso_NP_complete : NP.Complete SubgraphIso :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => subgraphIso_agree A).mp DescriptiveComplexity.subgraphIso_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.clique_agree subgraphIso_agree DescriptiveComplexity.clique_fo_reduction_subgraphIso) Lax799700.CliqueFamily.clique_NP_complete.2⟩

end Lax799700Proofs.Bridge.SubgraphIso
