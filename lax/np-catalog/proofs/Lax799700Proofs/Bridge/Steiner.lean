import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Steiner
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Steiner.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Steiner.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Steiner.Reductions
import Lax799700Proofs.Bridge.CliqueFamily

namespace Lax799700Proofs.Bridge.Steiner

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Steiner

/--
---
conclusion: Lax799700.Steiner.hasSmallEdgeSteinerTree_iso
---
The library's invariance theorem for HasSmallEdgeSteinerTree.
-/
theorem hasSmallEdgeSteinerTree_iso {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A] [Lax799700.Steiner.steinerGraph.Structure B] (e : A ≃[Lax799700.Steiner.steinerGraph] B) :
    HasSmallEdgeSteinerTree A ↔ HasSmallEdgeSteinerTree B :=
  DescriptiveComplexity.hasSmallEdgeSteinerTree_iso e

/--
---
conclusion: Lax799700.Steiner.edgeSteinerTree_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem edgeSteinerTree_iff (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] : EdgeSteinerTree A ↔ HasSmallEdgeSteinerTree A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallEdgeSteinerTree_iso A

/-- The library's bundled EdgeSteinerTree and the catalog's agree on every structure. -/
theorem edgeSteinerTree_agree (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] : DescriptiveComplexity.EdgeSteinerTree A ↔ EdgeSteinerTree A :=
  (edgeSteinerTree_iff A).symm

/--
---
conclusion: Lax799700.Steiner.edgeSteinerTree_NP_complete
---
Membership from the library's existential second-order definition of EdgeSteinerTree; hardness from the library's reduction out of
VertexCover, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem edgeSteinerTree_NP_complete : NP.Complete EdgeSteinerTree :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => edgeSteinerTree_agree A).mp DescriptiveComplexity.edgeSteinerTree_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.vertexCover_agree edgeSteinerTree_agree DescriptiveComplexity.vertexCover_ordered_fo_reduction_edgeSteinerTree) Lax799700.CliqueFamily.vertexCover_NP_complete.2⟩

/--
---
conclusion: Lax799700.Steiner.hasSmallSteinerTree_iso
---
The library's invariance theorem for HasSmallSteinerTree.
-/
theorem hasSmallSteinerTree_iso {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A] [Lax799700.Steiner.steinerGraph.Structure B] (e : A ≃[Lax799700.Steiner.steinerGraph] B) :
    HasSmallSteinerTree A ↔ HasSmallSteinerTree B :=
  DescriptiveComplexity.hasSmallSteinerTree_iso e

/--
---
conclusion: Lax799700.Steiner.steinerTree_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem steinerTree_iff (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] : SteinerTree A ↔ HasSmallSteinerTree A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallSteinerTree_iso A

/-- The library's bundled SteinerTree and the catalog's agree on every structure. -/
theorem steinerTree_agree (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] : DescriptiveComplexity.SteinerTree A ↔ SteinerTree A :=
  (steinerTree_iff A).symm

/--
---
conclusion: Lax799700.Steiner.steinerTree_NP_complete
---
Membership from the library's existential second-order definition of SteinerTree; hardness from the library's reduction out of
VertexCover, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem steinerTree_NP_complete : NP.Complete SteinerTree :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => steinerTree_agree A).mp DescriptiveComplexity.steinerTree_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.vertexCover_agree steinerTree_agree DescriptiveComplexity.vertexCover_ordered_fo_reduction_steinerTree) Lax799700.CliqueFamily.vertexCover_NP_complete.2⟩

end Lax799700Proofs.Bridge.Steiner
