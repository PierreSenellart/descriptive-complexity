import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.CliqueFamily
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.FromSat
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Reductions

namespace Lax799700Proofs.Bridge.CliqueFamily

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.CliqueFamily

/--
---
conclusion: Lax799700.CliqueFamily.hasLargeClique_iso
---
The library's invariance theorem for HasLargeClique.
-/
theorem hasLargeClique_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasLargeClique A ↔ HasLargeClique B :=
  DescriptiveComplexity.hasLargeClique_iso e

/--
---
conclusion: Lax799700.CliqueFamily.clique_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem clique_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : Clique A ↔ HasLargeClique A :=
  Common.ofPred_iff @DescriptiveComplexity.hasLargeClique_iso A

/-- The library's bundled Clique and the catalog's agree on every structure. -/
theorem clique_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.Clique A ↔ Clique A :=
  (clique_iff A).symm

/--
---
conclusion: Lax799700.CliqueFamily.clique_NP_complete
---
Membership from the library's existential second-order definition of Clique; hardness from the library's reduction out of
SAT, which is NP-hard by the
NP core's Cook–Levin theorem. Both are
transported to the catalog's problems along the agreements.
-/
theorem clique_NP_complete : NP.Complete Clique :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => clique_agree A).mp DescriptiveComplexity.clique_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr (fun _ _ => Iff.rfl) clique_agree DescriptiveComplexity.sat_ordered_fo_reduction_clique) Lax904597.CookLevin.SAT_NP_complete.2⟩

/--
---
conclusion: Lax799700.CliqueFamily.hasLargeIndependentSet_iso
---
The library's invariance theorem for HasLargeIndependentSet.
-/
theorem hasLargeIndependentSet_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasLargeIndependentSet A ↔ HasLargeIndependentSet B :=
  DescriptiveComplexity.hasLargeIndependentSet_iso e

/--
---
conclusion: Lax799700.CliqueFamily.indSet_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem indSet_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : IndependentSet A ↔ HasLargeIndependentSet A :=
  Common.ofPred_iff @DescriptiveComplexity.hasLargeIndependentSet_iso A

/-- The library's bundled IndependentSet and the catalog's agree on every structure. -/
theorem indSet_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.IndependentSet A ↔ IndependentSet A :=
  (indSet_iff A).symm

/--
---
conclusion: Lax799700.CliqueFamily.indSet_NP_complete
---
Membership from the library's reduction of IndependentSet to Clique, which is in NP; hardness from the library's reduction out of
Clique, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem indSet_NP_complete : NP.Complete IndependentSet :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr indSet_agree Lax799700Proofs.Bridge.CliqueFamily.clique_agree DescriptiveComplexity.indSet_fo_reduction_clique) Lax799700.CliqueFamily.clique_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.clique_agree indSet_agree DescriptiveComplexity.clique_fo_reduction_indSet) Lax799700.CliqueFamily.clique_NP_complete.2⟩

/--
---
conclusion: Lax799700.CliqueFamily.hasSmallVertexCover_iso
---
The library's invariance theorem for HasSmallVertexCover.
-/
theorem hasSmallVertexCover_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasSmallVertexCover A ↔ HasSmallVertexCover B :=
  DescriptiveComplexity.hasSmallVertexCover_iso e

/--
---
conclusion: Lax799700.CliqueFamily.vertexCover_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem vertexCover_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : VertexCover A ↔ HasSmallVertexCover A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallVertexCover_iso A

/-- The library's bundled VertexCover and the catalog's agree on every structure. -/
theorem vertexCover_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.VertexCover A ↔ VertexCover A :=
  (vertexCover_iff A).symm

/--
---
conclusion: Lax799700.CliqueFamily.vertexCover_NP_complete
---
Membership from the library's reduction of VertexCover to IndependentSet, which is in NP; hardness from the library's reduction out of
IndependentSet, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem vertexCover_NP_complete : NP.Complete VertexCover :=
  ⟨Lax904597.NPClass.NP_mem_of_foReduction
      (Common.FOReduction.congr vertexCover_agree Lax799700Proofs.Bridge.CliqueFamily.indSet_agree DescriptiveComplexity.vertexCover_fo_reduction_indSet) Lax799700.CliqueFamily.indSet_NP_complete.1,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.indSet_agree vertexCover_agree DescriptiveComplexity.indSet_fo_reduction_vertexCover) Lax799700.CliqueFamily.indSet_NP_complete.2⟩

end Lax799700Proofs.Bridge.CliqueFamily
