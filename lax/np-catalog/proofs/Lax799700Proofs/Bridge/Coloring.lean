import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Coloring
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Coloring.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Coloring.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Coloring.Reductions
import Lax799700Proofs.Bridge.ThreeColorability

namespace Lax799700Proofs.Bridge.Coloring

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Coloring

/--
---
conclusion: Lax799700.Coloring.hasSmallChromaticNumber_iso
---
The library's invariance theorem for HasSmallChromaticNumber.
-/
theorem hasSmallChromaticNumber_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasSmallChromaticNumber A ↔ HasSmallChromaticNumber B :=
  DescriptiveComplexity.hasSmallChromaticNumber_iso e

/--
---
conclusion: Lax799700.Coloring.chromaticNumber_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem chromaticNumber_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : ChromaticNumber A ↔ HasSmallChromaticNumber A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallChromaticNumber_iso A

/-- The library's bundled ChromaticNumber and the catalog's agree on every structure. -/
theorem chromaticNumber_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.ChromaticNumber A ↔ ChromaticNumber A :=
  (chromaticNumber_iff A).symm

/--
---
conclusion: Lax799700.Coloring.chromaticNumber_NP_complete
---
Membership from the library's existential second-order definition of
ChromaticNumber; hardness from the library's reduction out of ThreeCol, which
is NP-hard by the catalog’s statement for it. Both are transported to the
catalog's problems along the agreements.
-/
theorem chromaticNumber_NP_complete : NP.Complete ChromaticNumber :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => chromaticNumber_agree A).mp DescriptiveComplexity.chromaticNumber_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.ThreeColorability.threeCol_agree chromaticNumber_agree DescriptiveComplexity.threeCol_ordered_fo_reduction_chromaticNumber) Lax799700.ThreeColorability.threeCol_NP_complete.2⟩

/--
---
conclusion: Lax799700.Coloring.hasSmallCliqueCover_iso
---
The library's invariance theorem for HasSmallCliqueCover.
-/
theorem hasSmallCliqueCover_iso {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B] (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    HasSmallCliqueCover A ↔ HasSmallCliqueCover B :=
  DescriptiveComplexity.hasSmallCliqueCover_iso e

/--
---
conclusion: Lax799700.Coloring.cliqueCover_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem cliqueCover_iff (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : CliqueCover A ↔ HasSmallCliqueCover A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSmallCliqueCover_iso A

/-- The library's bundled CliqueCover and the catalog's agree on every structure. -/
theorem cliqueCover_agree (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] : DescriptiveComplexity.CliqueCover A ↔ CliqueCover A :=
  (cliqueCover_iff A).symm

/--
---
conclusion: Lax799700.Coloring.cliqueCover_NP_complete
---
Membership from the library's existential second-order definition of
CliqueCover; hardness from the library's reduction out of ChromaticNumber,
which is NP-hard by the catalog’s statement for it. Both are transported to
the catalog's problems along the agreements.
-/
theorem cliqueCover_NP_complete : NP.Complete CliqueCover :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => cliqueCover_agree A).mp DescriptiveComplexity.cliqueCover_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.Coloring.chromaticNumber_agree cliqueCover_agree DescriptiveComplexity.chromaticNumber_fo_reduction_cliqueCover) Lax799700.Coloring.chromaticNumber_NP_complete.2⟩

/--
---
conclusion: Lax799700.Coloring.kColorable_iso
---
The library's invariance theorem for KColorable.
-/
theorem kColorable_iso {k : ℕ} {A B : Type} [FirstOrder.Language.graph.Structure A]
    [FirstOrder.Language.graph.Structure B] (e : A ≃[FirstOrder.Language.graph] B) :
    KColorable k A ↔ KColorable k B :=
  DescriptiveComplexity.kColorable_iso e

/--
---
conclusion: Lax799700.Coloring.kCol_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem kCol_iff (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A] :
    KCol k A ↔ KColorable k A :=
  Common.ofPred_iff (fun e => DescriptiveComplexity.kColorable_iso e) A

/-- The library's bundled `KCol k` and the catalog's agree on every structure. -/
theorem kCol_agree (k : ℕ) (A : Type) [FirstOrder.Language.graph.Structure A] :
    DescriptiveComplexity.KCol k A ↔ KCol k A :=
  (kCol_iff k A).symm

/--
---
conclusion: Lax799700.Coloring.kCol_NP_complete
---
Membership from the library's existential second-order definition of
$k$-colorability; hardness by padding the reduction of 3-colorability to
$k$-colorability with $k - 3$ further colors, 3-colorability being NP-hard by
the catalog's statement for it.
-/
theorem kCol_NP_complete {k : ℕ} (hk : 3 ≤ k) : NP.Complete (KCol k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := ⟨k - 3, by omega⟩
  exact ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => kCol_agree (3 + m) A).mp
      (DescriptiveComplexity.kCol_sigmaSODefinable (3 + m)),
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.ThreeColorability.threeCol_agree (kCol_agree (3 + m))
        (DescriptiveComplexity.threeCol_fo_reduction_kCol m))
      Lax799700.ThreeColorability.threeCol_NP_complete.2⟩

end Lax799700Proofs.Bridge.Coloring
