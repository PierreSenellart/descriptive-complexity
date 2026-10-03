import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Knapsack
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Knapsack.Hardness
import Lax799700Proofs.Bridge.SetFamily

namespace Lax799700Proofs.Bridge.Knapsack

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Knapsack

/--
---
conclusion: Lax799700.Knapsack.hasSubsetSum_iso
---
The library's invariance theorem for HasSubsetSum.
-/
theorem hasSubsetSum_iso {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B] (e : A ≃[Lax799700.Knapsack.binWeights] B) :
    HasSubsetSum A ↔ HasSubsetSum B :=
  DescriptiveComplexity.hasSubsetSum_iso e

/--
---
conclusion: Lax799700.Knapsack.knapsack_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem knapsack_iff (A : Type) [Lax799700.Knapsack.binWeights.Structure A] : Knapsack A ↔ HasSubsetSum A :=
  Common.ofPred_iff @DescriptiveComplexity.hasSubsetSum_iso A

/-- The library's bundled Knapsack and the catalog's agree on every structure. -/
theorem knapsack_agree (A : Type) [Lax799700.Knapsack.binWeights.Structure A] : DescriptiveComplexity.Knapsack A ↔ Knapsack A :=
  (knapsack_iff A).symm

/--
---
conclusion: Lax799700.Knapsack.knapsack_NP_complete
---
Membership from the library's existential second-order definition of Knapsack;
hardness from the library's reduction out of ExactCover, which is NP-hard by
the catalog’s statement for it. Both are transported to the catalog's problems
along the agreements.
-/
theorem knapsack_NP_complete : NP.Complete Knapsack :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => knapsack_agree A).mp DescriptiveComplexity.knapsack_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.SetFamily.exactCover_agree knapsack_agree DescriptiveComplexity.exactCover_ordered_fo_reduction_knapsack) Lax799700.SetFamily.exactCover_NP_complete.2⟩

end Lax799700Proofs.Bridge.Knapsack
