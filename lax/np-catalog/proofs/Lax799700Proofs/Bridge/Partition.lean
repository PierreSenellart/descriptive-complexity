import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Partition
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Partition.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Partition.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Partition.Hardness
import Lax799700Proofs.Bridge.NaeSat

namespace Lax799700Proofs.Bridge.Partition

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Partition

/--
---
conclusion: Lax799700.Partition.hasEqualSplit_iso
---
The library's invariance theorem for HasEqualSplit.
-/
theorem hasEqualSplit_iso {A B : Type} [Lax799700.Knapsack.binWeights.Structure A] [Lax799700.Knapsack.binWeights.Structure B] (e : A ≃[Lax799700.Knapsack.binWeights] B) :
    HasEqualSplit A ↔ HasEqualSplit B :=
  DescriptiveComplexity.hasEqualSplit_iso e

/--
---
conclusion: Lax799700.Partition.partition_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem partition_iff (A : Type) [Lax799700.Knapsack.binWeights.Structure A] : Partition A ↔ HasEqualSplit A :=
  Common.ofPred_iff @DescriptiveComplexity.hasEqualSplit_iso A

/-- The library's bundled Partition and the catalog's agree on every structure. -/
theorem partition_agree (A : Type) [Lax799700.Knapsack.binWeights.Structure A] : DescriptiveComplexity.Partition A ↔ Partition A :=
  (partition_iff A).symm

/--
---
conclusion: Lax799700.Partition.partition_NP_complete
---
Membership from the library's existential second-order definition of Partition; hardness from the library's reduction out of
NAESAT, which is NP-hard by the
catalog's statement for it. Both are
transported to the catalog's problems along the agreements.
-/
theorem partition_NP_complete : NP.Complete Partition :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => partition_agree A).mp DescriptiveComplexity.partition_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.NaeSat.naeSat_agree partition_agree DescriptiveComplexity.naeSat_ordered_fo_reduction_partition) Lax799700.NaeSat.naeSat_NP_complete.2⟩

end Lax799700Proofs.Bridge.Partition
