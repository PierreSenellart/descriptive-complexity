import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.ZeroOneIP
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.ZeroOneIP.Hardness
import Lax799700Proofs.Bridge.Knapsack

namespace Lax799700Proofs.Bridge.ZeroOneIP

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.ZeroOneIP

/--
---
conclusion: Lax799700.ZeroOneIP.hasZeroOneSolution_iso
---
The library's invariance theorem for HasZeroOneSolution.
-/
theorem hasZeroOneSolution_iso {A B : Type} [Lax799700.ZeroOneIP.zeroOneIP.Structure A] [Lax799700.ZeroOneIP.zeroOneIP.Structure B] (e : A ≃[Lax799700.ZeroOneIP.zeroOneIP] B) :
    HasZeroOneSolution A ↔ HasZeroOneSolution B :=
  DescriptiveComplexity.hasZeroOneSolution_iso e

/--
---
conclusion: Lax799700.ZeroOneIP.zeroOneIP_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem zeroOneIP_iff (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] : ZeroOneIP A ↔ HasZeroOneSolution A :=
  Common.ofPred_iff @DescriptiveComplexity.hasZeroOneSolution_iso A

/-- The library's bundled ZeroOneIP and the catalog's agree on every structure. -/
theorem zeroOneIP_agree (A : Type) [Lax799700.ZeroOneIP.zeroOneIP.Structure A] : DescriptiveComplexity.ZeroOneIP A ↔ ZeroOneIP A :=
  (zeroOneIP_iff A).symm

/--
---
conclusion: Lax799700.ZeroOneIP.zeroOneIP_NP_complete
---
Membership from the library's existential second-order definition of
ZeroOneIP; hardness from the library's reduction out of Knapsack, which is NP-
hard by the catalog’s statement for it. Both are transported to the catalog's
problems along the agreements.
-/
theorem zeroOneIP_NP_complete : NP.Complete ZeroOneIP :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => zeroOneIP_agree A).mp DescriptiveComplexity.zeroOneIP_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (Common.OrderedFOReduction.congr Lax799700Proofs.Bridge.Knapsack.knapsack_agree zeroOneIP_agree DescriptiveComplexity.knapsack_ordered_fo_reduction_zeroOneIP) Lax799700.Knapsack.knapsack_NP_complete.2⟩

end Lax799700Proofs.Bridge.ZeroOneIP
