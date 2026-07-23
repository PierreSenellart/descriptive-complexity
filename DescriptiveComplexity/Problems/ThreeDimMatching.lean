/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import DescriptiveComplexity.Problems.ThreeDimMatching.Membership
import DescriptiveComplexity.Problems.ThreeDimMatching.Hardness
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Hierarchy

/-!
# 3-dimensional matching

Umbrella file for `DescriptiveComplexity.ThreeDimMatching`, Karp's 3-DIMENSIONAL
MATCHING – do some of the available triples cover every marked element exactly
once? – on the vocabulary `FirstOrder.Language.tripleSys` of three marked
classes and a ternary relation.

It collects the definition and its isomorphism-invariance, the membership half
(`DescriptiveComplexity.threeDimMatching_mem_NP`) – a matching *is* a relation, so
the certificate guesses it and the kernel spells out “inside the classes,
everything covered, nothing twice” – and the hardness half
(`DescriptiveComplexity.sat_ordered_fo_reduction_threeDimMatching`), Karp's reduction
from SAT: a truth-setting gadget running **cyclically** through the
occurrences of each variable, a pair per clause coverable only through the tip
of a true literal, and one garbage pair per occurrence that is not the first
of its clause – exactly as many as there are tips left over.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- 3-dimensional matching is in NP: it is `Σ₁`-definable, the certificate
being the matching itself. -/
theorem threeDimMatching_mem_NP : ThreeDimMatching ∈ NP :=
  threeDimMatching_sigmaSODefinable

/-- 3-dimensional matching is NP-hard: SAT, which is NP-hard, FO-reduces to it
over any linear order on the input. -/
theorem threeDimMatching_NP_hard : NP.Hard ThreeDimMatching :=
  NP.hard_of_orderedReduction sat_ordered_fo_reduction_threeDimMatching sat_NP_hard

/-- **3-dimensional matching is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem threeDimMatching_NP_complete : NP.Complete ThreeDimMatching :=
  ⟨threeDimMatching_mem_NP, threeDimMatching_NP_hard⟩

end DescriptiveComplexity
