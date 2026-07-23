/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Partition.Defs
import DescriptiveComplexity.Problems.Partition.Membership
import DescriptiveComplexity.Hierarchy

/-!
# Partition

Umbrella file for `DescriptiveComplexity.Partition`, Karp's PARTITION – can a
family of numbers, written in *binary*, be split into two parts of equal sum?

It collects the definition, its isomorphism-invariance and the membership half
(`DescriptiveComplexity.partition_mem_NP`): the certificate guesses the split and two
ripple-carry walks – one along the chosen items, one along the others – on the
*wide* positions of `DescriptiveComplexity.Numbers.Wide`, and requires them to agree
at the last item, which says exactly that the two sides weigh the same. The
hardness reduction from NAE-3SAT is under construction – see `ROADMAP.md`.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Partition is in NP: it is `Σ₁`-definable, the certificate carrying the
split and the two ripple-carry walks that weigh its two sides. -/
theorem partition_mem_NP : Partition ∈ NP :=
  partition_sigmaSODefinable

end DescriptiveComplexity
