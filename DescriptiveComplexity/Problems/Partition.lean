/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Partition.Defs
import DescriptiveComplexity.Problems.Partition.Membership
import DescriptiveComplexity.Problems.Partition.Hardness
import DescriptiveComplexity.Problems.NaeSat
import DescriptiveComplexity.Hierarchy

/-!
# Partition

Umbrella file for `DescriptiveComplexity.Partition`, Karp's PARTITION – can a
family of numbers, written in *binary*, be split into two parts of equal sum?

It collects the definition, its isomorphism-invariance, the membership half
(`DescriptiveComplexity.partition_mem_NP`) – the certificate guesses the split and two
ripple-carry walks, one along the chosen items, one along the others, on the
*wide* positions of `DescriptiveComplexity.Numbers.Wide`, and requires them to agree
at the last item, which says exactly that the two sides weigh the same – and
the hardness half
(`DescriptiveComplexity.naeSat_ordered_fo_reduction_partition`), a reduction from
NAE-SAT by digit blocks: one per variable, forcing an assignment, and one per
clause, forcing between one and `w − 1` true literals out of `w`.

Karp's own reduction pads a Knapsack instance with the weights `2Σ − T` and
`Σ + T`; both are arithmetic in the total, hence not first-order definable, so
hardness has to start from NAE-SAT instead.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Partition is in NP: it is `Σ₁`-definable, the certificate carrying the
split and the two ripple-carry walks that weigh its two sides. -/
theorem partition_mem_NP : Partition ∈ NP :=
  partition_sigmaSODefinable

/-- Partition is NP-hard: NAE-SAT, which is NP-hard, FO-reduces to it over any
linear order on the input. -/
theorem partition_NP_hard : NP.Hard Partition :=
  NP.hard_of_orderedReduction naeSat_ordered_fo_reduction_partition naeSat_NP_hard

/-- **Partition is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. Its weights are written in *binary*:
under the unary representation the problem is solvable in polynomial time. -/
theorem partition_NP_complete : NP.Complete Partition :=
  ⟨partition_mem_NP, partition_NP_hard⟩

end DescriptiveComplexity
