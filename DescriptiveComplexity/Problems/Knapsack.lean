/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Defs
import DescriptiveComplexity.Problems.Knapsack.Chain
import DescriptiveComplexity.Problems.Knapsack.Membership
import DescriptiveComplexity.Problems.Knapsack.Hardness
import DescriptiveComplexity.Problems.ExactCover
import DescriptiveComplexity.Hierarchy

/-!
# Knapsack

Umbrella file for `DescriptiveComplexity.Knapsack`, Karp's KNAPSACK – some set of
items whose weights sum exactly to the target – with the weights written in
*binary* (representation (C)), which is what makes the problem NP-hard rather
than polynomial-time.

It collects the membership half (`DescriptiveComplexity.knapsack_sigmaSODefinable`,
the certificate carrying the running totals and the carries of a ripple-carry
addition) and the hardness half
(`DescriptiveComplexity.exactCover_ordered_fo_reduction_knapsack`, one digit block of
bit positions per ground element of an exact-cover instance). Partition, Job
Sequencing and 0-1 Integer Programming follow from Knapsack – see
`ROADMAP.md`.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Knapsack is in NP: it is `Σ₁`-definable, the certificate carrying the
running totals and the carries of a ripple-carry addition. -/
theorem knapsack_mem_NP : Knapsack ∈ NP :=
  knapsack_sigmaSODefinable

/-- Knapsack is NP-hard: Exact Cover, which is NP-hard, FO-reduces to it over
any linear order on the input. -/
theorem knapsack_NP_hard : NP.Hard Knapsack :=
  NP.hard_of_orderedReduction exactCover_ordered_fo_reduction_knapsack exactCover_NP_hard

/-- **Knapsack is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. Its weights are written in *binary*:
under the unary representation the problem is solvable in polynomial time. -/
theorem knapsack_NP_complete : NP.Complete Knapsack :=
  ⟨knapsack_mem_NP, knapsack_NP_hard⟩

end DescriptiveComplexity
