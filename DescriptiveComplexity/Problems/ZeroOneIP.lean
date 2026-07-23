/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ZeroOneIP.Defs
import DescriptiveComplexity.Problems.ZeroOneIP.Membership
import DescriptiveComplexity.Problems.ZeroOneIP.Hardness
import DescriptiveComplexity.Problems.Knapsack
import DescriptiveComplexity.Hierarchy

/-!
# 0-1 integer programming

Umbrella file for `DescriptiveComplexity.ZeroOneIP`, Karp's 0-1 INTEGER
PROGRAMMING – is there a `0-1` vector `x` with `C x = d`? – with the entries
written in *binary* (representation (C)), which is what makes the problem
NP-hard rather than polynomial-time.

It collects the membership half
(`DescriptiveComplexity.zeroOneIP_sigmaSODefinable`, the certificate carrying one
ripple-carry walk per row) and the hardness half
(`DescriptiveComplexity.knapsack_ordered_fo_reduction_zeroOneIP`): a single equation
with `0-1` variables *is* a subset-sum instance, so Knapsack reduces to it by
a one-tag, dimension-one interpretation whose only piece of work is naming the
single row, the minimum of the input order.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- 0-1 integer programming is in NP: it is `Σ₁`-definable, the certificate
carrying, for each row, the running totals and the carries of a ripple-carry
addition along the columns. -/
theorem zeroOneIP_mem_NP : ZeroOneIP ∈ NP :=
  zeroOneIP_sigmaSODefinable

/-- 0-1 integer programming is NP-hard: Knapsack, which is NP-hard,
FO-reduces to it over any linear order on the input. -/
theorem zeroOneIP_NP_hard : NP.Hard ZeroOneIP :=
  NP.hard_of_orderedReduction knapsack_ordered_fo_reduction_zeroOneIP knapsack_NP_hard

/-- **0-1 integer programming is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. Its entries are written
in *binary*: under the unary representation the problem is solvable in
polynomial time. -/
theorem zeroOneIP_NP_complete : NP.Complete ZeroOneIP :=
  ⟨zeroOneIP_mem_NP, zeroOneIP_NP_hard⟩

end DescriptiveComplexity
