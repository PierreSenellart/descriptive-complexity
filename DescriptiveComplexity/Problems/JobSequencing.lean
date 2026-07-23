/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.JobSequencing.Defs
import DescriptiveComplexity.Problems.JobSequencing.Schedule
import DescriptiveComplexity.Problems.JobSequencing.Kernel
import DescriptiveComplexity.Problems.JobSequencing.Membership
import DescriptiveComplexity.Problems.JobSequencing.Hardness
import DescriptiveComplexity.Problems.NaeThreeSat
import DescriptiveComplexity.Hierarchy

/-!
# Job sequencing

Umbrella file for `DescriptiveComplexity.JobSequencing`, Karp's SEQUENCING – is
there a one-processor schedule whose late jobs carry a total penalty at most
the bound? – with the times, deadlines, penalties and bound written in
*binary* (representation (C)), which is what makes the problem NP-hard rather
than polynomial-time.

It collects the membership half
(`DescriptiveComplexity.jobSequencing_sigmaSODefinable`): the certificate guesses the
schedule as a linear order, the late jobs, and two ripple-carry walks – the
completion times along the schedule, the penalty total of the late jobs along
the instance's own order – and the kernel *compares* as well as adds, a job
being late exactly when its deadline falls below its completion time.

It also collects the hardness half
(`DescriptiveComplexity.nae3Sat_ordered_fo_reduction_jobSequencing`). Karp's reduction
from Partition does not transfer: its deadline and its bound are both half the
total execution time, and half of a total is an iterated sum, which no
first-order interpretation can write. The replacement starts from NAE-3SAT and
gives every digit block an even total – `2` per variable, `2 (w − 1)` per
clause of width `w` – so that the deadline is the digit-wise half, one bit per
block, the bound is the deadline, and a good schedule is a balanced split.
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Job sequencing is in NP: it is `Σ₁`-definable, the certificate carrying a
schedule, the late jobs, and the ripple-carry walks that compute the
completion times and the penalty total. -/
theorem jobSequencing_mem_NP : JobSequencing ∈ NP :=
  jobSequencing_sigmaSODefinable

/-- Job sequencing is NP-hard: NAE-3SAT, which is NP-hard, FO-reduces to it
over any linear order on the input. -/
theorem jobSequencing_NP_hard : NP.Hard JobSequencing :=
  NP.hard_of_orderedReduction nae3Sat_ordered_fo_reduction_jobSequencing nae3Sat_NP_hard

/-- **Job sequencing is NP-complete**, derived from the first-order reductions
of this library and the Cook–Levin theorem. Its execution times, deadlines,
penalties and bound are written in *binary*: under the unary representation
the problem is solvable in polynomial time by dynamic programming. -/
theorem jobSequencing_NP_complete : NP.Complete JobSequencing :=
  ⟨jobSequencing_mem_NP, jobSequencing_NP_hard⟩

end DescriptiveComplexity
