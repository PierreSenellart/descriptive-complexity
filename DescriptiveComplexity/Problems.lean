/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.Problems.SatUnsat
import DescriptiveComplexity.Problems.Sat.Hardness
import DescriptiveComplexity.Problems.SatUnsat.Hardness
import DescriptiveComplexity.Problems.Taut
import DescriptiveComplexity.Problems.ThreeDnfTaut
import DescriptiveComplexity.Problems.HornSat
import DescriptiveComplexity.Problems.Reachability
import DescriptiveComplexity.Problems.ReachabilityDet
import DescriptiveComplexity.Problems.ReachabilityDet.Complement
import DescriptiveComplexity.Problems.ThreeColorability
import DescriptiveComplexity.Problems.Coloring
import DescriptiveComplexity.Problems.ThreeSat
import DescriptiveComplexity.Problems.TwoSat
import DescriptiveComplexity.Problems.NaeSat
import DescriptiveComplexity.Problems.NaeThreeSat
import DescriptiveComplexity.Problems.OneInSat
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.Problems.SubgraphIso
import DescriptiveComplexity.Problems.SetFamily
import DescriptiveComplexity.Problems.ExactCover
import DescriptiveComplexity.Problems.SetSplitting
import DescriptiveComplexity.Problems.DominatingSet
import DescriptiveComplexity.Problems.Knapsack
import DescriptiveComplexity.Problems.Partition
import DescriptiveComplexity.Problems.ZeroOneIP
import DescriptiveComplexity.Problems.JobSequencing
import DescriptiveComplexity.Problems.ThreeDimMatching
import DescriptiveComplexity.Problems.Hamilton
import DescriptiveComplexity.Problems.Feedback
import DescriptiveComplexity.Problems.MaxCut
import DescriptiveComplexity.Problems.Steiner
import DescriptiveComplexity.Problems.Qbf
import DescriptiveComplexity.Problems.Qsat
import DescriptiveComplexity.Problems.SuccinctReach
import DescriptiveComplexity.Problems.FinSat
import DescriptiveComplexity.Problems.Pcp
import DescriptiveComplexity.Problems.Machine
import DescriptiveComplexity.Problems.MachineAlt
import DescriptiveComplexity.Problems.Machine.Halt
import DescriptiveComplexity.Problems.Machine.HaltCert
import DescriptiveComplexity.Problems.Machine.HaltFin
import DescriptiveComplexity.Problems.Machine.HaltMem
import DescriptiveComplexity.Problems.CodeHalt

/-!
# The problem catalog

Umbrella file importing every decision problem of the library. Each problem
lives in its own file (or directory) under `DescriptiveComplexity/Problems/`,
containing its vocabulary, its semantic definition, the bundled
`DescriptiveComplexity.DecisionProblem`, its first-order reductions, and its
completeness theorems.

Job sequencing is in NP but not yet proved NP-hard, so its umbrella carries
only the membership half – see `ROADMAP.md`. Alternating machine acceptance
(`DescriptiveComplexity.ATMAccept`) is the machine bridge for the polynomial
hierarchy: complete at one block (`DescriptiveComplexity.atmAccept_one_complete`)
and a member of its level at every one (`DescriptiveComplexity.atmAccept_mem_sigmaP`,
`DescriptiveComplexity.atmAccept_mem_piP`), with hardness above level one still
open – see `DescriptiveComplexity.Problems.MachineAlt` and `ROADMAP.md` (§7). The halting problem (`DescriptiveComplexity.HALT`, the same machine
with the tape unbounded) is **in RE** (`DescriptiveComplexity.halt_mem_RE`),
whence `DescriptiveComplexity.halt_le_finsat`, Trakhtenbrot's theorem in the form
it is usually stated; it is not proved RE-*hard*, see `ROADMAP.md` (§8). The
halting of a *partial recursive code* drawn as a syntax tree
(`DescriptiveComplexity.CODEHALT`) is in RE too
(`DescriptiveComplexity.codehalt_mem_RE`), and is the problem the
**undecidability** of the development goes through: it is undecidable outright
(`DescriptiveComplexity.not_computablePred_codehalt`), whence
`DescriptiveComplexity.finsat_not_computable`. Post's
correspondence problem (`DescriptiveComplexity.PCP`) is in RE too
(`DescriptiveComplexity.pcp_mem_RE`), the invented values being the slots of
the sequence of dominoes together with a matching between the two parses of
the word it spells; its RE-*hardness* is not a catalog item at all but the RE
machine bridge, see `ROADMAP.md` (§8).
-/
