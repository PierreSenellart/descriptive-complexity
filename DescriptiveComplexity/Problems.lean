/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.Problems.Sat
public import DescriptiveComplexity.Problems.SatUnsat
public import DescriptiveComplexity.Problems.Sat.Hardness
public import DescriptiveComplexity.Problems.Sat.TseitinUnique
public import DescriptiveComplexity.Problems.Sat.Counting
public import DescriptiveComplexity.Problems.Sat.CountingHardness
public import DescriptiveComplexity.Problems.Sat.CountingDnf
public import DescriptiveComplexity.Problems.Sat.CountingDnfSubtractive
public import DescriptiveComplexity.Problems.Sat.CountingDecision
public import DescriptiveComplexity.Problems.Sat.CountingCompare
public import DescriptiveComplexity.Problems.Sat.CountingRestricted
public import DescriptiveComplexity.Problems.SatUnsat.Hardness
public import DescriptiveComplexity.Problems.Taut
public import DescriptiveComplexity.Problems.ThreeDnfTaut
public import DescriptiveComplexity.Problems.HornSat
public import DescriptiveComplexity.Problems.Cvp
public import DescriptiveComplexity.Problems.CircuitNumber
public import DescriptiveComplexity.Problems.MachineNumber
public import DescriptiveComplexity.Problems.Reachability
public import DescriptiveComplexity.Problems.Game
public import DescriptiveComplexity.Problems.ReachabilityDet
public import DescriptiveComplexity.Problems.ReachabilityDet.Complement
public import DescriptiveComplexity.Problems.ThreeColorability
public import DescriptiveComplexity.Problems.ThreeColorability.CountGadget
public import DescriptiveComplexity.Problems.ThreeColorability.Counting
public import DescriptiveComplexity.Problems.ThreeColorability.CountDraw
public import DescriptiveComplexity.Problems.Coloring
public import DescriptiveComplexity.Problems.ThreeSat
public import DescriptiveComplexity.Problems.ThreeSat.Counting
public import DescriptiveComplexity.Problems.ThreeSat.CountingFromSat
public import DescriptiveComplexity.Problems.TwoSat
public import DescriptiveComplexity.Problems.NaeSat
public import DescriptiveComplexity.Problems.NaeThreeSat
public import DescriptiveComplexity.Problems.OneInSat
public import DescriptiveComplexity.Problems.OneInSat.Counting
public import DescriptiveComplexity.Problems.OneInSat.ExactlyOne
public import DescriptiveComplexity.Problems.OneInSat.CountingFromSat
public import DescriptiveComplexity.Problems.CycleCover.Defs
public import DescriptiveComplexity.Problems.CycleCover.Base
public import DescriptiveComplexity.Problems.CycleCover.Models
public import DescriptiveComplexity.Problems.CycleCover.Formulas
public import DescriptiveComplexity.Problems.CycleCover.Drawing
public import DescriptiveComplexity.Problems.CycleCover.Completeness
public import DescriptiveComplexity.Problems.CliqueFamily
public import DescriptiveComplexity.Problems.CliqueFamily.Counting
public import DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
public import DescriptiveComplexity.Problems.CliqueFamily.CountingReductions
public import DescriptiveComplexity.Problems.CliqueFamily.Pendant
public import DescriptiveComplexity.Problems.CliqueFamily.CountingAll
public import DescriptiveComplexity.Problems.CliqueFamily.Stretch
public import DescriptiveComplexity.Problems.CliqueFamily.CountingBipartite
public import DescriptiveComplexity.Problems.SubgraphIso
public import DescriptiveComplexity.Problems.SubgraphIso.Encoding
public import DescriptiveComplexity.Problems.DigraphIso
public import DescriptiveComplexity.Problems.DigraphIso.Bridge
public import DescriptiveComplexity.Problems.DagIso
public import DescriptiveComplexity.Problems.GraphIso.Defs
public import DescriptiveComplexity.Problems.GraphIso.Gadget
public import DescriptiveComplexity.Problems.GraphIso.Hardness
public import DescriptiveComplexity.Problems.GIDegree
public import DescriptiveComplexity.Problems.SetFamily
public import DescriptiveComplexity.Problems.SetFamily.CountingPacking
public import DescriptiveComplexity.Problems.SetFamily.CountingCover
public import DescriptiveComplexity.Problems.ExactCover
public import DescriptiveComplexity.Problems.SetFamily.Counting
public import DescriptiveComplexity.Problems.ExactCoverCounting
public import DescriptiveComplexity.Problems.SetSplitting
public import DescriptiveComplexity.Problems.NaeSatCounting
public import DescriptiveComplexity.Problems.DominatingSet
public import DescriptiveComplexity.Problems.DominatingSet.Counting
public import DescriptiveComplexity.Problems.DominatingSet.CountingHardness
public import DescriptiveComplexity.Problems.Knapsack
public import DescriptiveComplexity.Problems.Knapsack.Counting
public import DescriptiveComplexity.Problems.Knapsack.CountingHardness
public import DescriptiveComplexity.Problems.Partition
public import DescriptiveComplexity.Problems.ZeroOneIP
public import DescriptiveComplexity.Problems.ZeroOneIP.Counting
public import DescriptiveComplexity.Problems.ZeroOneIP.CountingHardness
public import DescriptiveComplexity.Problems.JobSequencing
public import DescriptiveComplexity.Problems.ThreeDimMatching
public import DescriptiveComplexity.Problems.Hamilton
public import DescriptiveComplexity.Problems.Hamilton.Counting
public import DescriptiveComplexity.Problems.Hamilton.CircuitPerm
public import DescriptiveComplexity.Problems.Hamilton.CountingGadget
public import DescriptiveComplexity.Problems.Hamilton.CountingForward
public import DescriptiveComplexity.Problems.Hamilton.CountingReverse
public import DescriptiveComplexity.Problems.Hamilton.CountingHardness
public import DescriptiveComplexity.Problems.Hamilton.CountingUndirected
public import DescriptiveComplexity.Problems.Hamilton.CountingUndirectedHardness
public import DescriptiveComplexity.Problems.Feedback
public import DescriptiveComplexity.Problems.Feedback.Counting
public import DescriptiveComplexity.Problems.Feedback.CountingArc
public import DescriptiveComplexity.Problems.Feedback.SplitBundle
public import DescriptiveComplexity.Problems.Feedback.CountingArcHardness
public import DescriptiveComplexity.Problems.MaxCut
public import DescriptiveComplexity.Problems.Steiner
public import DescriptiveComplexity.Problems.Steiner.Counting
public import DescriptiveComplexity.Problems.Steiner.CountingHardness
public import DescriptiveComplexity.Problems.Qbf
public import DescriptiveComplexity.Problems.Qsat
public import DescriptiveComplexity.Problems.SuccinctReach
public import DescriptiveComplexity.Problems.FinSat
public import DescriptiveComplexity.Problems.Pcp
public import DescriptiveComplexity.Problems.Machine
public import DescriptiveComplexity.Problems.Machine.Counting
public import DescriptiveComplexity.Problems.Machine.CountingHardness
public import DescriptiveComplexity.Problems.MachineAlt
public import DescriptiveComplexity.Problems.MachineAltSpace
public import DescriptiveComplexity.Problems.MachineAltSpace.Membership
public import DescriptiveComplexity.Problems.Wide
public import DescriptiveComplexity.Problems.Tiling
public import DescriptiveComplexity.Problems.Epr
public import DescriptiveComplexity.Problems.Machine.Halt
public import DescriptiveComplexity.Problems.Machine.HaltCert
public import DescriptiveComplexity.Problems.Machine.HaltFin
public import DescriptiveComplexity.Problems.Machine.HaltMem
public import DescriptiveComplexity.Problems.Machine.HaltHard
public import DescriptiveComplexity.Problems.CodeHalt
public import DescriptiveComplexity.Problems.Even
public import DescriptiveComplexity.Problems.Parity

/-!
# The problem catalog

Umbrella file importing every decision problem of the library. Each problem
lives in its own file (or directory) under `DescriptiveComplexity/Problems/`,
containing its vocabulary, its semantic definition, the bundled
`DescriptiveComplexity.DecisionProblem`, its first-order reductions, and its
completeness theorems.

Job sequencing carries only the membership half of a completeness statement.
Digraph Isomorphism (`DescriptiveComplexity.DigraphIso`) carries the membership
half on purpose: it is in NP (`DescriptiveComplexity.digraphIso_mem_NP`) and
conjecturally neither in P nor NP-complete, so what it is complete for is its *own* degree
(`DescriptiveComplexity.GI`, from `DescriptiveComplexity.Degree`). DAG
Isomorphism (`DescriptiveComplexity.DagIso`) is the first other problem of that
degree: **GI-complete** (`DescriptiveComplexity.dagIso_GI_complete`), by
subdividing every arc twice in one direction and forgetting the carried
topological order in the other. Graph Isomorphism
(`DescriptiveComplexity.GraphIso`) is the same question restricted to *simple*
graphs – what the literature means by GI – and carries its membership half
(`DescriptiveComplexity.graphIso_mem_GI`): simplicity is first-order, so the
reduction into `DigraphIso` only has to test it, while the converse needs the
classical digraph-to-graph gadget. Alternating machine acceptance
(`DescriptiveComplexity.ATMAccept`) is the machine bridge for the polynomial
hierarchy, complete at every level
(`DescriptiveComplexity.atmAccept_sigmaP_complete`,
`DescriptiveComplexity.atmAccept_piP_complete`) – see
`DescriptiveComplexity.Problems.MachineAlt`. The halting problem
(`DescriptiveComplexity.HALT`, the same machine with the tape unbounded) is
**RE-complete** (`DescriptiveComplexity.halt_RE_complete`, hardness being the
machine bridge of `DescriptiveComplexity.Problems.Machine.HaltHard`); its
membership half alone already gives `DescriptiveComplexity.halt_le_finsat`,
Trakhtenbrot's theorem in the form it is usually stated. The
halting of a *partial recursive code* drawn as a syntax tree
(`DescriptiveComplexity.CODEHALT`) is **RE-complete**
(`DescriptiveComplexity.codehalt_RE_complete`), and is the problem the
**undecidability** of the development goes through: it is undecidable outright
(`DescriptiveComplexity.not_computablePred_codehalt`), whence
`DescriptiveComplexity.finsat_not_computable`. Its hardness reduction draws the
instance as the *program* that runs a semi-decision procedure on it, which is
general enough to identify the class with its machine reading
(`DescriptiveComplexity.mem_RE_iff_rePred`) and to separate it from its
complement (`DescriptiveComplexity.RE_ne_coRE`). Post's
correspondence problem (`DescriptiveComplexity.PCP`) is **RE-complete** too
(`DescriptiveComplexity.pcp_RE_complete`): membership invents the slots of
the sequence of dominoes together with a matching between the two parses of
the word it spells, and hardness is the computation-history dominoes from
`HALT` (`DescriptiveComplexity.Problems.Pcp.Hardness`), whence the
undecidability of Post's problem
(`DescriptiveComplexity.pcp_not_computable`).
-/

@[expose] public section
