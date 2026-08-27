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
import DescriptiveComplexity.Problems.Cvp
import DescriptiveComplexity.Problems.Reachability
import DescriptiveComplexity.Problems.Game
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
import DescriptiveComplexity.Problems.SubgraphIso.Encoding
import DescriptiveComplexity.Problems.DigraphIso
import DescriptiveComplexity.Problems.DigraphIso.Bridge
import DescriptiveComplexity.Problems.DagIso
import DescriptiveComplexity.Problems.GraphIso.Defs
import DescriptiveComplexity.Problems.GraphIso.Gadget
import DescriptiveComplexity.Problems.GraphIso.Hardness
import DescriptiveComplexity.Problems.GIDegree
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
import DescriptiveComplexity.Problems.MachineAltSpace
import DescriptiveComplexity.Problems.MachineAltSpace.Membership
import DescriptiveComplexity.Problems.Wide
import DescriptiveComplexity.Problems.Tiling
import DescriptiveComplexity.Problems.Epr
import DescriptiveComplexity.Problems.Machine.Halt
import DescriptiveComplexity.Problems.Machine.HaltCert
import DescriptiveComplexity.Problems.Machine.HaltFin
import DescriptiveComplexity.Problems.Machine.HaltMem
import DescriptiveComplexity.Problems.Machine.HaltHard
import DescriptiveComplexity.Problems.CodeHalt
import DescriptiveComplexity.Problems.Even
import DescriptiveComplexity.Problems.Parity

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
