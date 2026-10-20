import Lax904597.Problems
import Lax904597.Sat
import Mathlib.ModelTheory.Graph
import Lax799700.SetFamily
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite

/-!
---
title: #NAE-SAT and #Set Splitting are one-call #P-complete
type: theorem
---
#NAE-SAT is one-call #P-complete, by a one-call reduction from #SAT, and
#Set Splitting is, by a one-call reduction from #NAE-SAT.
-/

namespace Lax859101.NaeSatComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #NAE-SAT is one-call #P-complete. -/
axiom sharpNaeSat_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpNAESAT

/-- #Set Splitting is one-call #P-complete. -/
axiom sharpSetSplitting_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpSetSplitting

end Lax859101.NaeSatComplete
