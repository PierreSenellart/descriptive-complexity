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
title: #BIS and #PP2DNF are one-call #P-complete
type: theorem
---
#BIS is one-call #P-complete, by a one-call reduction from counting all
independent sets. #PP2DNF is, by a one-call reduction from #BIS: on a
bipartite graph, the sets of vertices that are not independent are the
models of its partitioned positive 2-DNF formula.
-/

namespace Lax859101.BipartiteComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #BIS is one-call #P-complete. -/
axiom sharpBIS_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpBIS

/-- #PP2DNF is one-call #P-complete. -/
axiom sharpPP2DNF_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpPP2DNF

end Lax859101.BipartiteComplete
