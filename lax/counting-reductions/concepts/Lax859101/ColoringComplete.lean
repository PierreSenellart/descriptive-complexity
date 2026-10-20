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
title: #3-Colorability is one-call #P-complete
type: theorem
---
#3-Colorability is one-call #P-complete, by a one-call reduction from #SAT:
the graph built from a formula has $6 \cdot 8^g$ proper 3-colorings for each
model of the formula, $g$ being its number of gadgets, and the
post-processing term divides the oracle answer by that number.
-/

namespace Lax859101.ColoringComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #3-Colorability is one-call #P-complete. -/
axiom sharpThreeCol_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpThreeCol

end Lax859101.ColoringComplete
