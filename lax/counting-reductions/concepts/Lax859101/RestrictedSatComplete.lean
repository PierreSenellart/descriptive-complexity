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
title: #2SAT, #HORN-SAT, and #Monotone-2SAT are one-call #P-complete
type: theorem
---
#2SAT, #HORN-SAT, and #Monotone-2SAT are one-call #P-complete, although
their decision versions are in polynomial time: the independent sets of a
graph are the models of a formula with one clause per edge, which has at
most two literals, all negative, or all positive for the vertex covers.
-/

namespace Lax859101.RestrictedSatComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #2SAT is one-call #P-complete. -/
axiom sharpTwoSat_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpTwoSAT

/-- #HORN-SAT is one-call #P-complete. -/
axiom sharpHornSat_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpHornSAT

/-- #Monotone-2SAT is one-call #P-complete. -/
axiom sharpMonotoneTwoSat_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpMonotoneTwoSAT

end Lax859101.RestrictedSatComplete
