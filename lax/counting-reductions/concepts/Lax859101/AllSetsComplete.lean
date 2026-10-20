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
title: Counting all independent sets and vertex covers is one-call #P-complete
type: theorem
---
Counting all the independent sets of a graph is one-call #P-complete, by a
one-call reduction from #Independent Set, and so is counting all the vertex
covers, which are the complements of the independent sets.
-/

namespace Lax859101.AllSetsComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- Counting all independent sets is one-call #P-complete. -/
axiom sharpAllIndependentSets_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpAllIndependentSets

/-- Counting all vertex covers is one-call #P-complete. -/
axiom sharpAllVertexCovers_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpAllVertexCovers

end Lax859101.AllSetsComplete
