import Lax904597.Problems
import Lax904597.Sat
import Lax799700.CliqueFamily
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.Knapsack
import Lax799700.OneInSat
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax280166.CountingSatVariants
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingSetFamilies
import Lax280166.CountingKnapsacks
import Lax280166.CountingSteinerTrees

/-!
---
title: #Exact Cover is parsimoniously #P-complete
type: theorem
---
#Exact Cover is parsimoniously #P-complete: it is in #P, and every problem of #P
reduces to it by a relativized ordered parsimonious reduction. Hardness
comes from #1-in-SAT by a parsimonious reduction.
The support of #Exact Cover, the instances with a positive count, is the decision
problem ExactCover of the NP catalog.
-/

namespace Lax280166.ExactCoverComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- #Exact Cover is parsimoniously #P-complete. -/
axiom sharpExactCover_sharpP_parsimoniousComplete :
  SharpP.ParsimoniousComplete SharpExactCover

/-- The support of #Exact Cover is the decision problem ExactCover. -/
axiom sharpExactCover_support_iff :
  ∀ (A : Type) [Lax799700.SetFamily.setSystem.Structure A] [Finite A],
    SharpExactCover.support A ↔ Lax799700.SetFamily.ExactCover A

end Lax280166.ExactCoverComplete
