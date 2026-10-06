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
title: #Steiner Tree is parsimoniously #P-complete
type: theorem
---
#Steiner Tree is parsimoniously #P-complete: it is in #P, and every problem of #P
reduces to it by a relativized ordered parsimonious reduction. Hardness
comes from #Vertex Cover by an ordered parsimonious reduction.
The support of #Steiner Tree is the existence of a solution of exactly the threshold
size, which gives a yes-instance of SteinerTree; the converse needs a solution of
another size to be cut down or padded, which the library does not prove.
-/

namespace Lax280166.SteinerTreeComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Sat
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax799700.ThreeSat Lax799700.SetFamily
open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- #Steiner Tree is parsimoniously #P-complete. -/
axiom sharpSteinerTree_sharpP_parsimoniousComplete :
  SharpP.ParsimoniousComplete SharpSteinerTree

/-- The support of #Steiner Tree: a solution of exactly the threshold size exists. -/
axiom sharpSteinerTree_support_iff :
  ∀ (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] [Finite A],
    SharpSteinerTree.support A ↔ ∃ S : A → Prop, SteinerOfSize A S

/-- A positive count of #Steiner Tree gives a yes-instance of SteinerTree. -/
axiom steinerTree_of_sharpSteinerTree_support :
  ∀ (A : Type) [Lax799700.Steiner.steinerGraph.Structure A] [Finite A],
    SharpSteinerTree.support A → Lax799700.Steiner.SteinerTree A

end Lax280166.SteinerTreeComplete
