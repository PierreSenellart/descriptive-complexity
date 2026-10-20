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
title: #P is closed under subtractive reductions
type: theorem
---
Subtractive reducibility is transitive, and contains the relativized ordered
parsimonious reductions and the strong subtractive reductions. #P is closed
under subtractive reductions, a theorem of Durand, Hermann, and Kolaitis:
the witnesses at the minuend that are not witnesses at the subtrahend are
counted by an existential second-order sentence. Hardness travels forward
along subtractive reductions, and a parsimoniously #P-complete problem is
#P-complete.
-/

namespace Lax859101.SubtractiveClosure

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- Subtractive reducibility is transitive. -/
axiom subtractive_trans :
  ∀ {L L' L'' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] [L''.IsRelational]
      {C : CountingProblem L} {D : CountingProblem L'} {E : CountingProblem L''},
    SubtractiveReducible C D → SubtractiveReducible D E → SubtractiveReducible C E

/-- A relativized ordered parsimonious reduction is subtractive. -/
axiom subtractive_of_relOrderedParsimonious :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {C : CountingProblem L}
      {D : CountingProblem L'},
    Nonempty (RelOrderedParsimoniousReduction C D) → SubtractiveReducible C D

/-- A strong subtractive reduction is subtractive. -/
axiom subtractive_of_strongSubtractive :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {C : CountingProblem L}
      {D : CountingProblem L'},
    Nonempty (StrongSubtractiveReduction C D) → SubtractiveReducible C D

/-- #P is closed under subtractive reductions. -/
axiom sharpP_mem_of_subtractive :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {C : CountingProblem L}
      {D : CountingProblem L'},
    SubtractiveReducible C D → SharpP.Mem D → SharpP.Mem C

/-- Hardness travels forward along subtractive reductions. -/
axiom subtractiveHard_of_subtractive :
  ∀ (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
      {C : CountingProblem L} {D : CountingProblem L'},
    SubtractiveReducible C D → SubtractiveHard K C → SubtractiveHard K D

/-- A parsimoniously #P-complete problem is #P-complete. -/
axiom subtractiveComplete_sharpP_of_parsimoniousComplete :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    SharpP.ParsimoniousComplete C → SubtractiveComplete SharpP C

end Lax859101.SubtractiveClosure
