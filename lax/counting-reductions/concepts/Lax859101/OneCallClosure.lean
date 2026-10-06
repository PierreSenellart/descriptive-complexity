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
title: One-call reductions compose, and the one-call closure
type: theorem
---
One-call reductions compose: the post-processing term of the second is
substituted for the oracle in the first, pulled back through the first
interpretation. A relativized ordered parsimonious reduction is a one-call
reduction with the oracle as its term. The one-call closure of a class
contains the class and is closed under one-call reductions, one-call
hardness travels forward along them, and one-call hardness is hardness for
the whole closure. A parsimoniously #P-complete problem is one-call
#P-complete.
-/

namespace Lax859101.OneCallClosure

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- One-call reductions compose. -/
axiom oneCall_trans :
  ∀ {L L' L'' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] [L''.IsRelational]
      {C : CountingProblem L} {D : CountingProblem L'} {E : CountingProblem L''},
    Nonempty (OneCallReduction C D) → Nonempty (OneCallReduction D E) → Nonempty
        (OneCallReduction C E)

/-- A relativized ordered parsimonious reduction is a one-call reduction. -/
axiom oneCall_of_relOrderedParsimonious :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {C : CountingProblem L}
      {D : CountingProblem L'},
    Nonempty (RelOrderedParsimoniousReduction C D) → Nonempty (OneCallReduction C D)

/-- A problem of a class is in its one-call closure. -/
axiom oneCallMem_of_mem :
  ∀ (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    K.Mem C → OneCallMem K C

/-- The one-call closure is closed under one-call reductions. -/
axiom oneCallMem_of_oneCall :
  ∀ (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
      {C : CountingProblem L} {D : CountingProblem L'},
    Nonempty (OneCallReduction C D) → OneCallMem K D → OneCallMem K C

/-- One-call hardness travels forward along one-call reductions. -/
axiom oneCallHard_of_oneCall :
  ∀ (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
      {C : CountingProblem L} {D : CountingProblem L'},
    Nonempty (OneCallReduction C D) → OneCallHard K C → OneCallHard K D

/-- One-call hardness is hardness for the one-call closure. -/
axiom oneCallHard_iff :
  ∀ (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    OneCallHard K C ↔ ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
      OneCallMem K D → Nonempty (OneCallReduction D C)

/-- A parsimoniously #P-complete problem is one-call #P-complete. -/
axiom oneCallComplete_sharpP_of_parsimoniousComplete :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    SharpP.ParsimoniousComplete C → OneCallComplete SharpP C

end Lax859101.OneCallClosure
