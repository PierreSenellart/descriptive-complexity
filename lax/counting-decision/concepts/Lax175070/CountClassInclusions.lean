import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Interpretations
import Lax904597.Machines
import Lax564036.Hierarchy
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax366625.CountingRuns
import Lax175070.CountDefinability
import Lax175070.SelectedSat

/-!
---
title: Inclusions between the counting classes, NP, and coNP
type: theorem
---
UP ⊆ NP and UP ⊆ ⊕P: a count of at most one is one exactly when it is
positive, and exactly when it is odd. NP ⊆ PP: a problem with a witness has
more witnesses than a kernel that never holds has. coNP ⊆ PP follows by the
closure of PP under complement.
-/

namespace Lax175070.CountClassInclusions

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- UP ⊆ ⊕P. -/
axiom UP_subset_parityP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    UP.Mem P → ParityP.Mem P

/-- UP ⊆ NP. -/
axiom UP_subset_NP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    UP.Mem P → NP.Mem P

/-- NP ⊆ PP. -/
axiom NP_subset_PP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    NP.Mem P → PP.Mem P

/-- coNP ⊆ PP. -/
axiom coNP_subset_PP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    coNP.Mem P → PP.Mem P

end Lax175070.CountClassInclusions
