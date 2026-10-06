import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.SecondOrderCounting
import Lax366625.QuantitativeLogic
import Lax366625.CountingSat
import Lax366625.MachineNumbers
import Lax366625.CountingRuns
import Lax366625.NumberedCircuits
import Lax366625.HornNumbers

/-!
---
title: #P and NP
type: theorem
---
A decision problem is in NP if and only if it agrees, on nonempty finite
structures, with the support of some counting problem of #P: NP is the class
of the supports of #P. The support of a parsimoniously #P-hard counting
problem is NP-hard, and if such a support is in PTIME, then NP is contained
in PTIME. So a counting problem whose support is easy, such as counting the
models of a DNF formula, is not parsimoniously #P-hard unless NP ⊆ PTIME.
-/

namespace Lax366625.SharpPAndNP

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- NP is the class of the supports of #P. -/
axiom mem_NP_iff_exists_sharpP_support :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NP.Mem P ↔ ∃ C : CountingProblem L, SharpP.Mem C ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], C.support A ↔ P A

/-- The support of a parsimoniously #P-hard problem is NP-hard. -/
axiom NP_hard_support_of_sharpP_parsimoniousHard :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
  SharpP.ParsimoniousHard C → NP.Hard C.support

/-- A parsimoniously #P-hard problem with support in PTIME gives NP ⊆ PTIME. -/
axiom NP_subset_PTIME_of_sharpP_parsimoniousHard :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
  SharpP.ParsimoniousHard C → PTIME.Mem C.support →
    ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'), NP.Mem P → PTIME.Mem P

end Lax366625.SharpPAndNP
