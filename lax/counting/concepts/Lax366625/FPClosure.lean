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
title: FP is closed under parsimonious reductions
type: theorem
---
Membership in FP travels backward along ordered parsimonious reductions and
along relativized ordered parsimonious reductions, and reads a problem on its
finite instances only.
-/

namespace Lax366625.FPClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- Membership in FP travels backward along ordered parsimonious reductions. -/
axiom FP_mem_of_orderedParsimonious : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : CountingProblem L} {D : CountingProblem L'},
  OrderedParsimoniousReduction C D → FP.Mem D → FP.Mem C

/-- Membership in FP travels backward along relativized ordered
parsimonious reductions. -/
axiom FP_mem_of_relOrderedParsimonious :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : CountingProblem L} {D : CountingProblem L'},
  RelOrderedParsimoniousReduction C D → FP.Mem D → FP.Mem C

/-- Membership in FP only depends on the finite instances of a problem. -/
axiom FP_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], C A = D A) → (FP.Mem C ↔ FP.Mem D)

end Lax366625.FPClosure
