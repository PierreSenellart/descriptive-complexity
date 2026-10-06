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
title: #P is closed under parsimonious reductions
type: theorem
---
Membership in #P travels backward along ordered parsimonious reductions and
along relativized ordered parsimonious reductions: if a counting problem
reduces to a problem of #P, it is in #P. The witnesses of the target, pulled
back along the interpretation, are witnesses of the source; for a
relativized reduction, the kernel pins the pulled relations to the definable
domain, which makes the correspondence of witnesses a bijection. Membership
reads a problem on its finite instances only.
-/

namespace Lax366625.SharpPClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax535992.ClassPTIME
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
open Lax366625.SecondOrderCounting
open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers
open Lax366625.CountingRuns
open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- Membership in SharpP travels backward along ordered parsimonious reductions. -/
axiom SharpP_mem_of_orderedParsimonious :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : CountingProblem L} {D : CountingProblem L'},
  OrderedParsimoniousReduction C D → SharpP.Mem D → SharpP.Mem C

/-- Membership in SharpP travels backward along relativized ordered
parsimonious reductions. -/
axiom SharpP_mem_of_relOrderedParsimonious :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : CountingProblem L} {D : CountingProblem L'},
  RelOrderedParsimoniousReduction C D → SharpP.Mem D → SharpP.Mem C

/-- Membership in SharpP only depends on the finite instances of a problem. -/
axiom SharpP_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {C D : CountingProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], C A = D A) → (SharpP.Mem C ↔ SharpP.Mem D)

end Lax366625.SharpPClosure
