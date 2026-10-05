import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.ClassNL
import Lax485149.ClassL
import Lax535992.HornFragment
import Lax535992.LeastFixedPoint
import Lax535992.InflationaryFixedPoint
import Lax535992.HornSat
import Lax535992.CircuitValue
import Lax535992.Game
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME

/-!
---
title: PTIME is closed under first-order reductions
type: theorem
---
Membership in PTIME travels backward along first-order reductions, along
ordered first-order reductions and along relativized ordered first-order
reductions: if a problem reduces to a problem of PTIME, it is in PTIME. The
Horn shape of a definition survives the pullback along an interpretation,
which rewrites the guards only. Membership reads a problem on its finite
instances only: two problems with the same finite yes-instances are both in
PTIME or both outside.
-/

namespace Lax535992.PTIMEClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat Lax904597.Machines
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.ClassNL Lax485149.ClassL
open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint
open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines
open Lax535992.ClassPTIME

/-- Membership in PTIME travels backward along first-order reductions. -/
axiom PTIME_mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, FOReduction P Q → PTIME.Mem Q → PTIME.Mem P

/-- Membership in PTIME travels backward along ordered first-order reductions. -/
axiom PTIME_mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    OrderedFOReduction P Q → PTIME.Mem Q → PTIME.Mem P

/-- Membership in PTIME travels backward along relativized ordered first-order
reductions. -/
axiom PTIME_mem_of_relOrderedReduction :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    RelOrderedFOReduction P Q → PTIME.Mem Q → PTIME.Mem P

/-- Membership in PTIME only depends on the finite instances of a problem. -/
axiom PTIME_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (PTIME.Mem P ↔ PTIME.Mem Q)

end Lax535992.PTIMEClosure
