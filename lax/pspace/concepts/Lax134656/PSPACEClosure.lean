import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Machines
import Lax485149.Problems
import Lax485149.Complement
import Lax535992.InflationaryFixedPoint
import Lax535992.DeterministicMachines
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SuccinctReach
import Lax134656.SpaceBoundedMachines
import Lax134656.ClassPSPACE

/-!
---
title: PSPACE is closed under first-order reductions
type: theorem
---
Membership in PSPACE travels backward along first-order reductions and
along ordered first-order reductions: if a problem reduces to a problem of
PSPACE, it is in PSPACE. A state of the walk being an assignment of a
block, the states of the pulled-back walk are the states of the original
walk on the interpreted structure. Membership reads a problem on its finite
instances only.
-/

namespace Lax134656.PSPACEClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Membership in PSPACE travels backward along first-order reductions. -/
axiom PSPACE_mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, FOReduction P Q → PSPACE.Mem Q → PSPACE.Mem P

/-- Membership in PSPACE travels backward along ordered first-order reductions. -/
axiom PSPACE_mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    OrderedFOReduction P Q → PSPACE.Mem Q → PSPACE.Mem P

/-- Membership in PSPACE only depends on the finite instances of a problem. -/
axiom PSPACE_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (PSPACE.Mem P ↔ PSPACE.Mem Q)

end Lax134656.PSPACEClosure
