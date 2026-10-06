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
title: FO(≤, PFP) definability is closed under first-order reductions
type: theorem
---
FO($\le$, PFP) definability travels backward along first-order reductions,
ordered first-order reductions and relativized ordered first-order
reductions, and reads a problem on its finite instances only. For a
relativized reduction the block is pulled back onto the definable domain,
the transfer of assignments being a bijection onto the assignments inside
the domain, which a deterministic iteration needs.
-/

namespace Lax134656.PartialFixedPointClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- FO(≤, PFP) definability travels backward along first-order reductions. -/
axiom pfpDefinable_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    FOReduction P Q → PFPDefinable Q → PFPDefinable P

/-- FO(≤, PFP) definability travels backward along ordered first-order
reductions. -/
axiom pfpDefinable_of_orderedReduction :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    OrderedFOReduction P Q → PFPDefinable Q → PFPDefinable P

/-- FO(≤, PFP) definability travels backward along relativized ordered
first-order reductions. -/
axiom pfpDefinable_of_relOrderedReduction :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    RelOrderedFOReduction P Q → PFPDefinable Q → PFPDefinable P

/-- FO(≤, PFP) definability only depends on the finite instances of a problem. -/
axiom pfpDefinable_congr_finite :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (PFPDefinable P ↔ PFPDefinable Q)

end Lax134656.PartialFixedPointClosure
