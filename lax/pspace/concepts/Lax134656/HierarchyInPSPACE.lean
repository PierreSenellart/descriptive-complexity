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
title: PH ⊆ PSPACE
type: theorem
---
NP, polynomial time, every level $\Sigma_k^p$ and $\Pi_k^p$ of the
polynomial hierarchy, and hence PH, are contained in PSPACE. An existential
block of second-order quantifiers is a walk that guesses its state and
takes no step, and a walk can guess a block into its own state and never
touch it again, so an existential block in front of an SO(TC) condition is
again one; universal blocks are handled by complementing twice, PSPACE being
closed under complement.
-/

namespace Lax134656.HierarchyInPSPACE

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- NP is contained in PSPACE. -/
axiom NP_subset_PSPACE : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NP.Mem P → PSPACE.Mem P

/-- PTIME is contained in PSPACE. -/
axiom PTIME_subset_PSPACE : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PTIME.Mem P → PSPACE.Mem P

/-- Every `Σ` level is contained in PSPACE. -/
axiom sigmaP_subset_PSPACE :
  ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  (SigmaP k).Mem P → PSPACE.Mem P

/-- Every `Π` level is contained in PSPACE. -/
axiom piP_subset_PSPACE : ∀ (k : ℕ) {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  (PiP k).Mem P → PSPACE.Mem P

/-- PH is contained in PSPACE. -/
axiom PH_subset_PSPACE : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  PH.Mem P → PSPACE.Mem P

end Lax134656.HierarchyInPSPACE
