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
title: FO(IFP) ⊆ FO(PFP)
type: theorem
---
Every problem definable with inflationary fixed points is definable with
partial fixed points, on ordered structures and without an order:
disjoining each variable's own atom onto its step formula turns an
inflationary induction into a partial one with the same stages. And an
order-free definition is an ordered one that does not use the order, for
both logics.
-/

namespace Lax134656.InflationaryInPartial

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Every FO(≤, IFP) definable problem is FO(≤, PFP) definable. -/
axiom ifpDefinable_pfpDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  IFPDefinable P → PFPDefinable P

/-- Every order-free FO(IFP) definable problem is order-free FO(PFP) definable. -/
axiom ifpDefinableFree_pfpDefinableFree :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  IFPDefinableFree P → PFPDefinableFree P

/-- Every order-free FO(IFP) definable problem is FO(≤, IFP) definable. -/
axiom ifpDefinableFree_ifpDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  IFPDefinableFree P → IFPDefinable P

/-- Every order-free FO(PFP) definable problem is FO(≤, PFP) definable. -/
axiom pfpDefinableFree_pfpDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  PFPDefinableFree P → PFPDefinable P

end Lax134656.InflationaryInPartial
