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
title: The Abiteboul–Vianu theorem
type: theorem
---
On finite structures without an order, the inflationary and the partial
fixed-point logics define the same problems if and only if PTIME = PSPACE.
If the classes are equal, an order-free partial definition is relativized
to an order, captured in PSPACE = PTIME, and brought back. Conversely, an
order-free FO(PFP) computation with $k$ variables is invariant under the
equivalence of $k$-tuples by the $k$-pebble game; it therefore runs on the
structure of the equivalence classes, which carries a linear order
definable by an inflationary induction, and there the equality of the
logics on ordered structures applies. The proof follows the machine-free
route of Dawar, Lindell, and Weinstein and of Ebbinghaus and Flum.
-/

namespace Lax134656.AbiteboulVianu

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Machines
open Lax485149.Problems Lax485149.Complement
open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME
open Lax564036.Hierarchy
open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure
open Lax134656.PartialFixedPoint
open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Order-free FO(IFP) = order-free FO(PFP) exactly when PTIME = PSPACE. -/
axiom ifpDefinableFree_eq_pfpDefinableFree_iff_ptime_eq_pspace :
  (∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    IFPDefinableFree P ↔ PFPDefinableFree P) ↔ PTIME = PSPACE

end Lax134656.AbiteboulVianu
