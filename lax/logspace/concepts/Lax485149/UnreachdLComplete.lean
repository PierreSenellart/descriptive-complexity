import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax904597.Sat
import Lax485149.Problems
import Lax485149.Complement
import Lax485149.SecondOrderAtoms
import Lax485149.KromFragment
import Lax485149.TransitiveClosure
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.Reachability
import Lax485149.DeterministicReachability
import Lax485149.TwoSat
import Lax485149.ClassNL
import Lax485149.ClassL

/-!
---
title: UNREACHd is L-complete
type: theorem
---
UNREACHd, the complement of REACHd, is L-complete under first-order
reductions. A deterministic walk on a finite graph that does not arrive
within as many steps as there are vertices never arrives, so non-arrival is
itself witnessed by a deterministic walk that counts its steps; no analogue
of inductive counting is needed.
-/

namespace Lax485149.UnreachdLComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- UNREACHd is L-complete. -/
axiom unreachd_LOGSPACE_complete : LOGSPACE.Complete UNREACHd

end Lax485149.UnreachdLComplete
