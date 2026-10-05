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
title: REACHd is L-complete
type: theorem
---
REACHd, deterministic reachability, is L-complete under first-order
reductions. It is FO(DTC) definable, by the determinization of the
specification that defines REACH, and every FO(DTC) definable problem
reduces to it by an ordered first-order reduction that builds the graph of
the determinized specification.
-/

namespace Lax485149.ReachdLComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- REACHd is a single deterministic transitive closure. -/
axiom reachd_dtcDefinable : DTCDefinable REACHd

/-- Every FO(DTC) definable problem reduces to REACHd. -/
axiom reachd_hard_of_dtcDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  DTCDefinable P → Nonempty (OrderedFOReduction P REACHd)

/-- REACHd is L-complete. -/
axiom reachd_LOGSPACE_complete : LOGSPACE.Complete REACHd

end Lax485149.ReachdLComplete
