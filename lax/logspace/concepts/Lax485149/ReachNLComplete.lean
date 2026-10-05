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
title: REACH is NL-complete
type: theorem
---
REACH is NL-complete under first-order reductions. It is FO(TC) definable,
by a specification of arity one with a single mode that walks along the
edges from the marked sources to the marked targets, and every FO(TC)
definable problem reduces to it by an ordered first-order reduction that
builds the graph of the specification, its nodes the tagged tuples.
-/

namespace Lax485149.ReachNLComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- REACH is a single transitive closure. -/
axiom reach_tcDefinable : TCDefinable REACH

/-- Every FO(TC) definable problem reduces to REACH. -/
axiom reach_hard_of_tcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  TCDefinable P → Nonempty (OrderedFOReduction P REACH)

/-- REACH is NL-complete. -/
axiom reach_NL_complete : NL.Complete REACH

end Lax485149.ReachNLComplete
