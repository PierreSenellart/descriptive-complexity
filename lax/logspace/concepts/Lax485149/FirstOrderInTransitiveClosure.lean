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
title: FO(≤) ⊆ FO(DTC) ⊆ FO(TC)
type: theorem
---
Every FO($\le$) definable problem is FO(DTC) definable, by a walk that
takes no step, and every FO(DTC) definable problem is FO(TC) definable, the
determinization of a specification being a specification. Hence
$\mathrm{FO}(\le) \subseteq \mathrm{FO(DTC)} \subseteq \mathrm{FO(TC)}$
as classes of problems on finite structures.
-/

namespace Lax485149.FirstOrderInTransitiveClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- Every FO(≤) definable problem is FO(DTC) definable. -/
axiom foDefinable_dtcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  FODefinable P → DTCDefinable P

/-- Every FO(DTC) definable problem is FO(TC) definable. -/
axiom dtcDefinable_tcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  DTCDefinable P → TCDefinable P

/-- Every FO(≤) definable problem is FO(TC) definable. -/
axiom foDefinable_tcDefinable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  FODefinable P → TCDefinable P

end Lax485149.FirstOrderInTransitiveClosure
