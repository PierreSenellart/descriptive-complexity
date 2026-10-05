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
title: FO(TC) definability is closed under first-order reductions
type: theorem
---
FO(TC) definability travels backward along first-order reductions and along
ordered first-order reductions: if $P$ reduces to an FO(TC) definable
problem, then $P$ is FO(TC) definable, a walk on the interpreted structure
being a walk on the base structure with the tags carried in the modes. It
reads a problem on its finite instances only.
-/

namespace Lax485149.TransitiveClosureClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- FO(TC) definability travels backward along first-order reductions. -/
axiom tcDefinable_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, FOReduction P Q → TCDefinable Q → TCDefinable P

/-- FO(TC) definability travels backward along ordered first-order
reductions. -/
axiom tcDefinable_of_orderedReduction :
  ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'},
    OrderedFOReduction P Q → TCDefinable Q → TCDefinable P

/-- FO(TC) definability only depends on the finite instances of a problem. -/
axiom tcDefinable_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (TCDefinable P ↔ TCDefinable Q)

end Lax485149.TransitiveClosureClosure
