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
title: NL is closed under first-order reductions
type: theorem
---
Membership in NL travels backward along first-order reductions and along
ordered first-order reductions: if a problem reduces to a problem of NL, it
is in NL. Membership reads a problem on its finite instances only: two
problems with the same finite yes-instances are both in NL or both
outside.

The Krom shape of a definition survives the pullback along an interpretation.
-/

namespace Lax485149.NLClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- Membership in NL travels backward along first-order reductions. -/
axiom NL_mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, FOReduction P Q → NL.Mem Q → NL.Mem P

/-- Membership in NL travels backward along ordered first-order reductions. -/
axiom NL_mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {P : DecisionProblem L} {Q : DecisionProblem L'}, OrderedFOReduction P Q → NL.Mem Q → NL.Mem P

/-- Membership in NL only depends on the finite instances of a problem. -/
axiom NL_mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
  (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (NL.Mem P ↔ NL.Mem Q)

end Lax485149.NLClosure
