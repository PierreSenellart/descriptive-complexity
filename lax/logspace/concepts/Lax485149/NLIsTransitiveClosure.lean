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
title: NL = FO(TC)
type: theorem
---
A decision problem is in NL, that is, SO-Krom definable, if and only if it
is FO(TC) definable. Equivalently, since FO(TC) is closed under complement,
a problem is in NL if and only if its complement is FO(TC) definable.
-/

namespace Lax485149.NLIsTransitiveClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- FO(TC) definability is membership in NL. -/
axiom tcDefinable_iff_mem_NL : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  TCDefinable P ↔ NL.Mem P

/-- A problem is in NL exactly when its complement is FO(TC) definable. -/
axiom mem_NL_iff_tcDefinable_compl :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NL.Mem P ↔ TCDefinable (DecisionProblem.compl P)

end Lax485149.NLIsTransitiveClosure
