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
title: Translations between SO-Krom and FO(TC)
type: theorem
---
If a problem $P$ is SO-Krom definable, then its complement $P^c$ is FO(TC)
definable: a Krom program instantiated on a structure is a 2-CNF, which is
unsatisfiable exactly when the goal clause fires or some literal reaches its
negation and back in the implication graph, a reachability condition.
Conversely, if $P$ is FO(TC) definable, then $P^c$ is SO-Krom definable:
the program guesses a set of nodes containing the targets and closed under
predecessors, and rejects when the set contains a source.
-/

namespace Lax485149.KromAndTransitiveClosure

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- The complement of an SO-Krom definable problem is FO(TC) definable. -/
axiom tcDefinable_compl_of_sigmaSOKromDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  SigmaSOKromDefinable P → TCDefinable (DecisionProblem.compl P)

/-- The complement of an FO(TC) definable problem is SO-Krom definable. -/
axiom sigmaSOKromDefinable_compl_of_tcDefinable :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  TCDefinable P → SigmaSOKromDefinable (DecisionProblem.compl P)

end Lax485149.KromAndTransitiveClosure
