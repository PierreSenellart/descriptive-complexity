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
title: The Immerman–Szelepcsényi theorem: FO(TC) is closed under complement
type: theorem
---
If a decision problem $P$ is FO(TC) definable, then so is its complement
$P^c$. This is the Immerman–Szelepcsényi theorem in logical form: the
absence of a path between source and target nodes of a definable graph on
tuples of an ordered structure is witnessed by a walk that counts,
inductively on the distance, the nodes reachable from the sources.
-/

namespace Lax485149.ImmermanSzelepcsenyi

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- The complement of an FO(TC) definable problem is FO(TC) definable. -/
axiom tcDefinable_compl : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  TCDefinable P → TCDefinable (DecisionProblem.compl P)

end Lax485149.ImmermanSzelepcsenyi
