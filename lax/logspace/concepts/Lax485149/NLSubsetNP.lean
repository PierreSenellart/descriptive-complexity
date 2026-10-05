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
title: NL ⊆ NP
type: theorem
---
Every problem of NL is in NP: every SO-Krom definable problem is definable
in existential second-order logic. The inclusion is not syntactic, the
guards of a Krom program being over the ordered expansion of the vocabulary
while a $\Sigma_1$ definition is order-free. It goes through complete
problems: every problem of NL reduces to 2SAT, which a Horn program
defines, and every problem a Horn program defines reduces to HORN-SAT,
which is in NP.
-/

namespace Lax485149.NLSubsetNP

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder
open Lax904597.Classes Lax904597.Sat
open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment
open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure
open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability
open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- NL is contained in NP. -/
axiom NL_subset_NP : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NL.Mem P → NP.Mem P

end Lax485149.NLSubsetNP
