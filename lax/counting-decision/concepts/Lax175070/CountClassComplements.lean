import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Interpretations
import Lax904597.Machines
import Lax564036.Hierarchy
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax366625.CountingRuns
import Lax175070.CountDefinability
import Lax175070.SelectedSat

/-!
---
title: ⊕P and PP are closed under complement
type: theorem
---
⊕P and PP are closed under complement. A first kernel is paired with a
kernel that always holds, which adds one witness: a number is even exactly
when its successor is odd, and $c \le d$ exactly when $c < d + 1$, with the
two counts swapped. Whether C$_=$P is closed under complement is open.
-/

namespace Lax175070.CountClassComplements

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- ⊕P is closed under complement. -/
axiom compl_mem_parityP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    ParityP.Mem P → ParityP.Mem (DecisionProblem.compl P)

/-- PP is closed under complement. -/
axiom compl_mem_PP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    PP.Mem P → PP.Mem (DecisionProblem.compl P)

end Lax175070.CountClassComplements
