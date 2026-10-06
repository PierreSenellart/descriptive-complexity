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
title: Membership from two problems of #P
type: theorem
---
If two counting problems $C$ and $D$ are in #P, a decision problem $P$ such
that, on nonempty finite structures, $S(C(A), D(A))$ holds and $P(A)$ holds
exactly when $R(C(A), D(A))$, is in the class of $S$ and $R$. The witnesses
of the two definitions of #P are the witnesses of the class, read over the
ordered expansion.
-/

namespace Lax175070.CountClassMembership

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- A problem of the class, from two counting problems of #P. -/
axiom mem_countClass_of_sharpP :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {S R : ℕ → ℕ → Prop} {C D : CountingProblem L},
    SharpP.Mem C → SharpP.Mem D → ∀ {P : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      S (C A) (D A) ∧ (P A ↔ R (C A) (D A))) → (countClass S R).Mem P

end Lax175070.CountClassMembership
