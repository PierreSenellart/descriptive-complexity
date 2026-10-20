import Mathlib.ModelTheory.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Even
import Lax904597.Problems
import Lax485149.Problems

/-!
---
title: EVEN, the parity of the universe
type: definition
---
An instance is a bare finite set, a structure over the empty vocabulary. It
is a yes-instance of EVEN when its number of elements is even; EVEN is the
decision problem of the structures isomorphic to such an instance, that is,
of the sets of even size.
-/

namespace Lax945089.Even

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax485149.Problems

/-- EVEN: does the universe have an even number of elements? -/
def EVEN : DecisionProblem Language.empty :=
  DecisionProblem.ofPred fun A _ => Even (Nat.card A)

end Lax945089.Even
