import Lax904597.Classes
import Lax904597.Sat

/-!
---
title: The Cook–Levin theorem, by first-order reductions
type: theorem
---
SAT is NP-complete, with NP read as existential second-order definability
and hardness as cofinal hardness under relativized ordered first-order
reductions. The two halves are stated in their sharper forms as well: SAT is
$\Sigma_1$-definable, by the sentence that guesses a truth assignment and
checks, in first-order logic, that every clause contains a true literal; and
every $\Sigma_1$-definable problem has a plain ordered first-order reduction
to SAT. The reduction is generic and machine-free: in the manner of
Dahlhaus, it rewrites the first-order kernel of the defining sentence into
clauses over the elements of the input structure, with the guessed relations
as propositional variables.

Since ordered first-order reductions are computable in $\mathrm{AC}^0$, the
hardness half is stronger than hardness under polynomial-time reductions.
-/

namespace Lax904597.CookLevin

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.SecondOrder Lax904597.Classes
  Lax904597.Sat

/-- SAT is `Σ₁`-definable: SAT is in NP. -/
axiom sat_sigmaSODefinable : SigmaSODefinable 1 SAT

/-- Every `Σ₁`-definable problem has an ordered first-order reduction to
SAT. -/
axiom sat_hard_of_sigmaSODefinable : ∀ {L : Language.{0, 0}} [L.IsRelational]
  (Q : DecisionProblem L), SigmaSODefinable 1 Q → Nonempty (OrderedFOReduction Q SAT)

/-- The Cook–Levin theorem: SAT is NP-complete. -/
axiom SAT_NP_complete : NP.Complete SAT

end Lax904597.CookLevin
