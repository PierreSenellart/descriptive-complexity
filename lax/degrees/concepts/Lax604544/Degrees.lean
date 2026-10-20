import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Classes

/-!
---
title: The degree of a problem
type: definition
---
The degree of a decision problem $Q_0$ is the class of the problems that
reduce to $Q_0$ by an ordered first-order reduction, with the cofinal
hardness of the NP core. It is a complexity class defined by no logic and no
machine, only by a problem: a problem is complete for the degree of $Q_0$
when it has, under first-order reductions, exactly the difficulty of
$Q_0$.
-/

namespace Lax604544.Degrees

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes

/-- **The degree of a problem**: the problems that ordered first-order reduce
to `Q₀`, as a complexity class with cofinal hardness. -/
def below {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q₀ : DecisionProblem L₀) : ComplexityClass :=
  ComplexityClass.ofMem fun P => Nonempty (OrderedFOReduction P Q₀)

end Lax604544.Degrees
