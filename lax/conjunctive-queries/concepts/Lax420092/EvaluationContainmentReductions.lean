import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Classes
import Lax799700.Problems
import Lax420092.QueryDatabases
import Lax420092.Evaluation
import Lax420092.QueryPairs
import Lax420092.PackagedInstances

/-!
---
title: Evaluation and containment reduce to each other
type: theorem
---
Containment reduces to evaluation by a first-order reduction, the Chandra–Merlin
theorem in reduction form, and evaluation reduces to containment by a
first-order reduction, a database being a conjunctive query without
variables.
-/

namespace Lax420092.EvaluationContainmentReductions

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- Containment reduces to evaluation. -/
axiom cqContainment_reduces_to_cqEval : Nonempty (FOReduction CQContainment CQEval)

/-- Evaluation reduces to containment. -/
axiom cqEval_reduces_to_cqContainment : Nonempty (FOReduction CQEval CQContainment)

end Lax420092.EvaluationContainmentReductions
