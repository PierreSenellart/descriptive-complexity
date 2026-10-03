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
title: Conjunctive query evaluation is NP-complete
type: theorem
---
Boolean conjunctive query evaluation, in combined complexity, is NP-complete
in the sense of the NP core: it is definable in existential second-order
logic, guessing the valuation, and 3-colorability reduces to it by a
quantifier-free first-order reduction, the query of a graph being evaluated
in the triangle. This is the evaluation half of Chandra and Merlin (1977).
-/

namespace Lax420092.EvaluationNPComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- CQEval is NP-complete. -/
axiom cqEval_NP_complete : NP.Complete CQEval

end Lax420092.EvaluationNPComplete
