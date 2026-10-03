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
title: Conjunctive query containment is NP-complete
type: theorem
---
Boolean conjunctive query containment is NP-complete in the sense of the NP
core: it reduces to evaluation by the Chandra–Merlin theorem, evaluating the
right query in the canonical database of the left one, and evaluation
reduces to it, a database being a variable-free query. This is the
containment half of Chandra and Merlin (1977).
-/

namespace Lax420092.ContainmentNPComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems
open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- CQContainment is NP-complete. -/
axiom cqContainment_NP_complete : NP.Complete CQContainment

end Lax420092.ContainmentNPComplete
