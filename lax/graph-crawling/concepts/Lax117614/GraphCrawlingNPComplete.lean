import Lax904597.Classes
import Lax799700.Problems
import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem

/-!
---
title: Graph crawling is NP-complete
type: theorem
---
The graph crawling problem is NP-complete, in the sense of the NP core: it
is definable in existential second-order logic, and every problem of NP
reduces to it by an ordered first-order reduction. This is Proposition 4 of
Gauquier, Manolescu and Senellart (EDBT 2026) at unit page costs, hardness
coming from Set Cover by the paper's reduction.
-/

namespace Lax117614.GraphCrawlingNPComplete

open Lax904597.Classes Lax117614.GraphCrawlingProblem

/-- GraphCrawling is NP-complete (Proposition 4 of the paper). -/
axiom graphCrawling_NP_complete : NP.Complete GraphCrawling

end Lax117614.GraphCrawlingNPComplete
