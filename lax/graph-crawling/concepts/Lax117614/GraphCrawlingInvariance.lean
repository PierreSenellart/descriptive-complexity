import Lax904597.Classes
import Lax799700.Problems
import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem

/-!
---
title: Invariance and characterization of graph crawling
type: lemma
---
Having a cheap crawl is invariant under isomorphism of website graphs, and
a website graph is a yes-instance of the graph crawling problem exactly
when it has a cheap crawl.
-/

namespace Lax117614.GraphCrawlingInvariance

open FirstOrder

open FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes Lax799700.Problems
open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem

/-- The property `HasCheapCrawl` is isomorphism-invariant. -/
axiom hasCheapCrawl_iso : ∀ {A B : Type} [siteGraph.Structure A] [siteGraph.Structure B],
  (A ≃[siteGraph] B) → (HasCheapCrawl A ↔ HasCheapCrawl B)

/-- The yes-instances of GraphCrawling are exactly the website graphs
satisfying `HasCheapCrawl`. -/
axiom graphCrawling_iff : ∀ (A : Type) [siteGraph.Structure A],
  GraphCrawling A ↔ HasCheapCrawl A

end Lax117614.GraphCrawlingInvariance
