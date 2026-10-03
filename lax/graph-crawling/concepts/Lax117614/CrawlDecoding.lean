import Lax904597.Classes
import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem
import Lax117614.CrawlInstances

/-!
---
title: Decoding, and well-formed graph crawling is NP-complete
type: theorem
---
The decoder is sound: an instance it reads off a presented website has a
crawl within budget exactly when the presented website graph is a
yes-instance of the graph crawling problem. It is total on well-formed
websites: every nonempty presented website with exactly one root decodes
to an instance. And well-formed graph crawling, whose yes-instances are
exactly the website graphs with one root and a cheap crawl, is NP-complete,
so the restriction the decoder needs loses nothing.
-/

namespace Lax117614.CrawlDecoding

open FirstOrder FirstOrder.Language Structure
open Lax904597.Problems Lax904597.Classes
open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem Lax117614.CrawlInstances

/-- The decoder is sound: an instance it reads off a presented website has a
crawl within budget exactly when the presented website graph is a
yes-instance of GraphCrawling. -/
axiom crawlDecode_sound : ∀ (S : FinPresentation siteGraph) (i : CrawlInstance),
  i ∈ crawlDecode S → (ConcreteCrawlHolds i ↔ GraphCrawling (Fin S.card))

/-- The decoder is total on well-formed websites: a nonempty presented website
with exactly one root decodes to an instance. -/
axiom crawlDecode_total : ∀ S : FinPresentation siteGraph,
  0 < S.card → Fin S.card ⊨ crawlWFSentence → (crawlDecode S).isSome

/-- The yes-instances of WFGraphCrawling are exactly the website graphs with
exactly one root satisfying `HasCheapCrawl`. -/
axiom wfGraphCrawling_iff : ∀ (A : Type) [siteGraph.Structure A],
  WFGraphCrawling A ↔ (A ⊨ crawlWFSentence ∧ HasCheapCrawl A)

/-- WFGraphCrawling is NP-complete: the restriction to well-formed websites
loses nothing. -/
axiom wfGraphCrawling_NP_complete : NP.Complete WFGraphCrawling

end Lax117614.CrawlDecoding
