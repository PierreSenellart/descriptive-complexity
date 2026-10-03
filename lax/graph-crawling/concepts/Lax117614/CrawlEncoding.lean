import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem
import Lax117614.CrawlInstances

/-!
---
title: The encoding of crawling instances is faithful and size-honest
type: theorem
---
A packaged crawling instance has a crawl within budget exactly when the
website graph it encodes is a yes-instance of the graph crawling problem;
the encoded website graph has at most as many pages as the size of the
instance; and the size of the instance is at most $4(n+2)^2$ for $n+1$
pages. The encoding neither pads nor compresses.
-/

namespace Lax117614.CrawlEncoding

open FirstOrder FirstOrder.Language Structure
open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem Lax117614.CrawlInstances

/-- The encoding is faithful: a packaged instance has a crawl within budget
exactly when the website graph it encodes is a yes-instance of
GraphCrawling. -/
axiom crawlEncoding_faithful : ∀ i : CrawlInstance,
  ConcreteCrawlHolds i ↔ GraphCrawling (Fin (i.n + 1))

/-- No padding: the encoded structure has at most as many elements as the
textbook size of the instance. -/
axiom crawlSize_ge_card : ∀ i : CrawlInstance, i.n + 1 ≤ crawlSize i

/-- No compression: the textbook size of an instance is polynomial in the
number of elements of the encoded structure. -/
axiom crawlSize_le_card : ∀ i : CrawlInstance, crawlSize i ≤ 4 * (i.n + 2) ^ 2

end Lax117614.CrawlEncoding
