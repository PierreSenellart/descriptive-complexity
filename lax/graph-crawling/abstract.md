The NP-completeness of graph crawling, the decision problem behind focused Web
crawling in Gauquier, Manolescu and Senellart, “Efficient Crawling for
Scalable Web Data Acquisition” (EDBT 2026), formalized in the
descriptive-complexity library and stated on the archive together with the
paper's extended version (arXiv 2602.11874), whose Proposition 4 and its proof
are marked. A website is a directed graph of pages and hyperlinks with a root,
target pages and a budget; a crawl is a rooted subtree; the problem asks
whether some crawl reaches every target within the budget, at unit page costs.

The concepts state the problem both ways and relate them. On finite
structures, in the sense of the NP core registered as lax-904597, a website
graph is a structure with the links, the root, the targets and a marked set
whose cardinality is the budget, and GraphCrawling is NP-complete: membership
by an existential second-order definition, hardness by an ordered first-order
reduction from Set Cover, the paper's reduction, with Set Cover's
NP-completeness assumed from the catalog registered as lax-799700. On
packaged instances, the data a user handles, a computable encoder produces the
structure, faithfully and with neither padding nor compression, and a
computable decoder reads an instance back off any raw relation table with
exactly one root; graph crawling restricted to such well-formed websites is
NP-complete too.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's closure laws and the catalog's
statements for Set Cover, so the archive's proof network shows the reduction.
The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
