/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Examples.ConjunctiveQueries
import DescriptiveComplexity.Examples.GraphCrawling

/-!
# Worked examples

Tutorial-style, domain-specific worked examples: each file walks through the
addition of a new problem domain to the library, in the order a user meets
it – the concrete problem in their own formalism, its machine-checked
encoding (size bounds discharged at construction), the abstract vocabulary
and semantics, the faithfulness theorem tying the two, and then NP
membership, hardness and completeness of the encoded variant – and is meant
to be read top to bottom as a template for new formalizations.

* `DescriptiveComplexity.Examples.ConjunctiveQueries`: Boolean conjunctive queries
  over relational databases – evaluation and containment, both NP-complete
  ([Chandra & Merlin 1977][chandra1977optimal]), with the Chandra–Merlin
  homomorphism theorem as the
  bridge between them. Order-free, quantifier-free reductions; the file
  opens with the concrete list-of-atoms instances and their encoding.
* `DescriptiveComplexity.Examples.GraphCrawling`: Web data acquisition as graph
  crawling – NP-complete
  ([Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2]), by the
  paper's reduction from Set Cover. Read second: it exercises what the CQ
  tutorial does not – a cardinality threshold, a reachability certificate,
  an *ordered* FO reduction, and a single-sorted concrete encoding.
-/
