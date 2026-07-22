/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Examples.ConjunctiveQueries

/-!
# Worked examples

Tutorial-style, domain-specific worked examples: each file walks through the
addition of a new problem domain to the library — vocabulary, semantics,
bundled `DecisionProblem`, NP membership, hardness, completeness — and is
meant to be read top to bottom as a template for new formalizations.

* `DescriptiveComplexity.Examples.ConjunctiveQueries`: Boolean conjunctive queries
  over relational databases — evaluation and containment, both NP-complete
  (Chandra–Merlin), with the Chandra–Merlin homomorphism theorem as the
  bridge between them.
-/
