The two classical decision problems about Boolean conjunctive queries,
evaluation and containment, from the descriptive-complexity library's
worked example on database theory, built on the NP core registered as
lax-904597 and on the catalog registered as lax-799700. The schema is a
single binary relation, that of graph databases, which loses no
complexity-theoretic generality. An evaluation instance is a query and a
database over a shared universe, a containment instance a pair of queries
over shared constants.

Both problems are NP-complete in the core's sense, the results of Chandra
and Merlin (1977): evaluation is definable in existential second-order
logic and 3-colorability reduces to it by a quantifier-free first-order
reduction, assumed from the catalog's statement; containment reduces to
evaluation by the Chandra–Merlin theorem in reduction form, containment
holding exactly when the right query maps homomorphically into the
canonical database of the left one, and evaluation reduces to containment,
a database being a variable-free query. The Chandra–Merlin theorem itself is
a statement of the submission, as are the two reductions, so the archive's
proof network shows containment's completeness resting on evaluation's.

As in the graph-crawling submission, the problem is also stated on packaged
instances: concrete queries and databases, encoded faithfully and
size-honestly, and decoded back from any raw relation table with a constant,
with evaluation on such well-formed instances NP-complete too.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
