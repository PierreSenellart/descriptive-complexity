Completeness without a class, from the descriptive-complexity library: the
degree of a decision problem under first-order reductions, and the graph
isomorphism problems, which are complete for a degree and, conjecturally,
for no class defined by a logic. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, and the
submissions on logarithmic space, polynomial time, the polynomial hierarchy
and recursive enumerability.

The degree of a problem is the class of the problems that reduce to it by an
ordered first-order reduction, with the hardness of the NP core. A problem
is complete for its own degree, completeness for a degree is mutual
reducibility, and mutually reducible problems have the same degree. The
construction is checked against the classes that have a complete problem:
NP is the degree of SAT, coNP of TAUT, PTIME of HORN-SAT, NL of 2SAT and RE
of FINSAT, so that hardness for one of these problems is hardness for its
class.

GI is the degree of Graph Isomorphism, the problem of two simple graphs. It
is contained in NP. Digraph Isomorphism and the isomorphism of directed
acyclic graphs, given with a witness of acyclicity since acyclicity is not
first-order definable, are GI-complete, and GI is also the degree of the
directed problem.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the submission's own statements and those of
the submissions it requires where they compose. The library and its
documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
