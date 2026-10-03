A catalog of thirty NP-complete decision problems on finite structures,
from the descriptive-complexity library, built on the NP core registered
as lax-904597: the twenty-one problems of Karp (SAT itself being the core's),
the satisfiability variants the reductions run on (not-all-equal SAT and its
width-three form, 1-in-SAT), and classical companions: Independent Set,
Dominating Set, Subgraph Isomorphism, Set Splitting, the edge-weighted
Steiner tree, 3-colorability and $k$-colorability for every $k \geq 3$.
Each problem is a concept: its vocabulary, its defining
property, the decision problem it gives, and three claims, that the property
is isomorphism-invariant, that the problem's yes-instances are exactly the
structures satisfying the property, and that the problem is NP-complete in
the core's sense, with NP the class of problems definable in existential
second-order logic and hardness by first-order reductions.

The proofs assume the statements of the core they rest on, Cook–Levin and
the closure laws of NP, and nothing else: membership is an
existential second-order definition or a first-order reduction to a problem
already in NP, and hardness is a first-order reduction, plain, ordered or
relativized, from a problem already known hard. The archive's proof network
is therefore the reduction tree of the catalog, one edge per reduction, with
SAT at its root.

Thresholds are carried by the instances in unary, as the cardinality of a
marked set, so that no order is needed to state a problem; the four
problems of Karp's list that are polynomial under that encoding (Knapsack,
Partition, 0-1 integer programming, job sequencing) are written in binary,
with a linear order on bit positions folded into their yes-instances.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; the library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models;
the design and the statements are the author's.
