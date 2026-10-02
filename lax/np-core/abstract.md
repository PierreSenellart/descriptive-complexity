Two forms of the NP-completeness of SAT from the descriptive-complexity
library, with the definitions they rest on: a decision problem is an
isomorphism-invariant predicate on the finite structures of a relational
vocabulary; a reduction is a first-order interpretation, with tags for
disjoint copies and, in the ordered variant, a linear order on the input;
a complexity class is a set of problems closed under reductions, and NP is
the class of problems definable in existential second-order logic.

**SAT is NP-complete** (SAT_NP_complete): SAT belongs to NP, and every problem in NP reduces to
SAT by an ordered first-order reduction, the generic Tseitin reduction
applied to the problem's existential second-order definition.

**The machine form** (SAT_complete_for_ntmAccept): the Cook–Levin theorem in the form the
machine-based mechanizations prove, SAT complete for the class that
nondeterministic machine acceptance defines. The library has no model of
computation: machine acceptance is one more decision problem, whose
instances are finite structures describing a nondeterministic Turing
machine, its input and its step budget, and "accepted by a polynomial-time
machine" means "reduces to that problem by an ordered first-order
reduction". SAT reduces to machine acceptance, and every problem that
reduces to machine acceptance reduces to SAT.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; the library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models;
the design and the statements are the author's.
