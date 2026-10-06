Polynomial space as a logically defined class, from the
descriptive-complexity library. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, and the
submissions on logarithmic space (lax-485149), polynomial time
(lax-535992), and the polynomial hierarchy (lax-564036). PSPACE is the class
of decision problems on finite structures definable in second-order logic
with a transitive closure, SO(TC): a walk on the assignments of a block of
relation variables, each step a first-order condition on two consecutive
assignments. No machine model enters the definition.

Unlike the logics of the classes below, SO(TC) does not need an order: a
walk can guess one into its own state, so the order-free logic defines the
same class. PSPACE is closed under complement, which is not syntactic and
goes through the deterministic walk that evaluates a quantified Boolean
formula; and it contains the polynomial hierarchy, level by level.

First-order logic with partial fixed points defines the same problems on
ordered structures, FO(≤, PFP) = SO(TC) = PSPACE, and contains the
inflationary logic. With the capture of polynomial time by inflationary
fixed points this gives the Abiteboul–Vianu theorem on ordered structures,
and the theorem itself is proved as well: on finite structures without an
order, the inflationary and the partial fixed-point logics define the same
problems exactly when PTIME = PSPACE.

Four problems are complete under the core's first-order reductions:
quantified Boolean formulas, reachability in a succinctly described
transition system, and acceptance by a Turing machine in bounded space,
deterministic or not; every problem of the class reduces to the
deterministic machine problem, so that PSPACE = NPSPACE in this setting.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's hardness laws and the submission's
own statements where they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
