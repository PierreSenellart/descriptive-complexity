Complete problems for NEXPTIME and EXPSPACE, from the descriptive-complexity
library. It builds on the exponential classes registered as lax-480241, and
through them on the NP core lax-904597, the catalog of NP-complete problems
lax-799700, and the submissions on logarithmic space (lax-485149),
polynomial time (lax-535992), the polynomial hierarchy (lax-564036), and
polynomial space (lax-134656).

A wide machine is a Turing machine described by a finite structure whose
tape cells and time steps are the subsets of the universe, ordered as binary
numbers: an instance of size $n$ describes a machine with $2^n$ cells and
$2^n$ steps. Wide acceptance, the machine accepting within its $2^n$ steps,
is in NEXPTIME, and its form with a regular input channel, laid out along the
addresses, is NEXPTIME-complete. Wide acceptance in space, the machine
accepting within its $2^n$ cells with no bound on time, is
EXPSPACE-complete, deterministic or not. Membership reads a wide machine as
an ordinary one over an exponential expansion; hardness lays the computation
of a problem of the class out along the addresses.

The same reading gives tilings one exponential up, the rows of a tiling
being the configurations of a wide machine: tiling the square of side $2^n$
is NEXPTIME-complete, and tiling the corridor of width $2^n$ and unbounded
height is EXPSPACE-complete. Each wide acceptance problem has yes-instances,
so that none of the completeness results is about an empty problem.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the submission's own statements and those of
the submissions it requires where they compose. The library and its
documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
