The exponential classes as logically defined classes, from the
descriptive-complexity library. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, and the
submissions on logarithmic space (lax-485149), polynomial time
(lax-535992), the polynomial hierarchy (lax-564036), and polynomial space
(lax-134656).

An exponential expansion maps a finite ordered structure to a structure
whose points are the tagged assignments of a block of second-order
variables, its relations being defined by first-order sentences; its
universe is one exponential larger. A problem is definable in a class one
exponential up when some expansion turns it into a problem of the class.
EXPTIME and EXPSPACE are the classes defined by least and partial fixed
points read over an expansion, SO(≤, LFP) and SO(≤, PFP), and NEXPTIME is
NP read one exponential up. EXPTIME is PTIME and EXPSPACE is PSPACE read
one exponential up, these being the capture theorems of polynomial time and
space read on the expanded universe, and the order the expansion reads can
be removed from both definitions.

Reading a class one exponential up is monotone and commutes with
complement, so EXPTIME = coEXPTIME and EXPSPACE = coEXPSPACE, and the
inclusions carry up: PTIME ⊆ PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ EXPSPACE, with
NP ⊆ NEXPTIME, PSPACE ⊆ EXPSPACE, and PH ⊆ EXPTIME. Acceptance by
alternating Turing machines in bounded space is EXPTIME-complete, that is,
APSPACE = EXPTIME: membership reads acceptance as the game problem of
polynomial time over the configurations, and hardness runs a second-order
alternating game, which defines every problem of EXPTIME, on an alternating
machine.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the submission's own statements and those of
the submissions it requires where they compose. The library and its
documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
