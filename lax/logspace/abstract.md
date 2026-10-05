Logarithmic space as two logically defined classes, from the
descriptive-complexity library, built on the NP core registered as
lax-904597. NL is the class of decision problems on finite structures
definable in the Krom fragment of existential second-order logic, and L the
class of those definable in first-order logic with a deterministic
transitive closure, both on ordered structures and invariantly in the
order; these are the logics that capture nondeterministic and deterministic
logarithmic space, by theorems of Grädel and Immerman. No machine model
enters the definitions.

The central result is the Immerman–Szelepcsényi theorem in logical form:
first-order logic with a transitive closure, FO(TC), is closed under
complement, by a walk that counts inductively the tuples reachable from the
sources. Two translations relate the Krom fragment to FO(TC), each
exchanging a problem with its complement, so that NL = FO(TC) and NL = coNL.
L is closed under complement as well, without inductive counting, and
FO(≤) ⊆ FO(DTC) ⊆ FO(TC), whence L ⊆ NL; NL ⊆ NP.

Five problems are complete under the core's first-order reductions:
reachability in directed graphs, its complement and the satisfiability of
CNF formulas of width two for NL, by generic reductions that build the
graph of a transitive closure or instantiate a Krom program; deterministic
reachability, along the edges that are alone in leaving their source, and
its complement for L.

Both classes are then related to a machine model: a problem is in NL
exactly when it is accepted by a two-way multihead automaton on ordered
structures, with quantifier-free tests and no work tape, and in L exactly
when the automaton can be taken deterministic.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's hardness laws and the submission's
own statements where they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
