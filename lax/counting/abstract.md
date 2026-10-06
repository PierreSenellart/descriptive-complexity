Counting problems in descriptive complexity, from the descriptive-complexity
library: the classes #P and FP, defined by logics, their closure under
parsimonious first-order reductions, and their complete problems. It builds
on the NP core registered as lax-904597 and on the submissions on
logarithmic space (lax-485149), polynomial time (lax-535992), and AC⁰
(lax-895169).

A counting problem attaches an isomorphism-invariant natural number to every
finite structure, and a parsimonious reduction is a first-order
interpretation that preserves it. #P is the class of the numbers of
witnesses of existential second-order sentences over ordered structures,
after Saluja, Subrahmanyam, and Thakur, and it coincides with the quantitative
logic ΣQSO(FO) of Arenas, Muñoz, and Riveros. FP is the class defined by
quantitative first-order logic with least fixed points, equivalently by
least fixed points holding the binary digits of the number. Both classes are
closed under ordered parsimonious reductions, including relativized ones.

#SAT and the number of accepting runs of a nondeterministic Turing machine
are parsimoniously #P-complete, the latter giving #P as the class of the
problems reducing to it. The number written by a Boolean circuit, by unit
propagation on a Horn formula, and by a deterministic Turing machine are
parsimoniously FP-complete. NP is the class of the supports of #P, the
support of a parsimoniously #P-hard problem is NP-hard, and the support of a
problem of FP is in PTIME; so a parsimoniously #P-hard problem in FP, or one
whose support is in PTIME, gives NP ⊆ PTIME.

The proofs are those of the library's development after version 1.2.2, on
its Lean 4.33 branch, sliced to what these statements use; they assume the
submission's own statements and those of the submissions it requires where
they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
