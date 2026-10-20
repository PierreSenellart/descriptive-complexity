Counting reductions beyond parsimony, from the descriptive-complexity
library: one-call and subtractive reductions, and the counting problems that
are complete for #P under them but not known to be under parsimonious ones.
It builds on the submission on counting problems, #P, and FP (lax-366625)
and on the catalog of parsimoniously #P-complete problems lax-280166. These
build in turn on the NP core registered as lax-904597, the catalog of
NP-complete problems lax-799700, and the submissions on logarithmic space
(lax-485149), polynomial time (lax-535992), and AC⁰ (lax-895169).

A one-call reduction is a relativized first-order interpretation followed by
a post-processing term, which computes the count of the source from the
answer of the oracle with polynomial terms, powers of two, and the
arithmetic of natural numbers: a restricted form of the metric reductions of
Krentel, in the statement of Faliszewski and Hemaspaandra. One-call
reductions compose, and a parsimoniously #P-complete problem is one-call
#P-complete. Since #P is presumably not closed under them, as Toda and
Watanabe showed, completeness is for the one-call closure of #P. Subtractive
reductions, after Durand, Hermann, and Kolaitis, are chains of strong
subtractive and parsimonious steps; #P is closed under them, and a
parsimoniously #P-complete problem is #P-complete.

#DNF is #P-complete under subtractive reductions and one-call #P-complete,
although its support is easy: the models of a CNF formula are all the
assignments minus the models of the DNF formula of its negation, as Durand,
Hermann, and Kolaitis showed and as Durand, Haak, Kontinen, and Vollmer used
for #AC⁰. #NAE-SAT, #Set Splitting, #3-Colorability, counting all
independent sets and all vertex covers, #2SAT, #HORN-SAT, #Monotone-2SAT,
#BIS, and #PP2DNF are one-call #P-complete; the proofs follow the library's
tree of reductions, from #SAT and #Independent Set.

The proofs are those of the library's development after version 1.2.2, on
its Lean 4.33 branch, sliced to what these statements use; they assume the
submission's own statements and those of the submissions it requires where
they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
