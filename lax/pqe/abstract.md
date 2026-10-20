Probabilistic query evaluation, from the descriptive-complexity library: the
data complexity of computing the probability of a Boolean query over a
database whose facts are independent. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, the submissions
on counting problems, #P, and FP (lax-366625), on the parsimoniously
#P-complete problems (lax-280166), and on one-call and subtractive counting
reductions (lax-859101), and the submissions they require on logarithmic
space (lax-485149), polynomial time (lax-535992), and AC⁰ (lax-895169).

An instance carries certain and uncertain facts. With every uncertain fact
present with probability 1/2, the k uncertain facts give 2^k equally likely
possible worlds, and the probability of a query is the number of worlds in
which it holds divided by 2^k. With weights in the instance, each uncertain
fact is present with probability a/(a + c) for two weights written in
binary, and the probability of every first-order query is a ratio of two
numbers of #P: the weighted counts of the worlds of the query and of all
worlds.

The query h₀ = ∃x y, R(x) ∧ S(x, y) ∧ T(y) is hard, after Dalvi and Suciu:
counting its possible worlds is one-call #P-complete, by a parsimonious
reduction from #PP2DNF, and so is the numerator of its probability with
weights in the instance. On the same instances the hierarchical query ∃x y,
R(x) ∧ S(x, y) is easy: the numerator of its probability is in FP. The
weight of the worlds in which it fails is a product over the constants, and
the weight of those in which it holds is computed the same way, without a
subtraction, as a term of quantitative first-order logic. A concrete
probabilistic database, with its computed count and total, is encoded as a
weighted instance on which the probability of h₀ is their ratio.

The proofs are those of the library's development after version 1.2.2, on
its Lean 4.33 branch, sliced to what these statements use; they assume the
submission's own statements and those of the submissions it requires where
they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
