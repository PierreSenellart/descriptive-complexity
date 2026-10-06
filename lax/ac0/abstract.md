AC⁰ as a logic, from the descriptive-complexity library, built on the NP
core registered as lax-904597 and on the classes of logarithmic space and
polynomial time, lax-485149 and lax-535992. A decision problem on finite
structures is AC⁰ definable when one first-order sentence with the order,
addition and multiplication of ranks, FO(≤, +, ×), decides it on every
ordered instance, invariantly in the order: the logic that defines the
problems of uniform AC⁰, by theorems of Barrington, Immerman and Straubing.
No circuit model is introduced.

The two classical vocabularies define the same problems,
FO(≤, +, ×) = FO(≤, +, BIT), where BIT reads a bit of the rank of an
element. One direction defines the powers of two from the arithmetic; the
other defines multiplication from BIT, through the Bit Sum Lemma, which
counts the ones of a word of logarithmic length.

The machine side is the logarithmic-time hierarchy: a problem is AC⁰
definable exactly when it is decided by an alternating machine with a
logarithmic clock and constantly many alternations, which guesses
addresses, queries the input at them, and passes over their bits with
finite automata.

AC⁰ definability is closed under complement and contains FO(≤). It is
contained in L, by evaluating the sentence with a deterministic multihead
automaton, hence in NL; and in PTIME, directly, the numeric predicates being
defined by one simultaneous induction, so that every AC⁰ definable problem
is definable in FO(LFP) and in FO(≤, IFP).

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the submission's own statements where they
compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
