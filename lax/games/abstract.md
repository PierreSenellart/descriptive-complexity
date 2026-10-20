The separations proved in the descriptive-complexity library, which need
no complexity-theoretic assumption: what the logics of descriptive
complexity cannot express. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, and the
submissions on logarithmic space (lax-485149), polynomial time
(lax-535992), the polynomial hierarchy (lax-564036), polynomial space
(lax-134656), and AC⁰ (lax-895169).

The Ehrenfeucht–Fraïssé game is defined with its method: structures
equivalent for n rounds satisfy the same first-order sentences of
quantifier depth n. Two strategies are given, on bare sets with at least
n elements and, by Ehrenfeucht's theorem, on linear orders with at least
2ⁿ elements. The k-pebble game between two structures is defined as well,
with the invariance of k-variable formulas and of inflationary inductions
under it.

This is applied to EVEN, the parity of the universe. It is not
first-order definable, even with an order; but one deterministic walk
along the order decides it, so FO(≤) ⊊ FO(DTC) ⊆ FO(TC), and a sentence
with arithmetic decides it, so FO(≤) ⊊ AC⁰. It is in PTIME and not
definable by an inflationary induction without an order, so order-free
FO(IFP) does not capture PTIME; and no order-free induction defines a
linear order at all. PARITY, the parity of a marked subset, is in L and
not first-order definable. Finally EVEN reduces to some problem by a
reduction in FO(DTC) and by no first-order reduction: the first-order
reductions of these submissions are strictly weaker than
logarithmic-space reductions.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the submission's own statements and those of
the submissions it requires where they compose. The library and its
documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
