A catalog of parsimoniously #P-complete problems, from the
descriptive-complexity library. It builds on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, the submission
on counting problems, #P, and FP (lax-366625), and the submissions it
requires on logarithmic space (lax-485149), polynomial time (lax-535992),
and AC⁰ (lax-895169).

Seventeen counting problems are parsimoniously #P-complete: #3SAT,
#1-in-SAT, #Exact Cover, #Knapsack, #0-1 Integer Programming, #Clique,
#Independent Set, #Vertex Cover, #Set Packing, #Set Cover, #Hitting Set,
#Dominating Set, #Feedback Vertex Set, #Feedback Arc Set, #Steiner Tree,
#Directed Hamilton Circuit, and #Hamilton Circuit. Each counts the solutions
of a problem of the NP catalog, at exactly the threshold size where the
decision problem asks for one at least or at most that large, so that the
reductions can be parsimonious. Each is in #P, and its hardness is carried
along a parsimonious first-order reduction, ordered or relativized where
needed, from a problem proved complete before it; the proofs form the
library's tree of reductions rooted at #SAT. The reductions are parsimonious
versions of reductions between the decision problems that go back to Karp,
and to Schaefer for 1-in-SAT; parsimonious reductions are due to Simon, and
the #P-completeness of such counting problems goes back to Valiant. The
support of each problem, the instances with a positive count, is the
corresponding decision problem, or for four of them implies it.

The proofs are those of the library's development after version 1.2.2, on
its Lean 4.33 branch, sliced to what these statements use; they assume the
submission's own statements and those of the submissions it requires where
they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
