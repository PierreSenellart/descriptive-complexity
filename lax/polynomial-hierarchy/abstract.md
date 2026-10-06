The polynomial hierarchy as a family of logically defined classes, from the
descriptive-complexity library, built on the NP core registered as
lax-904597, the catalog of NP-complete problems lax-799700, and the classes
of logarithmic space and polynomial time, lax-485149 and lax-535992. Above
polynomial time, the level Σₖ is the class of decision problems on finite
structures definable by a second-order sentence with k alternating blocks of
quantifiers, existential first, and Πₖ the class of those definable with a
universal first block: the levels of the hierarchy by the theorems of Fagin
and Stockmeyer. coNP is Π₁, PH is the union of the levels, and DP is the
class of conjunctions of an NP and a coNP condition. No machine model enters
the definitions.

The structure of the hierarchy is proved, not assumed: Πₖ is the class of
complements of Σₖ, the levels are nested and contained in PH, polynomial
time sits at the bottom, inside NP ∩ coNP, and NP ∪ coNP ⊆ DP ⊆ Σ₂ ∩ Π₂.
coNP and DP are closed under first-order reductions.

Complete problems are given at every level, under the core's first-order
reductions: tautology of DNF formulas, its restriction to width three and
the unsatisfiability of 3-CNF formulas for coNP; SAT-UNSAT for DP; and, for
every k ≥ 1, quantified Boolean formulas with k alternating blocks for Σₖ
and for Πₖ, according to the first quantifier.

Each level is then related to a machine model: acceptance by an alternating
Turing machine with k blocks of states, within the bounds of the instance,
is complete for Σₖ or Πₖ according to its first block, and a problem is in
the level exactly when it reduces to that acceptance problem. At one block
this gives coNP its machine.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's hardness laws and the submission's
own statements where they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
