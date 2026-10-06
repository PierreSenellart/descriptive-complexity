Decision classes defined by counting, from the descriptive-complexity
library. It builds on the NP core registered as lax-904597 and on the
submissions on logarithmic space (lax-485149), polynomial time
(lax-535992), the polynomial hierarchy (lax-564036), AC⁰ (lax-895169), and
counting problems, #P, and FP (lax-366625).

A problem is in one of these classes when its answer is a property of the
numbers of witnesses of existential second-order sentences over ordered
structures, the descriptive form of the numbers of accepting runs of a
nondeterministic machine: ⊕P, after Papadimitriou and Zachos and,
independently, Goldschlager and Parberry, when the number is odd; Mod_k P,
after Cai and Hemachandra, when it is not a multiple of k; PP, after Gill,
when one number exceeds another; C₌P, after Wagner, when two numbers are
equal; and UP, after Valiant, when there is at most one witness and the
answer is whether there is one. Comparing two numbers, rather than taking
the sign of one integer, is the two-number form of the GapP characterization
of Fenner, Fortnow, and Kurtz.

UP is contained in NP and in ⊕P, NP and coNP in PP, and ⊕P and PP are closed
under complement. ⊕SAT is ⊕P-complete and Mod_k-SAT is Mod_k P-complete, and
more generally the parity and the residues of every parsimoniously
#P-complete problem are complete, since a parsimonious reduction preserves
every property of the count; ⊕P and Mod_k P are also reducibility to the
parity and residues of the number of accepting runs of a Turing machine.
Comparing the models of a CNF formula in which a selected variable is true
with those in which it is false gives a PP-complete problem, by majority,
and a C₌P-complete one, by equality; the hardness proof pairs two kernels in
one Tseitin formula. No complete problem is known for UP, a question which
Hartmanis and Hemachandra showed not to relativize.

The proofs are those of the library's development after version 1.2.2, on
its Lean 4.33 branch, sliced to what these statements use; they assume the
submission's own statements and those of the submissions it requires where
they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
