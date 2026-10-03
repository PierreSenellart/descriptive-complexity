Recursive enumerability as a logically defined class, from the
descriptive-complexity library, built on the NP core registered as
lax-904597 and on the catalog registered as lax-799700. RE is the class of
decision problems on finite structures definable in existential second-order
logic with value invention: the certificate is a finite extension of the
universe by invented values, in unbounded number, together with relations
over it checked by a first-order kernel. No machine model enters the
definition.

Four problems are RE-complete under the core's first-order reductions:
finite satisfiability of first-order sentences, by the generic reduction
that writes a definition as a sentence, which is Trakhtenbrot's theorem in
logical form; the halting problem of the core's machine instances, with the
step and tape bounds dropped; the halting of a partial recursive code of
Mathlib drawn as a syntax tree; and Post's correspondence problem, by the
computation-history dominoes. The archive's proof network carries the chain:
every problem of RE reduces to finite satisfiability, finite satisfiability
to the two halting problems, the halting problem to Post's.

The class meets Mathlib's computability theory on concrete instances, finite
structures presented as a size and Boolean tables: a problem is in RE exactly
when its concrete instances form a recursively enumerable set, first-order
reductions are computable, so every RE-hard problem is undecidable, and the
four problems are undecidable in Mathlib's sense, finite satisfiability
being Trakhtenbrot's theorem proper. NP is contained in RE, and RE differs
from co-RE, by Post's theorem on code halting.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's hardness laws and the submission's
own statements where they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
