Polynomial time as a logically defined class, from the
descriptive-complexity library, built on the NP core registered as
lax-904597 and on the logarithmic-space classes registered as lax-485149.
PTIME is the class of decision problems on finite structures definable in
the Horn fragment of existential second-order logic, on ordered structures
and invariantly in the order: the logic that captures polynomial time by a
theorem of Grädel. No machine model enters the definition.

The Horn fragment is equivalent to first-order logic with least fixed
points, FO(LFP), each compiled into the other; read against the definition
of the class, this is the Immerman–Vardi theorem, PTIME = FO(LFP). FO(LFP)
is closed under complement, hence so is the Horn fragment, and PTIME =
coPTIME. First-order logic with inflationary fixed points defines the same
problems on ordered structures, so FO(≤, IFP) = PTIME as well.

Four problems are complete under the core's first-order reductions: the
satisfiability of Horn formulas, by a generic reduction that instantiates a
Horn program, the polynomial-time counterpart of the Cook–Levin theorem; the
circuit value problem; alternating reachability; and acceptance by a
deterministic Turing machine within the bounds of the instance. The last
relates the class to the machine model: a problem is in PTIME exactly when
it reduces to deterministic machine acceptance.

The class sits between those of the two earlier submissions: L ⊆ NL ⊆ PTIME
⊆ NP, neither inclusion of a fragment being syntactic.

The proofs are those of version 1.2.2 of the library, sliced to what these
statements use; they assume the core's hardness laws and the submission's
own statements where they compose. The library and its documentation are at
<https://github.com/PierreSenellart/descriptive-complexity> and
<https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html>.
The Lean code was written with the assistance of several Claude models; the
design and the statements are the author's.
