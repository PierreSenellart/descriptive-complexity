The classes NP and PTIME of the descriptive-complexity library, which are
defined by logics on finite structures, are the textbook classes on bit strings.
Over a vocabulary with finitely many relation symbols, a decision problem is in
NP exactly when the language of the binary encodings of its yes-instances has
polynomially bounded certificates checked in polynomial time by a Mathlib
Turing machine (FinTM2); it is in PTIME exactly when such a machine decides that
language in polynomial time. The encodings and the machine classes are those of
Szymon Toruńczyk's lax-988886 (Fagin's theorem) and lax-751879 (the
Immerman–Vardi theorem), required here, and each machine statement is one
application of a registered capture theorem.

The content of this submission is the logical side, which assumes neither
theorem: the library's second-order definition of NP agrees with the existential
second-order logic of lax-988886, and the library's definition of PTIME with the
FO(LFP) of lax-751879. The second agreement carries the proofs. Going to the
archive's syntax turns one simultaneous least fixed point into nested ones, by
Bekić's principle. Coming back turns nested, negated, and parameterized fixed
points into one inflationary induction, by a construction that iterates a program
in a relation it reads, its rounds being the tuples of the universe, each round
starting from empty relations and opening once the previous round has converged.
