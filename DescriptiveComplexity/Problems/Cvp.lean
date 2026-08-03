/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Defs
import DescriptiveComplexity.Problems.Cvp.Membership
import DescriptiveComplexity.Problems.Cvp.Hardness

/-!
# CVP

Umbrella file for the circuit value problem: does a Boolean circuit, given with
the values of its inputs, evaluate its output gate to `1`? It is the canonical
`PTIME`-complete problem ([Ladner 1975][ladner1975circuit]), and the second
complete problem the library has for the class, beside HORN-SAT.

## The two halves

**Membership** (`DescriptiveComplexity.cvp_mem_PTIME`) is written in FO(LFP)
rather than in the Horn fragment, because the semantics of the problem *is* a
least fixed point: the rule system is the ten gate rules transcribed, and the
output sentence – “some output gate is in the true rail” – is exactly the
statement a Horn program cannot make head-on, its goal clauses being able to
reject and not to accept. Immerman–Vardi
(`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`) reads the definition back
into the class.

**Hardness** (`DescriptiveComplexity.cvp_PTIME_hard`) draws, inside a HORN-SAT
instance, the circuit that runs unit propagation, and reports *failure* of Horn
satisfiability. Reducing from the complement is what keeps the circuit
monotone – no negation gate anywhere – and it costs nothing, since polynomial
time is closed under complement, so complementing the Horn discharge turns
hardness for `HORNSAT`ᶜ into hardness for the class. Unit propagation is a
fixed point and a circuit is acyclic, so the stages are unrolled along the
order, one element of the universe per stage; the two unbounded quantifiers of
a propagation round become chains of fan-in-two gates walking the order, and
the wiring – not the circuit – tests where a literal occurs, which is what an
interpretation may do and a fixed circuit may not.

## What is *not* assumed of an instance

Neither well-formedness nor acyclicity: the value of a gate is the least
dual-rail derivation, so junk derives nothing, a gate on a cycle derives
nothing, and a malformed gate is a yes-instance of nothing in particular. This
keeps CVP a total predicate on arbitrary `Language.circuit`-structures – and it
matters, acyclicity not being first-order and so not something a reduction
could be asked to establish.
-/

namespace DescriptiveComplexity

/-- **CVP is `PTIME`-complete** ([Ladner 1975][ladner1975circuit]): membership
is the FO(LFP) definition read back into the class by Immerman–Vardi, hardness
is the unit-propagation circuit drawn inside a HORN-SAT instance. Both halves
are machine-free, as everywhere in this library. -/
theorem CVP_PTIME_complete : PTIME.Complete CVP :=
  ⟨cvp_mem_PTIME, cvp_PTIME_hard⟩

end DescriptiveComplexity
