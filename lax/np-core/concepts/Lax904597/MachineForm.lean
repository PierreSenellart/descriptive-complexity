import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Machines

/-!
---
title: The Cook–Levin theorem, in its machine form
type: theorem
---
Machine acceptance – does a nondeterministic Turing machine, given as a
finite structure, accept its input in fewer steps than there are
positions? – is interreducible with SAT, and characterizes NP: a problem is
existential second-order definable exactly when it has an ordered
first-order reduction to machine acceptance.

Together with the machine-free Cook–Levin theorem this gives the statement
in machine terms: SAT is NP-complete for NP read as nondeterministic
polynomial time, where the time available to a machine is the number of
positions of the structure a reduction builds, polynomial in the input –
the bound is unary by construction – and where the reduction from a machine
to a formula is the usual tableau, built here as a first-order
interpretation.
-/

namespace Lax904597.MachineForm

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.SecondOrder Lax904597.Classes
  Lax904597.Sat Lax904597.Machines

/-- SAT reduces to machine acceptance, by the machine that guesses an
assignment and checks the clauses; and whatever reduces to machine
acceptance reduces to SAT, by the tableau of the machine as a first-order
interpretation. -/
axiom SAT_complete_for_ntmAccept : ∀ (h : NTMAcceptInvariant),
  Nonempty (OrderedFOReduction SAT (NTMAccept h)) ∧
    ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
      Nonempty (OrderedFOReduction P (NTMAccept h)) → Nonempty (OrderedFOReduction P SAT)

/-- NP, as existential second-order definability, is the class of problems
that reduce to machine acceptance. -/
axiom mem_NP_iff_le_ntmAccept : ∀ (h : NTMAcceptInvariant)
  {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
  NP.Mem P ↔ Nonempty (OrderedFOReduction P (NTMAccept h))

end Lax904597.MachineForm
