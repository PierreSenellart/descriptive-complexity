import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.SecondOrder
import Lax485149.SecondOrderAtoms

/-!
---
title: The Horn fragment of existential second-order logic
type: definition
---
A Horn clause over a vocabulary $L$, a block of second-order relation
variables and $k$ first-order variables $\bar x$ is an implication
$\gamma(\bar x) \wedge \alpha_1 \wedge \dots \wedge \alpha_m \to \eta$,
where the guard $\gamma$ is an arbitrary first-order formula over $L$, the
body atoms $\alpha_i$ are atoms in the relation variables, and the head
$\eta$ is such an atom or $\bot$, the clause being then a goal clause. A
Horn program is a finite list of such clauses, and an assignment of
relations to the block satisfies it on a structure when every clause holds
at every valuation of $\bar x$.

A decision problem $P$ over $L$ is SO-Horn definable when there are a block,
a number $k$ and a Horn program over $L \cup \{\le\}$ such that, for
every nonempty finite $L$-structure $A$ and every linear order on $A$, $A$ is
a yes-instance of $P$ if and only if some assignment satisfies the program
on $A$ with that order. This is the fragment SO-Horn of Grädel, existential
second-order logic whose first-order kernel is universal and Horn in the
second-order atoms.
-/

namespace Lax535992.HornFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A Horn clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` and a list of second-order body atoms imply the head atom – or `⊥`,
when the head is `none` (a *goal* clause). -/
structure HornClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The body: second-order atoms, all of them positive. -/
  body : List (SOAtom B k)
  /-- The head: a second-order atom, or `none` for a goal clause. -/
  head : Option (SOAtom B k)

/-- An SO-Horn kernel, as data: a finite conjunction of Horn clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev HornProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (HornClause L B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of the head of a clause: `False` for a goal clause. -/
def HornClause.HeadHolds (c : HornClause L B k) (ρ : B.Assignment A)
    (v : Fin k → A) : Prop :=
  c.head.elim False fun h => h.Holds ρ v

/-- A Horn clause holds at a valuation when its guard and all its body atoms
force its head. -/
def HornClause.Holds (c : HornClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  (c.guard.Realize v ∧ ∀ a ∈ c.body, a.Holds ρ v) → c.HeadHolds ρ v

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def HornProgram.Holds (prog : HornProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

/-- A decision problem is *SO-Horn definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Horn
kernel: there is a block of relation variables and a Horn program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment. A single block suffices,
since existential second-order quantifiers merge.

The guards live over `L.sum Language.order`, and the equivalence is required
for *every* linear order on `A`: since the problem itself does not see the
order, this is order-invariant SO-Horn definability. -/
def SigmaSOHornDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : HornProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

end Lax535992.HornFragment
