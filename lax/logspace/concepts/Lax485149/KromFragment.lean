import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax485149.SecondOrderAtoms
import Lax904597.Problems
import Lax904597.SecondOrder
import Lax904597.Interpretations

/-!
---
title: The Krom fragment of existential second-order logic
type: definition
---
A Krom clause over a vocabulary $L$, a block of second-order relation
variables and $k$ first-order variables $\bar x$ is an implication
$\gamma(\bar x) \to \ell_1 \vee \ell_2$, where the guard $\gamma$ is an
arbitrary first-order formula over $L$ and each $\ell_i$ is an atom in the
relation variables or the negation of one; either literal may be absent, so a
clause may be a unit clause or the goal clause $\gamma(\bar x) \to \bot$.
A Krom program is a finite list of such clauses, and an assignment of
relations to the block satisfies it on a structure when every clause holds at
every valuation of $\bar x$.

A decision problem $P$ over $L$ is SO-Krom definable when there are a block,
a number $k$ and a Krom program over $L \cup \{\le\}$ such that, for
every nonempty finite $L$-structure $A$ and every linear order on $A$, $A$ is
a yes-instance of $P$ if and only if some assignment satisfies the program
on $A$ with that order. The guards may thus use the order, while the problem
does not depend on it. This is the fragment SO-Krom of Grädel, existential
second-order logic whose first-order kernel is universal with at most two
second-order literals per clause.
-/

namespace Lax485149.KromFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A literal in the relation variables of a block: an atom together with a
sign (`positive = false` for a negated atom). -/
structure KromLit (B : SOBlock) (k : ℕ) where
  /-- The underlying second-order atom. -/
  atom : SOAtom B k
  /-- The sign of the literal: `true` for the atom, `false` for its
  negation. -/
  positive : Bool

/-- A Krom clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` implies the disjunction of at most two signed second-order literals.
A `none` literal is absent, so a clause with both literals absent is the goal
clause `guard → ⊥`. -/
structure KromClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The first literal of the clause, if any. -/
  lit₁ : Option (KromLit B k)
  /-- The second literal of the clause, if any. -/
  lit₂ : Option (KromLit B k)

/-- An SO-Krom kernel, as data: a finite conjunction of Krom clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev KromProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (KromClause L B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of a literal: its atom, or the negation of its atom. -/
def KromLit.Holds (l : KromLit B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  if l.positive then l.atom.Holds ρ v else ¬l.atom.Holds ρ v

/-- The truth value of one of the two literal slots of a clause: `False` when
the literal is absent. -/
def KromLit.slotHolds (o : Option (KromLit B k)) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  o.elim False fun l => l.Holds ρ v

/-- A Krom clause holds at a valuation when its guard forces one of its (at
most two) literals. -/
def KromClause.Holds (c : KromClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  c.guard.Realize v →
    (KromLit.slotHolds c.lit₁ ρ v ∨ KromLit.slotHolds c.lit₂ ρ v)

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def KromProgram.Holds (prog : KromProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

variable {L : Language.{0, 0}}

/-- A decision problem is *SO-Krom definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Krom
kernel: there is a block of relation variables and a Krom program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment. A single block suffices,
since existential second-order quantifiers merge.

The guards live over `L.sum Language.order` and the equivalence is required
for *every* linear order on `A`, so this is order-invariant SO-Krom
definability. -/
def SigmaSOKromDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : KromProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

end Lax485149.KromFragment
