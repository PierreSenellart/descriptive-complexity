import Lax904597.SecondOrder

/-!
---
title: Atoms in second-order relation variables
type: definition
---
Given a block of second-order relation variables $R_1, \dots, R_m$ and $k$
first-order variables $x_1, \dots, x_k$, an atom is an expression
$R_i(x_{j_1}, \dots, x_{j_r})$, with $r$ the arity of $R_i$. It holds under an
assignment of relations to the block and a valuation $v$ of the variables when
the tuple $(v(x_{j_1}), \dots, v(x_{j_r}))$ belongs to the relation assigned
to $R_i$. The clausal fragments of existential second-order logic, Krom and
Horn, are built from these atoms.
-/

namespace Lax485149.SecondOrderAtoms

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- An atom `R i (x_{f 0}, …)` in the relation variables of a block, with
arguments read from `k` universally quantified first-order variables. -/
structure SOAtom (B : SOBlock) (k : ℕ) where
  /-- The relation variable of the block the atom is about. -/
  idx : B.ι
  /-- The arguments, as indices among the `k` universally quantified
  variables. -/
  args : Fin (B.arity idx) → Fin k

variable {B : SOBlock} {k : ℕ}

/-- The truth value of a second-order atom under an assignment of the block
and a valuation of the universally quantified variables. -/
def SOAtom.Holds {A : Type} (a : SOAtom B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  ρ a.idx fun j => v (a.args j)

end Lax485149.SecondOrderAtoms
