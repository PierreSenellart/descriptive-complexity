import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Lax366625.WitnessCounting
import Lax904597.Problems
import Lax904597.SecondOrder
import Lax904597.Classes
import Lax485149.Problems
import Lax366625.CountingProblems

/-!
---
title: Decision classes defined by counting
type: definition
---
A decision problem $P$ over $L$ is defined by a relation $R$ between two
witness counts under a side condition $S$ when there are two existential
second-order sentences over $L \cup \{\le\}$ whose witness counts $c$ and
$d$ satisfy, on every nonempty finite $L$-structure with every linear order,
$S(c, d)$, and $P$ holds exactly when $R(c, d)$. The class of $S$ and $R$
consists of these problems, with cofinal hardness. Taking for the answer a
property of the counts, rather than of one integer, is the two-number form
of the GapP characterization of Fenner, Fortnow, and Kurtz.

The classes are ⊕P, after Papadimitriou and Zachos and, independently,
Goldschlager and Parberry, where the first count is odd; Mod$_k$P, after Cai
and Hemachandra, where it is not a multiple of $k$; PP, after Gill, where
the first count exceeds the second; C$_=$P, after Wagner, where the two
counts are equal; and UP, after Valiant, where the first count is at most
one and the answer is whether it is one. No complete problem is known for
UP, and the question does not relativize, as Hartmanis and Hemachandra
showed: UP is here for its inclusions. The decision version of a counting
problem by a property of numbers holds on the structures whose count has the
property.
-/

namespace Lax175070.CountDefinability

open Lax366625.WitnessCounting Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A decision problem is **defined by the relation `R` between two witness
counts under the side condition `S`** if, on nonempty finite ordered
structures, the two counts satisfy `S` and the problem holds exactly when
they satisfy `R`. -/
def CountDefinable (S R : ℕ → ℕ → Prop) (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (B' : SOBlock) (φ' : ((L.sum Language.order).sum B'.lang).Sentence),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      S (witnessCount B φ A) (witnessCount B' φ' A) ∧
        (P A ↔ R (witnessCount B φ A) (witnessCount B' φ' A))

end Definable

open Lax904597.Classes Lax485149.Problems Lax366625.CountingProblems

/-- The class of the problems defined by the relation `R` between two witness
counts under the side condition `S`, with cofinal hardness. -/
def countClass (S R : ℕ → ℕ → Prop) : ComplexityClass :=
  ComplexityClass.ofMem fun P => CountDefinable S R P

/-- **⊕P**: the number of witnesses is odd. -/
def ParityP : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => Odd c

/-- **Mod_k P**: the number of witnesses is not a multiple of `k`. -/
def ModP (k : ℕ) : ComplexityClass :=
  countClass (fun _ _ => True) fun c _ => ¬ k ∣ c

/-- **PP**: the first number of witnesses exceeds the second. -/
def PP : ComplexityClass :=
  countClass (fun _ _ => True) fun c d => d < c

/-- **C₌P**: the two numbers of witnesses are equal. -/
def CeqP : ComplexityClass :=
  countClass (fun _ _ => True) fun c d => c = d

/-- **UP**: at most one witness, and the answer is whether there is one. -/
def UP : ComplexityClass :=
  countClass (fun c _ => c ≤ 1) fun c _ => c = 1

/-- The decision version of a counting problem by a property `R` of numbers:
does the count satisfy `R`? -/
def decide {L : Language.{0, 0}} [L.IsRelational] (R : ℕ → Prop) (C : CountingProblem L) :
    DecisionProblem L :=
  DecisionProblem.ofPred fun A _ => R (C A)

end Lax175070.CountDefinability
