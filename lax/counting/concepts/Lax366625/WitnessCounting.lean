import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Lax366625.CountingProblems
import Lax904597.SecondOrder
import Lax366625.CountingClasses

/-!
---
title: The class #P, by witness counting
type: definition
---
Given a block of second-order relation variables and a first-order sentence
$\varphi$ over a vocabulary expanded by the block, the witness count of
$\varphi$ on a structure is the number of assignments of relations to the
block under which $\varphi$ holds. A counting problem $C$ over $L$ is
#P-definable when there are a block and a sentence $\varphi$ over
$L \cup \{\le\}$ and the block such that, for every nonempty finite
$L$-structure $A$ and every linear order on $A$, $C(A)$ is the witness count
of $\varphi$ on $A$ with that order: the number of witnesses of an
existential second-order sentence, after Saluja, Subrahmanyam, and Thakur.
#P is the counting class of the #P-definable problems.
-/

namespace Lax366625.WitnessCounting

open Lax366625.CountingProblems Lax904597.SecondOrder

open FirstOrder

open Language Structure

section Witness

variable {L : Language.{0, 0}}

/-- The number of assignments of the block `B` on the structure `A` under which
the first-order kernel `φ` holds. -/
noncomputable def witnessCount (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [inst : L.Structure A] : ℕ :=
  Nat.card {ρ : B.Assignment A //
    @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ)) φ}

end Witness

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A counting problem is **`#P`-definable** if, on nonempty finite structures,
it counts the witnesses of an existential second-order sentence over the
ordered expansion: for some block `B` and first-order kernel `φ`, its value is
the number of assignments of `B` satisfying `φ`, whatever the linear order of
the instance. -/
def SharpPDefinable (C : CountingProblem L) : Prop :=
  ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = witnessCount B φ A

end Definable

open Lax366625.CountingClasses

/-- **#P**: the class of the `#P`-definable counting problems. -/
def SharpP : CountingClass :=
  CountingClass.ofMem fun C => SharpPDefinable C

end Lax366625.WitnessCounting
