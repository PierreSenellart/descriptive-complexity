import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax895169.BitPredicate

/-!
---
title: First-order logic with order, addition and BIT
type: definition
---
The atoms of the bit-level logic over a vocabulary $L$ are $x \le y$, the
addition of ranks $r(x) + r(y) = r(z)$, BIT$(i, x)$, and the atoms of $L$.
A kernel is a Boolean combination of atoms, and a sentence is in prenex
form: a quantifier prefix over finitely many variables followed by a kernel.
It holds on a finite linearly ordered $L$-structure when the prefix holds of
the kernel.

A decision problem $P$ over $L$ is bit-definable when some sentence holds,
for every nonempty finite $L$-structure $A$ and every linear order on $A$,
exactly when $A$ is a yes-instance of $P$. This is the logic
FO($\le, +$, BIT), in prenex form.
-/

namespace Lax895169.BitLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- The atoms of the bit-level logic: the order, the addition of ranks, the bit
of an element at an index, and an input relation at a tuple of variables. -/
inductive BitAtom (L : Language.{0, 0}) (γ : Type) where
  /-- `x ≤ y`. -/
  | le (x y : γ) : BitAtom L γ
  /-- `orank x + orank y = orank z`. -/
  | plus (x y z : γ) : BitAtom L γ
  /-- The bit of `x` at the index `i` is set. -/
  | bit (i x : γ) : BitAtom L γ
  /-- An input relation at a tuple of variables. -/
  | rel {a : ℕ} (R : L.Relations a) (arg : Fin a → γ) : BitAtom L γ

/-- A quantifier-free kernel over the bit-level atoms. -/
inductive BitKernel (L : Language.{0, 0}) (γ : Type) where
  /-- An atom. -/
  | atom (a : BitAtom L γ) : BitKernel L γ
  /-- The constant `true`, so that a trivial relation needs no dummy variable. -/
  | tt : BitKernel L γ
  /-- Negation. -/
  | not (k : BitKernel L γ) : BitKernel L γ
  /-- Conjunction. -/
  | and (k k' : BitKernel L γ) : BitKernel L γ
  /-- Disjunction. -/
  | or (k k' : BitKernel L γ) : BitKernel L γ

/-- **A sentence of the bit-level logic, in prenex form**: a polarity per
variable and a quantifier-free kernel. -/
structure BitSentence (L : Language.{0, 0}) where
  /-- The number of quantified variables. -/
  vars : ℕ
  /-- The quantifier at each variable: `true` existential, `false` universal. -/
  pol : Fin vars → Bool
  /-- The quantifier-free kernel. -/
  kernel : BitKernel L (Fin vars)

namespace BitAtom

variable {L : Language.{0, 0}} {γ : Type}

/-- What an atom says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitAtom L γ → (γ → A) → Prop
  | .le x y, v => v x ≤ v y
  | .plus x y z, v => orank (v x) + orank (v y) = orank (v z)
  | .bit i x, v => BitIx (v i) (v x)
  | .rel R arg, v => RelMap R fun t => v (arg t)

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {γ : Type}

/-- What a kernel says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitKernel L γ → (γ → A) → Prop
  | .atom a, v => a.Holds v
  | .tt, _ => True
  | .not k, v => ¬ k.Holds v
  | .and k k', v => k.Holds v ∧ k'.Holds v
  | .or k k', v => k.Holds v ∨ k'.Holds v

end BitKernel

namespace BitSentence

/-- What a sentence says of an instance: the prefix, played over the kernel. -/
def Holds {L : Language.{0, 0}} (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : Prop :=
  prefixHolds (A := A) φ.vars φ.pol fun v => φ.kernel.Holds v

end BitSentence

/-- A decision problem is **bit-definable** when a prenex sentence over the
order, the addition and the bit at an index – `FO(≤, +, BIT)` – decides it on
every nonempty finite ordered structure. -/
def BitDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : BitSentence L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ φ.Holds A

end Lax895169.BitLogic
