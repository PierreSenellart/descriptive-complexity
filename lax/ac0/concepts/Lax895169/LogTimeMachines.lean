import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Lax904597.Problems
import Lax895169.BitPredicate

/-!
---
title: Alternating logarithmic-time machines
type: definition
---
A machine over a vocabulary $L$ has a list of registers, each holding an
element of the universe, that is, an address of about $\log n$ bits, and
each filled by one of two players, existential or universal, in the order
of the list. It then runs a deterministic test of the tuple of registers, a
Boolean combination of three kinds of operations: a query, an atom of $L$
at a tuple of registers, which is the random access to the input; a read,
the bit of one register at the position named by another; and a sweep, one
pass over the bit positions from the lowest to the highest by a finite
automaton that reads, at each position, one bit of the rank of each
register. No operation evaluates a numeric predicate.

The machine accepts a finite linearly ordered $L$-structure when the
players, filling the registers in order, leave a tuple passing the test. A
decision problem is decidable in logarithmic time with constantly many
alternations when some machine accepts, for every nonempty finite
$L$-structure and every linear order on it, exactly the yes-instances. The
number of alternations is fixed by the machine, so this is the
logarithmic-time hierarchy of Sipser, the union of the classes
$\Sigma_k$-TIME($\log n$).
-/

namespace Lax895169.LogTimeMachines

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- A Boolean expression over bit variables: what a sweep computes in one step,
and what its acceptance condition is. Expressions rather than functions, so that
the translation into a formula is a recursion rather than an enumeration of a
truth table. -/
inductive BitExpr (V : Type) where
  /-- A bit variable. -/
  | var (v : V) : BitExpr V
  /-- The constant `true`. -/
  | tt : BitExpr V
  /-- The constant `false`. -/
  | ff : BitExpr V
  /-- Negation. -/
  | not (e : BitExpr V) : BitExpr V
  /-- Conjunction. -/
  | and (e f : BitExpr V) : BitExpr V
  /-- Disjunction. -/
  | or (e f : BitExpr V) : BitExpr V

namespace BitExpr

variable {V : Type}

/-- The value of an expression under a `Bool`-valued assignment. -/
def eval (val : V → Bool) : BitExpr V → Bool
  | .var v => val v
  | .tt => true
  | .ff => false
  | .not e => !(e.eval val)
  | .and e f => e.eval val && f.eval val
  | .or e f => e.eval val || f.eval val

end BitExpr

/-- A **sweep**: one pass over the bit positions of the universe, from the
lowest to the highest, by a finite automaton with `σ` state bits reading, at
each position, one bit of each of the `ρ` registers. -/
structure Sweep (ρ : ℕ) where
  /-- The number of state bits. -/
  σ : ℕ
  /-- The state before the lowest position. -/
  init : Fin σ → Bool
  /-- The next state: one Boolean expression per state bit, over the old state
  and the register bits at the current position. -/
  step : Fin σ → BitExpr (Fin σ ⊕ Fin ρ)
  /-- The acceptance condition, read from the state after the last position. -/
  acc : BitExpr (Fin σ)

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The state of a sweep before position `i`**: the automaton starts in its
initial state and takes one step per position, reading the bits of the
registers there. -/
noncomputable def state (S : Sweep ρ) (x : Fin ρ → A) : ℕ → (Fin S.σ → Bool)
  | 0 => S.init
  | i + 1 => fun j => (S.step j).eval
      (Sum.elim (state S x i) fun k => (orank (x k)).testBit i)

/-- **A sweep accepts** when its acceptance condition holds of the state left
after the last bit position. -/
def Accepts (S : Sweep ρ) (x : Fin ρ → A) : Prop :=
  S.acc.eval (S.state x (posCount A)) = true

end Sweep

/-- The **deterministic base** of a machine: a Boolean combination of sweeps and
of queries to the instance. Its cost is a constant number of passes over the bit
positions, hence `O(log n)` steps; nothing here evaluates a numeric predicate. -/
inductive BaseTest (L : Language.{0, 0}) (ρ : ℕ) where
  /-- Run a sweep on the registers. -/
  | sweep (S : Sweep ρ) : BaseTest L ρ
  /-- Read a bit: the bit of register `x` at the position named by register
  `i`. The addressing the model has over its own registers, and the one base
  operation that is not a pass over the positions. -/
  | bit (i x : Fin ρ) : BaseTest L ρ
  /-- Query the instance: an input relation at a tuple of registers. -/
  | query {a : ℕ} (R : L.Relations a) (arg : Fin a → Fin ρ) : BaseTest L ρ
  /-- Negation. -/
  | not (t : BaseTest L ρ) : BaseTest L ρ
  /-- Conjunction. -/
  | and (t u : BaseTest L ρ) : BaseTest L ρ
  /-- Disjunction. -/
  | or (t u : BaseTest L ρ) : BaseTest L ρ

namespace BaseTest

variable {L : Language.{0, 0}} {ρ : ℕ}

/-- What a base test says of a tuple of register values. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BaseTest L ρ → (Fin ρ → A) → Prop
  | .sweep S, x => S.Accepts x
  | .bit i y, x => BitIx (x i) (x y)
  | .query R arg, x => RelMap R fun t => x (arg t)
  | .not t, x => ¬ t.Holds x
  | .and t u, x => t.Holds x ∧ u.Holds x
  | .or t u, x => t.Holds x ∨ u.Holds x

end BaseTest

/-- **An alternating machine with a logarithmic clock**: a list of registers,
each filled by one of the two players, and a deterministic bit-level test of the
tuple they leave behind. Registers are filled in order, `pol i` telling which
player fills the `i`-th; the number of alternations is the number of changes
of polarity along the list. -/
structure LTMachine (L : Language.{0, 0}) where
  /-- The number of registers, that is, of guessed addresses. -/
  regs : ℕ
  /-- Who fills each register: `true` existentially, `false` universally. -/
  pol : Fin regs → Bool
  /-- The deterministic base test. -/
  base : BaseTest L regs

/-- **The machine accepts** the instance when the two players, filling the
registers in order, leave a tuple passing the base test. -/
def LTMachine.Accepts {L : Language.{0, 0}} (M : LTMachine L) (A : Type) [L.Structure A]
    [LinearOrder A] [Finite A] : Prop :=
  prefixHolds (A := A) M.regs M.pol fun x => M.base.Holds x

/-- A problem is decidable in *constant-alternation logarithmic time* when one
machine decides it on every nonempty finite ordered structure. -/
def LTDecidable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ M : LTMachine L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ M.Accepts A

end Lax895169.LogTimeMachines
