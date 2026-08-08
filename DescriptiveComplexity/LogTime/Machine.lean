/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Bits

/-!
# Alternating machines with a logarithmic clock, at the level of bits

The machine side of the bottom of the ladder: an **alternating random-access
machine** whose registers hold addresses of the instance, whose clock is the
number of *bit positions* of those addresses – logarithmic in the size of the
universe – and whose deterministic steps are **bit operations**, never a numeric
predicate.

## The three parts of a machine

* **Guesses.** A machine names `regs` registers and a polarity for each
  (`DescriptiveComplexity.LTMachine.pol`): the registers are filled in order,
  existentially or universally, by the two players. A register holds an element
  of the universe, that is, an address of `posCount A` bits, so filling one is a
  block of the classical `Σₖ-TIME(log n)` normal form – a logarithmic number of
  guessed bits – and an alternation is a change of polarity along the list.
* **Queries.** The instance is read only through
  `DescriptiveComplexity.BaseTest.query`: an input relation at a tuple of
  registers. This is the random access of the model, and in a structure-based
  framework it needs no index tape: *reading the input at an address is
  evaluating a relation at a tuple*.
* **Sweeps.** Everything else the machine computes it computes bit by bit, with
  `DescriptiveComplexity.Sweep`: one pass over the bit positions, from the
  lowest to the highest, run by a finite automaton with `σ` state bits that
  reads, at each position, one bit of each register. A base test is a Boolean
  combination of sweeps and queries, so a machine performs a *constant number of
  passes* over a logarithmic tape: a logarithmic clock, and a constant number of
  head reversals.

## Why the base has to be this weak, and what it can still do

Letting the base evaluate an atom of `≤`, `+` or `×` in one step would make the
model a prenex `FO(≤, +, ×)` sentence in disguise, and the bridge to the logic
vacuous. Sweeps are the honest opposite: they see nothing but bits, and the
arithmetic has to be *built* – `DescriptiveComplexity.leSweep` and
`DescriptiveComplexity.plusSweep` (in `DescriptiveComplexity.LogTime.Arith`)
are the comparison and the ripple-carry addition, exactly as
`DescriptiveComplexity.HeadArith` builds them one resource bound higher.

The restriction is real, and its boundary is worth naming: a sweep carries `σ`
bits of state past each position, so a constant number of sweeps carries a
constant number of bits per position, that is, `O(log n)` bits of trace in
total – which is what a first-order formula can guess, one element per bit
vector (`DescriptiveComplexity.LogTime.Simulate`). A machine that could *count*
its positions, or revisit them unboundedly often, would leave that budget, and
with it the reach of the simulation.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Boolean expressions over bits -/

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

/-- The value of an expression under a `Prop`-valued assignment: the reading a
first-order formula gives it. -/
def Holds (val : V → Prop) : BitExpr V → Prop
  | .var v => val v
  | .tt => True
  | .ff => False
  | .not e => ¬ e.Holds val
  | .and e f => e.Holds val ∧ f.Holds val
  | .or e f => e.Holds val ∨ f.Holds val

/-- The two readings agree. -/
theorem holds_iff_eval (val : V → Bool) (e : BitExpr V) :
    e.Holds (fun v => val v = true) ↔ e.eval val = true := by
  induction e with
  | var v => exact Iff.rfl
  | tt => simp [Holds, eval]
  | ff => simp [Holds, eval]
  | not e ih => simp [Holds, eval, ih]
  | and e f ihe ihf => simp [Holds, eval, ihe, ihf]
  | or e f ihe ihf => simp [Holds, eval, ihe, ihf]

/-- Renaming the bit variables of an expression. -/
def mapVar {W : Type} (f : V → W) : BitExpr V → BitExpr W
  | .var v => .var (f v)
  | .tt => .tt
  | .ff => .ff
  | .not e => .not (e.mapVar f)
  | .and e g => .and (e.mapVar f) (g.mapVar f)
  | .or e g => .or (e.mapVar f) (g.mapVar f)

/-- Renaming bit variables is composition on the assignment. -/
theorem eval_mapVar {W : Type} (f : V → W) (val : W → Bool) (e : BitExpr V) :
    (e.mapVar f).eval val = e.eval (val ∘ f) := by
  induction e with
  | var v => rfl
  | tt => rfl
  | ff => rfl
  | not e ih => rw [mapVar, eval, ih, eval]
  | and e g ihe ihg => rw [mapVar, eval, ihe, ihg, eval]
  | or e g ihe ihg => rw [mapVar, eval, ihe, ihg, eval]

/-- Holding only depends on the assignment pointwise. -/
theorem holds_congr {val val' : V → Prop} (h : ∀ v, val v ↔ val' v) (e : BitExpr V) :
    e.Holds val ↔ e.Holds val' := by
  induction e with
  | var v => exact h v
  | tt => exact Iff.rfl
  | ff => exact Iff.rfl
  | not e ih => exact not_congr ih
  | and e f ihe ihf => exact and_congr ihe ihf
  | or e f ihe ihf => exact or_congr ihe ihf

end BitExpr

/-! ### Sweeps -/

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

/-- **The state of a sweep before position `i`**: the automaton starts in
`DescriptiveComplexity.Sweep.init` and takes one step per position, reading the
bits of the registers there. -/
noncomputable def state (S : Sweep ρ) (x : Fin ρ → A) : ℕ → (Fin S.σ → Bool)
  | 0 => S.init
  | i + 1 => fun j => (S.step j).eval
      (Sum.elim (S.state x i) fun k => (orank (x k)).testBit i)

omit [Finite A] in
@[simp]
theorem state_zero (S : Sweep ρ) (x : Fin ρ → A) : S.state x 0 = S.init := rfl

omit [Finite A] in
theorem state_succ (S : Sweep ρ) (x : Fin ρ → A) (i : ℕ) (j : Fin S.σ) :
    S.state x (i + 1) j = (S.step j).eval
      (Sum.elim (S.state x i) fun k => (orank (x k)).testBit i) := rfl

/-- **A sweep accepts** when its acceptance condition holds of the state left
after the last bit position. -/
def Accepts (S : Sweep ρ) (x : Fin ρ → A) : Prop :=
  S.acc.eval (S.state x (posCount A)) = true

/-- **Renaming the registers of a sweep**: what lets a sweep built once – the
comparison, the addition – be run on any registers of a larger machine. -/
def relabel {ρ' : ℕ} (S : Sweep ρ) (f : Fin ρ → Fin ρ') : Sweep ρ' where
  σ := S.σ
  init := S.init
  step := fun j => (S.step j).mapVar (Sum.map id f)
  acc := S.acc

omit [Finite A] in
/-- A renamed sweep runs the original one on the renamed registers. -/
theorem state_relabel {ρ' : ℕ} (S : Sweep ρ) (f : Fin ρ → Fin ρ') (x : Fin ρ' → A) :
    ∀ (i : ℕ) (j : Fin S.σ), (S.relabel f).state x i j = S.state (fun k => x (f k)) i j := by
  intro i
  induction i with
  | zero => intro j; rfl
  | succ i ih =>
    intro j
    have h1 := BitExpr.eval_mapVar (Sum.map id f)
      (Sum.elim ((S.relabel f).state x i) fun k => (orank (x k)).testBit i) (S.step j)
    have h2 : ((Sum.elim ((S.relabel f).state x i) fun k => (orank (x k)).testBit i) ∘
        Sum.map id f) =
        Sum.elim (S.state (fun k => x (f k)) i) fun k => (orank (x (f k))).testBit i := by
      funext z
      rcases z with j' | k
      · exact ih j'
      · rfl
    exact h1.trans (congrArg (fun v => (S.step j).eval v) h2)

/-- Acceptance of a renamed sweep. -/
theorem accepts_relabel {ρ' : ℕ} (S : Sweep ρ) (f : Fin ρ → Fin ρ') (x : Fin ρ' → A) :
    (S.relabel f).Accepts x ↔ S.Accepts fun k => x (f k) := by
  have h : (S.relabel f).state x (posCount A) = S.state (fun k => x (f k)) (posCount A) :=
    funext fun j => state_relabel S f x _ j
  have hacc : (S.relabel f).Accepts x ↔ S.acc.eval ((S.relabel f).state x (posCount A)) = true :=
    Iff.rfl
  rw [hacc, h]
  exact Iff.rfl

end Sweep

/-! ### The deterministic base -/

/-- The **deterministic base** of a machine: a Boolean combination of sweeps and
of queries to the instance. Its cost is a constant number of passes over the bit
positions, hence `O(log n)` steps; nothing here evaluates a numeric predicate. -/
inductive BaseTest (L : Language.{0, 0}) (ρ : ℕ) where
  /-- Run a sweep on the registers. -/
  | sweep (S : Sweep ρ) : BaseTest L ρ
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
  | .query R arg, x => RelMap R fun t => x (arg t)
  | .not t, x => ¬ t.Holds x
  | .and t u, x => t.Holds x ∧ u.Holds x
  | .or t u, x => t.Holds x ∨ u.Holds x

end BaseTest

/-! ### Machines, and the class they decide -/

/-- **An alternating machine with a logarithmic clock**: a list of registers,
each filled by one of the two players, and a deterministic bit-level test of the
tuple they leave behind.

Registers are filled in order, `DescriptiveComplexity.LTMachine.pol i` telling
which player fills the `i`-th; a *block* of the classical normal form is a
maximal run of equal polarities, and the number of alternations is the number of
changes along the list. -/
structure LTMachine (L : Language.{0, 0}) where
  /-- The number of registers, that is, of guessed addresses. -/
  regs : ℕ
  /-- Who fills each register: `true` existentially, `false` universally. -/
  pol : Fin regs → Bool
  /-- The deterministic base test. -/
  base : BaseTest L regs

/-- The quantifier prefix of a machine, peeled from the innermost register
outwards. -/
def prefixHolds {A : Type} : (m : ℕ) → (Fin m → Bool) → ((Fin m → A) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | m + 1, pol, P =>
      prefixHolds m (fun j => pol j.castSucc)
        (fun v => if pol (Fin.last m) = true then ∃ a, P (Fin.snoc v a)
          else ∀ a, P (Fin.snoc v a))

/-- Prefixes only depend on their body pointwise. -/
theorem prefixHolds_congr {A : Type} :
    ∀ (m : ℕ) (pol : Fin m → Bool) {P Q : (Fin m → A) → Prop},
      (∀ v, P v ↔ Q v) → (prefixHolds m pol P ↔ prefixHolds m pol Q) := by
  intro m
  induction m with
  | zero => intro pol P Q h; exact h _
  | succ m ih =>
    intro pol P Q h
    refine ih (fun j => pol j.castSucc) fun v => ?_
    by_cases hp : pol (Fin.last m) = true
    · rw [if_pos hp, if_pos hp]
      exact exists_congr fun a => h _
    · rw [if_neg hp, if_neg hp]
      exact forall_congr' fun a => h _

/-- **The machine accepts** the instance when the two players, filling the
registers in order, leave a tuple passing the base test. -/
def LTMachine.Accepts {L : Language.{0, 0}} (M : LTMachine L) (A : Type) [L.Structure A]
    [LinearOrder A] [Finite A] : Prop :=
  prefixHolds (A := A) M.regs M.pol fun x => M.base.Holds x

/-- **The class decided by the machines of this section**: the analogue, at the
bottom of the ladder, of `DescriptiveComplexity.LOGSPACE`'s automata. A problem
is decidable in *sweeping logarithmic time* when one machine decides it on every
nonempty finite ordered structure. -/
def LTDecidable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ M : LTMachine L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ M.Accepts A

end DescriptiveComplexity
