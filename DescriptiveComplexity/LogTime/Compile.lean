/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Arith
import DescriptiveComplexity.LogTime.Simulate

/-!
# The lower fence: a bit-level prenex logic, compiled into machines

`DescriptiveComplexity.LTDecidable.ac0Definable` puts the machine model inside
the logic. This file puts a logic inside the machine model, so that the
characterization is a **sandwich** with both fences proved:

`FO(≤, +, BIT)` in prenex form  ⊆  sweeping logarithmic time  ⊆  `FO(≤, +, ×)`.

## The logic

`DescriptiveComplexity.BitSentence`: a quantifier prefix – a polarity per
variable, exactly the shape a machine's registers have – over a quantifier-free
kernel built from four atoms (`DescriptiveComplexity.BitAtom`): the order, the
addition of ranks, an input relation at a tuple of variables, and a **guarded
bit** `IsPos p ∧ BitAt p x`, that is, “`p` is a position and the bit of `x`
there is set”.

The guard is not a blemish but the honest reading of `BIT` in a vocabulary whose
positions are named by their place values: for a `p` that is *not* a place
value, `DescriptiveComplexity.BitAt` is a condition modulo `2p`, which is
arithmetic rather than bit-level, and no sweep decides it. Guarding it is what
keeps the atom inside the machine's reach – `oneBitSweep` checks that `p` has
exactly one bit, `impliesSweep` that every bit of `p` is a bit of `x`
(`DescriptiveComplexity.bitAt_iff_sweeps`).

## The compilation

Atom by atom, with the sweeps already built: `≤` is `leSweep`, `+` is
`plusSweep`, the bit atom is the pair above, and an input relation is a query.
`DescriptiveComplexity.Sweep.relabel` is what lets a sweep written once for two
or three registers be run on any registers of the machine. The Boolean structure
of the kernel becomes the Boolean structure of the base test, and the quantifier
prefix becomes the register list unchanged – there is nothing to prenexify,
because the source syntax is prenex by construction.

## What the sandwich does and does not close

It does not collapse. The gap between the fences is exactly `×` on one side and
`BIT` on the other, that is, Immerman's mutual definability (Thm 1.17), of which
this library has the easy half (`DescriptiveComplexity.arithDef_bit`: `BIT` from
`+` and `×`) and not the hard one (`×` from `BIT`). Two consequences worth
stating plainly:

* nothing here says the machine model is *weak*: it decides every prenex
  `FO(≤, +, BIT)` sentence, and by `DescriptiveComplexity.leSweep_accepts` and
  `DescriptiveComplexity.plusSweep_accepts` it computes the numeric predicates
  from bits rather than reading them;
* nothing here says it is *complete* for AC⁰ either, and the missing step is
  named rather than hidden: a sentence of `FO(≤, +, ×)` becomes a
  `DescriptiveComplexity.BitSentence` only if `×` is definable from `BIT` and
  the result is brought to prenex form – the first is the hard half of Thm 1.17,
  the second is a normal form Mathlib's `BoundedFormula` does not yet have.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### A prenex logic over bit-level atoms -/

/-- The atoms of the bit-level logic: the order, the addition of ranks, a
guarded bit, and an input relation at a tuple of variables. -/
inductive BitAtom (L : Language.{0, 0}) (m : ℕ) where
  /-- `x ≤ y`. -/
  | le (x y : Fin m) : BitAtom L m
  /-- `orank x + orank y = orank z`. -/
  | plus (x y z : Fin m) : BitAtom L m
  /-- `p` is a position and the bit of `x` there is set. -/
  | bit (p x : Fin m) : BitAtom L m
  /-- An input relation at a tuple of variables. -/
  | rel {a : ℕ} (R : L.Relations a) (arg : Fin a → Fin m) : BitAtom L m

/-- A quantifier-free kernel over the bit-level atoms. -/
inductive BitKernel (L : Language.{0, 0}) (m : ℕ) where
  /-- An atom. -/
  | atom (a : BitAtom L m) : BitKernel L m
  /-- Negation. -/
  | not (k : BitKernel L m) : BitKernel L m
  /-- Conjunction. -/
  | and (k k' : BitKernel L m) : BitKernel L m
  /-- Disjunction. -/
  | or (k k' : BitKernel L m) : BitKernel L m

/-- **A sentence of the bit-level logic, in prenex form**: a polarity per
variable and a quantifier-free kernel. Prenex by construction, which is what
makes the compilation into a machine a matter of atoms rather than of normal
forms. -/
structure BitSentence (L : Language.{0, 0}) where
  /-- The number of quantified variables. -/
  vars : ℕ
  /-- The quantifier at each variable: `true` existential, `false` universal. -/
  pol : Fin vars → Bool
  /-- The quantifier-free kernel. -/
  kernel : BitKernel L vars

namespace BitAtom

variable {L : Language.{0, 0}} {m : ℕ}

/-- What an atom says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitAtom L m → (Fin m → A) → Prop
  | .le x y, v => v x ≤ v y
  | .plus x y z, v => orank (v x) + orank (v y) = orank (v z)
  | .bit p x, v => IsPos (v p) ∧ BitAt (v p) (v x)
  | .rel R arg, v => RelMap R fun t => v (arg t)

/-- The base test an atom compiles to. -/
def compile : BitAtom L m → BaseTest L m
  | .le x y => .sweep (leSweep.relabel ![x, y])
  | .plus x y z => .sweep (plusSweep.relabel ![x, y, z])
  | .bit p x => .and (.sweep (oneBitSweep.relabel ![p]))
      (.sweep (impliesSweep.relabel ![p, x]))
  | .rel R arg => .query R arg

/-- **The compilation of an atom is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (a : BitAtom L m) (v : Fin m → A) : a.compile.Holds v ↔ a.Holds v := by
  cases a with
  | le x y =>
    have h : (leSweep.relabel ![x, y]).Accepts v ↔ leSweep.Accepts fun k => v (![x, y] k) :=
      Sweep.accepts_relabel _ _ _
    rw [show ((BitAtom.le x y : BitAtom L m).compile.Holds v) =
      (leSweep.relabel ![x, y]).Accepts v from rfl, h, leSweep_accepts]
    exact Iff.rfl
  | plus x y z =>
    have h : (plusSweep.relabel ![x, y, z]).Accepts v ↔
        plusSweep.Accepts fun k => v (![x, y, z] k) := Sweep.accepts_relabel _ _ _
    rw [show ((BitAtom.plus x y z : BitAtom L m).compile.Holds v) =
      (plusSweep.relabel ![x, y, z]).Accepts v from rfl, h, plusSweep_accepts]
    exact Iff.rfl
  | bit p x =>
    have h1 : (oneBitSweep.relabel ![p]).Accepts v ↔
        oneBitSweep.Accepts fun k => v (![p] k) := Sweep.accepts_relabel _ _ _
    have h2 : (impliesSweep.relabel ![p, x]).Accepts v ↔
        impliesSweep.Accepts fun k => v (![p, x] k) := Sweep.accepts_relabel _ _ _
    rw [show ((BitAtom.bit p x : BitAtom L m).compile.Holds v) =
      ((oneBitSweep.relabel ![p]).Accepts v ∧ (impliesSweep.relabel ![p, x]).Accepts v) from rfl,
      h1, h2, oneBitSweep_accepts, impliesSweep_accepts, Holds, bitAt_iff_bits]
    exact Iff.rfl
  | rel R arg => exact Iff.rfl

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {m : ℕ}

/-- What a kernel says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitKernel L m → (Fin m → A) → Prop
  | .atom a, v => a.Holds v
  | .not k, v => ¬ k.Holds v
  | .and k k', v => k.Holds v ∧ k'.Holds v
  | .or k k', v => k.Holds v ∨ k'.Holds v

/-- The base test a kernel compiles to: the Boolean structure is carried over
unchanged. -/
def compile : BitKernel L m → BaseTest L m
  | .atom a => a.compile
  | .not k => .not k.compile
  | .and k k' => .and k.compile k'.compile
  | .or k k' => .or k.compile k'.compile

/-- **The compilation of a kernel is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (k : BitKernel L m) (v : Fin m → A) : k.compile.Holds v ↔ k.Holds v := by
  induction k with
  | atom a => exact a.holds_compile v
  | not k ih => exact not_congr ih
  | and k k' ih ih' => exact and_congr ih ih'
  | or k k' ih ih' => exact or_congr ih ih'

end BitKernel

/-! ### The logic decided by the machines -/

namespace BitSentence

variable {L : Language.{0, 0}}

/-- What a sentence says of an instance: the prefix, played over the kernel. -/
def Holds (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A] [Finite A] : Prop :=
  prefixHolds (A := A) φ.vars φ.pol fun v => φ.kernel.Holds v

/-- The machine a sentence compiles to: the prefix *is* the register list. -/
def compile (φ : BitSentence L) : LTMachine L where
  regs := φ.vars
  pol := φ.pol
  base := φ.kernel.compile

/-- **The compilation of a sentence is correct**: the machine accepts exactly
the instances the sentence holds of. -/
theorem accepts_compile (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : φ.compile.Accepts A ↔ φ.Holds A :=
  prefixHolds_congr φ.vars φ.pol fun v => φ.kernel.holds_compile v

end BitSentence

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A decision problem is **bit-definable** when a prenex sentence over the
order, the addition and the guarded bit decides it on every nonempty finite
ordered structure. -/
def BitDefinable (P : DecisionProblem L) : Prop :=
  ∃ φ : BitSentence L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ φ.Holds A

/-- **The lower fence**: every prenex `FO(≤, +, BIT)` sentence is decided by a
machine with a logarithmic clock and a bit-level base. The atoms are the sweeps
of `DescriptiveComplexity.LogTime.Arith`, the quantifiers are the registers. -/
theorem BitDefinable.ltDecidable {P : DecisionProblem L} (h : BitDefinable P) :
    LTDecidable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.compile, fun A _ _ _ _ => ?_⟩
  rw [hφ A]
  exact (φ.accepts_compile A).symm

/-- **The sandwich**, one side: a bit-definable problem is AC⁰ definable,
through the machine. The other side – that every AC⁰ definable problem is
bit-definable – needs `×` from `BIT` and a prenex normal form, and is not
proved here. -/
theorem BitDefinable.ac0Definable {P : DecisionProblem L} (h : BitDefinable P) :
    AC0Definable P :=
  h.ltDecidable.ac0Definable

end DescriptiveComplexity
