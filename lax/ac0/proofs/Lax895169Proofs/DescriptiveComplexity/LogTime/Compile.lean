/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax895169Proofs.DescriptiveComplexity.LogTime.Arith
import Lax895169Proofs.DescriptiveComplexity.LogTime.BitLogic
import Lax895169Proofs.DescriptiveComplexity.LogTime.Simulate
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax895169.BitLogic
end Lax895169.BitLogic

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169.LogTimeMachines
end Lax895169.LogTimeMachines

namespace Lax895169Proofs.DescriptiveComplexity.BitAtom
end Lax895169Proofs.DescriptiveComplexity.BitAtom

namespace Lax895169Proofs.DescriptiveComplexity.BitDefinable
end Lax895169Proofs.DescriptiveComplexity.BitDefinable

namespace Lax895169Proofs.DescriptiveComplexity.BitKernel
end Lax895169Proofs.DescriptiveComplexity.BitKernel

namespace Lax895169Proofs.DescriptiveComplexity.BitSentence
end Lax895169Proofs.DescriptiveComplexity.BitSentence

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (BitIx orank posCount)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.BitLogic (BitAtom BitDefinable BitKernel BitSentence)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax895169.LogTimeMachines (BaseTest LTDecidable LTMachine)
end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax895169Proofs.DescriptiveComplexity

/-!
# The lower fence: a bit-level prenex logic, compiled into machines

`DescriptiveComplexity.LTDecidable.bitDefinable` puts the machine model inside
the bit-level logic. This file puts that logic back inside the machine model, so
that the fence is an **equality** and the picture is

prenex `FO(≤, +, BIT)`  =  constant-alternation logarithmic time.

`DescriptiveComplexity.ltDecidable_iff_bitDefinable` is that equality: the
machine model of this development is exactly characterized by a logic, with no
normal form left to apply and no gap left to name on either side of it.

## The logic

`DescriptiveComplexity.BitSentence`: a quantifier prefix – a polarity per
variable, exactly the shape a machine's registers have – over a quantifier-free
kernel built from four atoms (`DescriptiveComplexity.BitAtom`): the order, the
addition of ranks, an input relation at a tuple of variables, and the bit
`BitIx i x` of `x` at the index `i`.

That last atom is where the model gets its power, and it is a *read* rather than
a computation: the machine has the index in a register and addresses the bit
there (`DescriptiveComplexity.BaseTest.bit`). No sweep can do it – locating the
position `orank i` means counting positions, and an automaton carrying a constant
number of bits cannot – which is exactly why it is a primitive and not a
construction.

## The addition is a derived predicate

`DescriptiveComplexity.bitDef_plus_free`: the atom
`DescriptiveComplexity.BitAtom.plus` is redundant. `orank x + orank y = orank z`
is bit-definable from the order and the bit atom alone, by carry-lookahead
(`DescriptiveComplexity.plus_iff_bits`), so the logic of this file is
`FO(≤, BIT)` under another name – its classical name, and in the sharpest sense,
since `≤` is itself first-order definable from `BIT` alone, whence
`FO(BIT) = FO(≤, BIT)` ([Dawar, Doets, Lindell & Weinstein
1998][dawar1998finiteranks] Thm. 2.1 and Cor. 2.3: `BIT` is Ackermann
membership, `(A, BIT)` is an ∈-initial segment of the hereditarily finite sets,
and one formula defines the order on all of them – it guesses the order relation
itself as an *element*, a set of pairs, and checks it is a post-fixed point of
the “greatest differing member” operator). That elimination is neither used nor
proved here: every structure in this library carries its order anyway. The atom
stays all the same:
`DescriptiveComplexity.plusSweep_accepts` is half of what shows the machine has
to *build* its arithmetic rather than read it, and deleting the atom would delete
that demonstration for no theorem.

The lookahead is also where the index naming shows: the carry into position `i`
is “some `j < i` generates one, and every `k` strictly between propagates it”,
with `j` and `k` ordinary elements compared by `≤`. Under the place-value naming
each of those quantifiers had to be relativized to the powers of two.

## The compilation

Atom by atom, with the sweeps already built: `≤` is `leSweep`, `+` is
`plusSweep`, the bit atom is the machine's read, and an input relation is a
query. `DescriptiveComplexity.Sweep.relabel` is what lets a sweep written once
for two or three registers be run on any registers of the machine. The Boolean
structure of the kernel becomes the Boolean structure of the base test, and the
quantifier prefix becomes the register list unchanged – there is nothing to
prenexify, because the source syntax is prenex by construction.

## What is closed, and what is not

The equality with the logic is closed on both sides. The identification of that
logic with `FO(≤, +, ×)`, that is, with `DescriptiveComplexity.AC0Definable`, is
[Immerman 1999][immerman1999descriptive] Thm 1.17, one named theorem per
direction:

* `FO(≤, +, BIT) ⊆ FO(≤, +, ×)` is `DescriptiveComplexity.powArithDef`, the
  definability of `i ↦ 2 ^ i`, which is **proved**
  (`DescriptiveComplexity.LogTime.Pow`), so
  `DescriptiveComplexity.BitDefinable.ac0Definable` is unconditional;
* `FO(≤, +, ×) ⊆ FO(≤, +, BIT)` is the Bit Sum Lemma, the counting argument that
  eliminates `×` in favor of the bit atom, and it is **not** built.

Neither is a defect of the machine: they are statements about two vocabularies,
and the machine is exactly the one of them that a machine can be.
-/

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitAtom

variable {L : Language.{0, 0}} {m : ℕ}

/-- The base test an atom compiles to. -/
def compile : Lax895169.BitLogic.BitAtom L (Fin m) → Lax895169.LogTimeMachines.BaseTest L m
  | .le x y => .sweep (leSweep.relabel ![x, y])
  | .plus x y z => .sweep (plusSweep.relabel ![x, y, z])
  | .bit i x => .bit i x
  | .rel R arg => .query R arg

end BitAtom

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitAtom

export Lax895169Proofs.DescriptiveComplexity.BitAtom (compile)

end Lax895169.BitLogic.BitAtom

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitAtom

variable {L : Language.{0, 0}} {m : ℕ}

/-- **The compilation of an atom is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (a : Lax895169.BitLogic.BitAtom L (Fin m)) (v : Fin m → A) : a.compile.Holds v ↔ a.Holds v := by
  cases a with
  | le x y =>
    have h : (leSweep.relabel ![x, y]).Accepts v ↔ leSweep.Accepts fun k => v (![x, y] k) :=
      Sweep.accepts_relabel _ _ _
    rw [show ((Lax895169.BitLogic.BitAtom.le x y : Lax895169.BitLogic.BitAtom L (Fin m)).compile.Holds v) =
      (leSweep.relabel ![x, y]).Accepts v from rfl, h, leSweep_accepts]
    exact Iff.rfl
  | plus x y z =>
    have h : (plusSweep.relabel ![x, y, z]).Accepts v ↔
        plusSweep.Accepts fun k => v (![x, y, z] k) := Sweep.accepts_relabel _ _ _
    rw [show ((Lax895169.BitLogic.BitAtom.plus x y z : Lax895169.BitLogic.BitAtom L (Fin m)).compile.Holds v) =
      (plusSweep.relabel ![x, y, z]).Accepts v from rfl, h, plusSweep_accepts]
    exact Iff.rfl
  | bit i x => exact Iff.rfl
  | rel R arg => exact Iff.rfl

end BitAtom

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitAtom

export Lax895169Proofs.DescriptiveComplexity.BitAtom (holds_compile)

end Lax895169.BitLogic.BitAtom

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitAtom

variable {L : Language.{0, 0}} {m : ℕ}

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {m : ℕ}

/-- The base test a kernel compiles to: the Boolean structure is carried over
unchanged. -/
def compile : Lax895169.BitLogic.BitKernel L (Fin m) → Lax895169.LogTimeMachines.BaseTest L m
  | .atom a => a.compile
  | .tt => .sweep (trueSweep.relabel Fin.elim0)
  | .not k => .not (compile k)
  | .and k k' => .and (compile k) (compile k')
  | .or k k' => .or (compile k) (compile k')

end BitKernel

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitKernel

export Lax895169Proofs.DescriptiveComplexity.BitKernel (compile)

end Lax895169.BitLogic.BitKernel

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitKernel

variable {L : Language.{0, 0}} {m : ℕ}

/-- **The compilation of a kernel is correct.** -/
theorem holds_compile {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
    (k : Lax895169.BitLogic.BitKernel L (Fin m)) (v : Fin m → A) : k.compile.Holds v ↔ k.Holds v := by
  induction k with
  | atom a => exact a.holds_compile v
  | tt => exact ⟨fun _ => trivial, fun _ => (Sweep.accepts_relabel _ _ _).mpr rfl⟩
  | not k ih => exact not_congr ih
  | and k k' ih ih' => exact and_congr ih ih'
  | or k k' ih ih' => exact or_congr ih ih'

end BitKernel

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitKernel

export Lax895169Proofs.DescriptiveComplexity.BitKernel (holds_compile)

end Lax895169.BitLogic.BitKernel

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitKernel

variable {L : Language.{0, 0}} {m : ℕ}

end BitKernel

/-! ### The logic decided by the machines -/

namespace BitSentence

variable {L : Language.{0, 0}}

/-- The machine a sentence compiles to: the prefix *is* the register list. -/
def compile (φ : Lax895169.BitLogic.BitSentence L) : Lax895169.LogTimeMachines.LTMachine L where
  regs := φ.vars
  pol := φ.pol
  base := φ.kernel.compile

end BitSentence

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitSentence

export Lax895169Proofs.DescriptiveComplexity.BitSentence (compile)

end Lax895169.BitLogic.BitSentence

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitSentence

variable {L : Language.{0, 0}}

/-- **The compilation of a sentence is correct**: the machine accepts exactly
the instances the sentence holds of. -/
theorem accepts_compile (φ : Lax895169.BitLogic.BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : φ.compile.Accepts A ↔ φ.Holds A :=
  prefixHolds_congr φ.vars φ.pol fun v => φ.kernel.holds_compile v

end BitSentence

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitSentence

export Lax895169Proofs.DescriptiveComplexity.BitSentence (accepts_compile)

end Lax895169.BitLogic.BitSentence

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace BitSentence

variable {L : Language.{0, 0}}

end BitSentence

/-! ### The addition is a derived predicate

`FO(≤, +, BIT) = FO(≤, BIT)`: the addition of ranks is expressed by the
carry-lookahead formula, a condition on the bits with no addition in it. The
atom is kept all the same – `plusSweep_accepts` is half of what shows the model
has to *build* its arithmetic rather than read it – so what this section settles
is a name, not an API. -/

section Carry

end Carry

section PlusFree

end PlusFree

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **The lower fence**: every prenex `FO(≤, +, BIT)` sentence is decided by a
machine with a logarithmic clock and a bit-level base. The order and the addition
are the sweeps of `DescriptiveComplexity.LogTime.Arith`, the bit is a read, and
the quantifiers are the registers. -/
theorem BitDefinable.ltDecidable {P : Lax904597.Problems.DecisionProblem L} (h : Lax895169.BitLogic.BitDefinable P) :
    Lax895169.LogTimeMachines.LTDecidable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.compile, fun A _ _ _ _ => ?_⟩
  rw [hφ A]
  exact (φ.accepts_compile A).symm

end Lax895169Proofs.DescriptiveComplexity

namespace Lax895169.BitLogic.BitDefinable

export Lax895169Proofs.DescriptiveComplexity.BitDefinable (ltDecidable)

end Lax895169.BitLogic.BitDefinable

namespace Lax895169Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax895169Proofs.DescriptiveComplexity


