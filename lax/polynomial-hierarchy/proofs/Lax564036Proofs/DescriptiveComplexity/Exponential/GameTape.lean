/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax564036Proofs.DescriptiveComplexity.Padding
import Lax564036Proofs.DescriptiveComplexity.Numbers.BinRel
import Lax564036Proofs.DescriptiveComplexity.OrderedComposition
import Lax564036Proofs.DescriptiveComplexity.SecondOrder
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Machines (MinPos SuccPos)
end Lax564036Proofs.DescriptiveComplexity

/-!
# The tape of a machine playing a second-order game

The layout half of `SO-GAME ≤ʳᶠᵒ[≤] ATMAcceptSpace`: which tagged tuples the
emitted machine calls positions, in what order they sit, and what a tape *is*.

## The layout

```
  ⊢₀ ⊢₁ | region 0: one cell per atom | region 1: one cell per atom | ⊣
```

A **cell** is `(region, relation variable i, ā)` with `ā` a tuple of `arity i`
elements of the instance, so the cells of one region are exactly the atoms of a
block assignment and a region *is* a point of the second-order game – `n^a`
bits, one tape's worth, which is the whole reason `APSPACE = EXPTIME`. The two
regions hold the current position and the candidate; their roles swap at each
move of the game, so nothing is ever copied.

**The two left sentinels** are there because `DescriptiveComplexity.TMData.Step`
has no stay-put option: every step moves the head, so the phases that do not
touch the tape have to bounce it somewhere harmless, and they bounce between
these two. Two of them exist whatever `|A|` is, because a sentinel tag pins
*every* coordinate to the minimum and so carries exactly one position. The right
sentinel does the same service for a step that runs off the last cell.

## A cell holds its own address

The symbol in the cell of the atom `i ā` of region `r` is not a bit but
`DescriptiveComplexity.valPt b r i ā`: the bit **together with the address of
the cell**. That is the one decision of the layout that is repaid several times
over, and it is available only because a tape here is a function
`A → A` into the *emitted universe*, so a symbol may carry a tuple.

> The machine never has to know where its head is.

Without it, every walk would have to carry the head's address in its state and
preserve the invariant *the tracked address is the head's position* – the
single most expensive invariant of a tape-walking reduction. With it:

* a **seek** to the cell of a computed atom walks right and stops when the
  symbol it *reads* carries the target address, which is a first-order
  condition on the transition's own tuple;
* a **sweep** writing a guessed assignment into region `r` needs no phase per
  region: the transitions that guess are the ones whose read symbol has region
  `r`, and those that copy back are the ones whose read symbol has region `!r`,
  so the machine's own alphabet decides which fires;
* the sentinels carry `DescriptiveComplexity.markPt`, a symbol of their own, so
  a walk knows it has reached an end by reading it, and the initial tape is
  first-order definable and *total* – which is what
  `DescriptiveComplexity.TMData.WellFormed` demands of the input.

## The order

A tag's `DescriptiveComplexity.TapeTag.fam` is what the order is designed
around – the five position families above, then the symbols, with the control
above all of them – and inside a family any fixed order will do, so the linear
order on tags is `(fam, an arbitrary tie-break)` read lexicographically
(`DescriptiveComplexity.machTagOrder`). No hand-built numbering of the
constructors is needed, and none of the control's tags has to be numbered at
all. On tuples the order is then `DescriptiveComplexity.tagTupleLe`, the tag
first and the coordinates lexicographically, which
`DescriptiveComplexity.OrderedComposition` already supplies and already proves
linear.

## The domain

The reduction is *relativized*, so a tag may pin the coordinates it does not
use: `DescriptiveComplexity.machDom` says every coordinate from a tag's own
arity on is a minimum (`DescriptiveComplexity.Canon`). That is what makes the
cells of variable `i` correspond to the atoms of `i` one for one, rather than
`n^{dim - arity i}` times over.
-/

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language

/-! ### The tags of the tape -/

/-- **The tags of the tape**: two left sentinels, one family of cells per
region and relation variable, a right sentinel, the symbols carrying a bit and
the address of their cell, and the sentinels' own symbol. -/
inductive TapeTag (B : Lax904597.SecondOrder.SOBlock) : Type
  /-- A left sentinel; `left false` is the lowest position of all. -/
  | left (b : Bool)
  /-- The cells of region `r` holding the relation variable `i`. -/
  | cell (r : Bool) (i : B.ι)
  /-- The right sentinel, the highest position. -/
  | right
  /-- The symbol of a cell: the bit `b`, and the address of the cell itself. -/
  | val (b r : Bool) (i : B.ι)
  /-- The symbol on the sentinels: `mark false` on the left pair, `mark true`
  on the right one, so that a walk can tell which end it has reached. -/
  | mark (b : Bool)

namespace TapeTag

variable {B : Lax904597.SecondOrder.SOBlock}

/-- The tape tags as a sum, for the `Finite` instance. -/
def equivSum : TapeTag B ≃ Bool ⊕ (Bool × B.ι) ⊕ Unit ⊕ (Bool × Bool × B.ι) ⊕ Bool where
  toFun
    | .left b => .inl b
    | .cell r i => .inr (.inl (r, i))
    | .right => .inr (.inr (.inl ()))
    | .val b r i => .inr (.inr (.inr (.inl (b, r, i))))
    | .mark b => .inr (.inr (.inr (.inr b)))
  invFun
    | .inl b => .left b
    | .inr (.inl (r, i)) => .cell r i
    | .inr (.inr (.inl ())) => .right
    | .inr (.inr (.inr (.inl (b, r, i)))) => .val b r i
    | .inr (.inr (.inr (.inr b))) => .mark b
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | (_ | (_ | (_ | _))) <;> rfl

instance : Finite (TapeTag B) := Finite.of_equiv _ equivSum.symm

instance : Nonempty (TapeTag B) := ⟨.mark false⟩

/-- **The family of a tag**, which is what the order of the tape is designed
around: the sentinels, then the cells of region `0`, then those of region `1`,
then the right sentinel, then the symbols. -/
def fam : TapeTag B → ℕ
  | .left false => 0
  | .left true => 1
  | .cell false _ => 2
  | .cell true _ => 3
  | .right => 4
  | .val _ _ _ => 5
  | .mark _ => 6

/-- The number of coordinates a tag uses: an address for a cell and for the
symbol of a cell, none for a sentinel or the mark. -/
def arity : TapeTag B → ℕ
  | .cell _ i => B.arity i
  | .val _ _ i => B.arity i
  | _ => 0

/-- Being a position: the sentinels and the cells, not the symbols. -/
def IsPos : TapeTag B → Prop
  | .val _ _ _ => False
  | .mark _ => False
  | _ => True

end TapeTag

/-! ### The tags of the machine, and their order -/

/-- **The tags of the machine**: the tape's, and the control's. The control is
a parameter, so this file fixes the tape without committing to the phases. -/
abbrev MachTag (B : Lax904597.SecondOrder.SOBlock) (C : Type) : Type := TapeTag B ⊕ C

namespace MachTag

variable {B : Lax904597.SecondOrder.SOBlock} {C : Type}

/-- The family of a machine tag: the control sits above the whole tape. -/
def fam : MachTag B C → ℕ := Sum.elim TapeTag.fam fun _ => 7

/-- Being a position: only the tape's positions are. -/
def IsPos : MachTag B C → Prop := Sum.elim TapeTag.IsPos fun _ => False

/-- The number of coordinates a tag uses, the control's arities being given. -/
def arity (carity : C → ℕ) : MachTag B C → ℕ := Sum.elim TapeTag.arity carity

@[simp] theorem fam_inl (t : TapeTag B) : fam (Sum.inl t : MachTag B C) = TapeTag.fam t := rfl

@[simp] theorem isPos_inl (t : TapeTag B) :
    IsPos (Sum.inl t : MachTag B C) = TapeTag.IsPos t := rfl

@[simp] theorem isPos_inr (c : C) : IsPos (Sum.inr c : MachTag B C) = False := rfl

@[simp] theorem arity_inl (carity : C → ℕ) (t : TapeTag B) :
    arity carity (Sum.inl t : MachTag B C) = TapeTag.arity t := rfl

end MachTag

/-- An arbitrary injection of a finite type into `ℕ`, used only to break ties
inside a family of tags. -/
noncomputable def finiteIdx (T : Type) [Finite T] (t : T) : ℕ :=
  letI := Fintype.ofFinite T
  (Fintype.equivFin T t : ℕ)

theorem finiteIdx_injective (T : Type) [Finite T] : Function.Injective (finiteIdx T) := by
  let := Fintype.ofFinite T
  intro a b h
  exact (Fintype.equivFin T).injective (Fin.ext h)

section Order

variable {B : Lax904597.SecondOrder.SOBlock} {C : Type} [Finite C]

/-- The sort key of a machine tag: its family, then an arbitrary tie-break,
read lexicographically. Only the family is designed. -/
noncomputable def machKey (t : MachTag B C) : ℕ ×ₗ ℕ :=
  toLex (MachTag.fam t, finiteIdx (MachTag B C) t)

theorem machKey_injective : Function.Injective (machKey (B := B) (C := C)) := fun _ _ h =>
  finiteIdx_injective _ (congrArg Prod.snd (toLex.injective h))

/-- **The order on the machine's tags**: by family, then arbitrarily. -/
@[instance_reducible]
noncomputable def machTagOrder : LinearOrder (MachTag B C) :=
  LinearOrder.lift' machKey machKey_injective

end Order

/-! ### The points of the emitted universe -/

section Points

variable {B : Lax904597.SecondOrder.SOBlock} {C : Type} {dim : ℕ} {A : Type} [LinearOrder A]

/-- A tagged tuple of the emitted universe, before the domain is imposed. -/
abbrev Pt (B : Lax904597.SecondOrder.SOBlock) (C : Type) (dim : ℕ) (A : Type) : Type := MachTag B C × (Fin dim → A)

/-- **The domain of the reduction**: every coordinate a tag does not use is a
minimum, so that a cell of the relation variable `i` corresponds to exactly one
atom of `i`. -/
def machDom (carity : C → ℕ) (p : Pt B C dim A) : Prop :=
  Canon (MachTag.arity carity p.1) p.2

/-- Being a position of the tape. -/
def machPosn (p : Pt B C dim A) : Prop := MachTag.IsPos p.1

variable (a₀ : A)

/-- **The symbol of that cell**: the bit `b`, together with the address of the
cell it sits in. -/
def valPt (b r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) : Pt B C dim A :=
  (Sum.inl (.val b r i), pad a₀ ā)

/-- The symbol on the sentinels: `markPt a₀ false` on the left pair,
`markPt a₀ true` on the right one. The blank is `markPt a₀ false`. -/
def markPt (b : Bool) : Pt B C dim A := (Sum.inl (.mark b), fun _ => a₀)

end Points

/-! ### The ends of the tape -/

section Ends

end Ends

/-! ### A tape is a pair of assignments -/

section Tape

variable {B : Lax904597.SecondOrder.SOBlock} {C : Type} {dim : ℕ} {A : Type} (a₀ : A)

open Classical in
/-- **The tape holding two assignments**: the first in region `0`, the second in
region `1`, each cell carrying its own address, the mark everywhere else. -/
noncomputable def tapeOfAssign (hdim : blockArityBound B ≤ dim) (ρ σ : B.Assignment A) :
    Pt B C dim A → Pt B C dim A := fun p =>
  match p.1 with
  | Sum.inl (.cell r i) =>
      valPt a₀ (decide (cond r σ ρ i (pref ((arity_le_blockArityBound B i).trans hdim) p.2))) r i
        (pref ((arity_le_blockArityBound B i).trans hdim) p.2)
  | Sum.inl .right => markPt a₀ true
  | _ => markPt a₀ false

end Tape

/-! ### One cell of an assignment, rewritten -/

section Update

end Update

/-! ### A tape is only ever read at a position -/

section Agree

end Agree

/-! ### The initial tape -/

section Init

variable {B : Lax904597.SecondOrder.SOBlock} {C : Type} {dim : ℕ} {A : Type} (a₀ : A)
  (hdim : blockArityBound B ≤ dim)

variable (B A) in
/-- The empty assignment. Named rather than written as a lambda, because
`DescriptiveComplexity.SOBlock.Assignment` is a non-reducible `def` and a
lambda literal in that position is ill-typed at `implicit` transparency, which
makes `rw` fail. -/
def emptyAssign : B.Assignment A := fun _ _ => False

/-- **The initial tape**: both regions empty, the sentinels marked. -/
noncomputable def gameInitTape : Pt B C dim A → Pt B C dim A :=
  tapeOfAssign a₀ hdim (emptyAssign B A) (emptyAssign B A)

/-- **The input of the machine**: which symbol each position starts with. It is
*total* on the positions – every cell starts empty rather than blank – which is
what makes it functional, as
`DescriptiveComplexity.TMData.WellFormed` demands, and what pins the initial
configuration. -/
def machInp (p x : Pt B C dim A) : Prop := machPosn p ∧ x = gameInitTape a₀ hdim p

end Init

end Lax564036Proofs.DescriptiveComplexity


