/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.FixedPointPartialMachine

/-!
# Second-order fixed points: SO(LFP) and SO(PFP)

> A **second-order** fixed point is a first-order fixed point **read over a
> structure whose universe is the assignments of a second-order block**.

A relation over an exponential expansion of `A` is a set of tuples of
second-order objects of `A`, so iterating a definable operator on it is a
second-order induction; and the first-order fixpoint logics, read there, are
the second-order ones. That is the definition of
`DescriptiveComplexity.SOLFPDefinable` and
`DescriptiveComplexity.SOPFPDefinable`, and the two classes
`DescriptiveComplexity.EXPTIME` and `DescriptiveComplexity.EXPSPACE` are named
after them.

**No third-order syntax is introduced**, and none is needed. The fixpoint
variable of SO(LFP) is a relation over the expanded universe, hence a
third-order object over `A`; but the expansion has already made those objects
the first-order elements of a new sort, so the syntax is the ordinary
`FirstOrder.Language.BoundedFormula` layer and the fixpoint is the ordinary
`DescriptiveComplexity.LFPDefinable`. This is the standard type-lowering
translation of higher-order logic into many-sorted first-order logic over the
power type ([Henkin 1950][henkin1950completeness]), which is why “SO(LFP) over
`A`” and “FO(LFP) over the expansion of `A`” are two presentations of one
object.

## The bridge theorems

`DescriptiveComplexity.solfpDefinable_iff_expDefinable` and
`DescriptiveComplexity.sopfpDefinable_iff_expDefinable` say that the two logics
are `DescriptiveComplexity.ExpDefinable` at `PTIME` and at `PSPACE`. Each is a
congruence down to the library's own capture theorem
(`DescriptiveComplexity.lfpDefinable_iff_mem_PTIME`,
`DescriptiveComplexity.pfpDefinable_iff_mem_PSPACE`) applied at the expanded
vocabulary, which is relational by the `eRelational` field of an expansion.
There is no mathematics in them, and that is the point of the design: they let
every later statement be proved once, about
`DescriptiveComplexity.ComplexityClass.exp` at an arbitrary class, and read off
at the exponential classes.

## Literature

These are *definitions* here, so nothing is claimed. Naming the classes after
these logics follows [Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint], which
parameterizes fixpoint logic by operator and iteration construct and obtains
characterizations up to EXPTIME. That work is stated in the *relational*
(order-free, generic) setting, so it must not be cited as a capture theorem for
the classes defined here; what this development proves in its place are the
bridge theorems above, which are about this library's own classes and owe the
literature nothing. The order these two definitions carry is nevertheless
removable (`DescriptiveComplexity.solfpDefinable_iff_free`,
`DescriptiveComplexity.sopfpDefinable_iff_free`): the expansion can guess it,
and the resulting union of copies costs one existential – paid for by guessing
the copy in `DescriptiveComplexity.Exponential.FreeSpace`, and by naming it with
a point in `DescriptiveComplexity.Exponential.FreeTime`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The two logics -/

/-- **SO(≤, LFP)**: a least fixed point over a second-order universe. The
problem holds of `A` exactly when an FO(≤, LFP) definition holds of an
exponential expansion of `A`. The order the expansion's own sentences read can
be removed (`DescriptiveComplexity.solfpDefinable_iff_free`), by guessing it
into the block. -/
def SOLFPDefinable (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), LFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

/-- **SO(≤, PFP)**: a partial fixed point over a second-order universe. The
order the expansion's own sentences read can be removed
(`DescriptiveComplexity.sopfpDefinable_iff_free`), by guessing it into the
block. -/
def SOPFPDefinable (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), PFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

/-! ### The bridge theorems -/

/-- **SO(≤, LFP) is polynomial time over an expanded universe**: the
Immerman–Vardi capture theorem, read at the expanded vocabulary. -/
theorem solfpDefinable_iff_expDefinable (P : DecisionProblem L) :
    SOLFPDefinable P ↔ ExpDefinable PTIME P :=
  exists_congr fun _X => exists_congr fun Q =>
    and_congr_left' (lfpDefinable_iff_mem_PTIME Q)

/-- **SO(≤, PFP) is polynomial space over an expanded universe**: the
Abiteboul–Vianu capture theorem, read at the expanded vocabulary. -/
theorem sopfpDefinable_iff_expDefinable (P : DecisionProblem L) :
    SOPFPDefinable P ↔ ExpDefinable PSPACE P :=
  exists_congr fun _X => exists_congr fun Q =>
    and_congr_left' (pfpDefinable_iff_mem_PSPACE Q)

/-! ### Closure under reductions, inherited

The three membership obligations of
`DescriptiveComplexity.ComplexityClass.ofMem` are *borrowed* through the bridge
theorems rather than proved: `DescriptiveComplexity.Exponential.Class` proved
them once, for `ExpDefinable C` at an arbitrary `C`. -/

variable {L' : Language.{0, 0}} [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

theorem SOLFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : SOLFPDefinable Q) :
    SOLFPDefinable P :=
  (solfpDefinable_iff_expDefinable P).mpr
    (((solfpDefinable_iff_expDefinable Q).mp h).of_foReduction f)

theorem SOLFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : SOLFPDefinable Q) :
    SOLFPDefinable P :=
  (solfpDefinable_iff_expDefinable P).mpr
    (((solfpDefinable_iff_expDefinable Q).mp h).of_orderedReduction f)

theorem solfpDefinable_congr {P P' : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) :
    SOLFPDefinable P ↔ SOLFPDefinable P' :=
  (solfpDefinable_iff_expDefinable P).trans
    ((expDefinable_congr h).trans (solfpDefinable_iff_expDefinable P').symm)

theorem SOPFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : SOPFPDefinable Q) :
    SOPFPDefinable P :=
  (sopfpDefinable_iff_expDefinable P).mpr
    (((sopfpDefinable_iff_expDefinable Q).mp h).of_foReduction f)

theorem SOPFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : SOPFPDefinable Q) :
    SOPFPDefinable P :=
  (sopfpDefinable_iff_expDefinable P).mpr
    (((sopfpDefinable_iff_expDefinable Q).mp h).of_orderedReduction f)

theorem sopfpDefinable_congr {P P' : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) :
    SOPFPDefinable P ↔ SOPFPDefinable P' :=
  (sopfpDefinable_iff_expDefinable P).trans
    ((expDefinable_congr h).trans (sopfpDefinable_iff_expDefinable P').symm)

end DescriptiveComplexity
