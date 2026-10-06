import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Mathlib.Dynamics.FixedPoints.Basic
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.SecondOrder
import Lax535992.InflationaryFixedPoint

/-!
---
title: First-order logic with partial fixed points
type: definition
---
A simultaneous induction, a block of relation variables with a first-order
step formula per variable and an output sentence, is read partially as
follows. The partial iteration starts from the empty relations and at each
stage replaces every relation by the set of tuples satisfying its step
formula at the current stage: $R_i^0 = \emptyset$ and
$R_i^{n+1} = \{\bar a \mid \varphi_i(\bar a) \text{ holds at stage } n\}$.
Nothing is accumulated, so the stages need not converge. The induction holds
on a structure, read partially, when some stage is a fixed point of the
step and the output sentence is true at it; a diverging iteration holds
nowhere.

A decision problem $P$ over a vocabulary $L$ is FO($\le$, PFP) definable
when some simultaneous induction over $L \cup \{\le\}$ holds partially,
for every nonempty finite $L$-structure $A$ and every linear order on $A$,
exactly when $A$ is a yes-instance of $P$. It is order-free FO(PFP)
definable, respectively order-free FO(IFP) definable, when some
simultaneous induction over $L$ alone holds partially, respectively
inflationarily, on every nonempty finite $L$-structure exactly when it is a
yes-instance: the notions the Abiteboul–Vianu theorem compares.
-/

namespace Lax134656.PartialFixedPoint

open Lax535992.InflationaryFixedPoint Lax904597.Problems

open FirstOrder

open Language Structure

open Function (IsFixedPt)

namespace StepDef

section Semantics

variable {L : Language.{0, 0}} (d : StepDef L) {A : Type} [L.Structure A]

variable (A) in
/-- The stages of the partial iteration. -/
def partStage (n : ℕ) : d.B.Assignment A :=
  (d.next)^[n] (SOBlock.botAssign d.B A)

end Semantics

end StepDef

/-- A decision problem is *order-free FO(IFP) definable* if, on nonempty
finite structures, it is the value of a simultaneous induction over its own
vocabulary, read inflationarily. This is the unordered notion the
Abiteboul–Vianu theorem is about. -/
def IFPDefinableFree {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef L, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ d.IFPHolds A

namespace StepDef

/-- The value of a simultaneous induction read partially: some stage is a
fixed point of the step and satisfies the output sentence. All stable stages
are equal, so this says exactly «the iteration converges and its limit
satisfies the output». -/
def PFPHolds {L : Language.{0, 0}} (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  ∃ n, IsFixedPt d.next (partStage d A n) ∧
    @Sentence.Realize _ A (SOBlock.structure₁ (L := L) d.B (partStage d A n)) d.out

end StepDef

/-- A decision problem is *order-free FO(PFP) definable* if, on nonempty
finite structures, it is the value of a simultaneous induction over its own
vocabulary, read partially. This is the unordered notion on the fixed-point
side of the Abiteboul–Vianu theorem. -/
def PFPDefinableFree {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef L, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ StepDef.PFPHolds d A

/-- A decision problem is *FO(≤, PFP) definable* if, on nonempty finite
ordered structures, it is the value of a simultaneous induction over the
ordered expansion of its vocabulary, read partially – for every linear order,
the problem itself never seeing it. -/
def PFPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef (L.sum Language.order),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ StepDef.PFPHolds d A

end Lax134656.PartialFixedPoint
