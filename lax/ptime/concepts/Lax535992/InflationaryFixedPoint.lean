import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Function.Iterate
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.SecondOrder

/-!
---
title: First-order logic with inflationary fixed points
type: definition
---
A simultaneous induction over a vocabulary $L$ consists of a block of
relation variables $R_1, \dots, R_m$, a step formula $\varphi_i(\bar x)$
for each variable, an arbitrary first-order formula over $L$ expanded by
the block whose free variables are the arguments of $R_i$, and an output
sentence over the same expanded vocabulary. On an $L$-structure, the
inflationary iteration starts from the empty relations and at each stage
adds to every $R_i$ the tuples satisfying $\varphi_i$ at the current stage:
$R_i^0 = \emptyset$ and
$R_i^{n+1} = R_i^n \cup \{\bar a \mid \varphi_i(\bar a) \text{ holds at stage } n\}$.
Its limit is the union of the stages, and the induction holds on the
structure, read inflationarily, when the output sentence is true at the
limit. No positivity is required of the step formulas.

A decision problem $P$ over $L$ is FO($\le$, IFP) definable when some
simultaneous induction over $L \cup \{\le\}$ holds inflationarily, for
every nonempty finite $L$-structure $A$ and every linear order on $A$,
exactly when $A$ is a yes-instance of $P$.
-/

namespace Lax535992.InflationaryFixedPoint

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[reducible]
def SOBlock.structure₁ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

/-- The all-empty assignment of a block: the starting point of the
iteration. -/
def SOBlock.botAssign (B : SOBlock) (A : Type) : B.Assignment A :=
  fun _ _ => False

/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence

namespace StepDef

variable {L : Language.{0, 0}} (d : StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

/-- One application of the step formulas to an assignment. -/
def next (ρ : d.B.Assignment A) : d.B.Assignment A :=
  fun i x => @Formula.Realize _ A (SOBlock.structure₁ (L := L) d.B ρ) _ (d.step i) x

/-- The inflationary step: accumulate the step formulas into the previous
stage. -/
def inflStep (ρ : d.B.Assignment A) : d.B.Assignment A :=
  fun i x => ρ i x ∨ d.next ρ i x

variable (A) in
/-- The stages of the inflationary iteration. -/
def inflStage (n : ℕ) : d.B.Assignment A :=
  (d.inflStep)^[n] (SOBlock.botAssign d.B A)

variable (A) in
/-- The value of the inflationary iteration: the union of the stages. -/
def inflLimit : d.B.Assignment A :=
  fun i x => ∃ n, d.inflStage A n i x

end Semantics

/-- The value of a simultaneous induction read inflationarily: the output
sentence, at the limit of the inflationary iteration. -/
def IFPHolds (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L) d.B (d.inflLimit A)) d.out

end StepDef

/-- A decision problem is *FO(≤, IFP) definable* if, on nonempty finite
ordered structures, it is the value of a simultaneous induction over the
ordered expansion of its vocabulary, read inflationarily. The equivalence is
required for every linear order, so the notion is order-invariant: the
formulas see the order, the problem does not. -/
def IFPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef (L.sum Language.order),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ d.IFPHolds A

end Lax535992.InflationaryFixedPoint
