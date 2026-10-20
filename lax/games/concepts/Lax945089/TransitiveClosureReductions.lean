import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Relation
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.SecondOrder
import Lax535992.InflationaryFixedPoint

/-!
---
title: Reductions in first-order logic with a deterministic transitive closure
type: definition
---
A parameterized walk over a vocabulary is a finite set of modes, an arity
$k$, a number of parameters, and a step formula for each pair of modes, in
two $k$-tuples of variables and the parameters; at a valuation of the
parameters it defines a graph on the pairs of a mode and a $k$-tuple, and
its reachability relation. Its determinization keeps only the steps that
are alone in leaving their node. A finite family of walks gives one
relation variable per walk and pair of modes, holding the reachability
relation between two nodes of these modes at given parameters.

An FO(DTC) reduction from a problem $P$ to a problem $Q$ consists of a
finite family of walks over the ordered expansion of the vocabulary of $P$
and a relativized first-order interpretation whose formulas may use, beside
the vocabulary and the order, the reachability relations of the
determinized walks. For every nonempty finite structure and every linear
order on it, the interpreted structure must be nonempty and be a
yes-instance of $Q$ exactly when the structure is a yes-instance of $P$.
This is Immerman's logical form of a deterministic logarithmic-space
reduction.
-/

namespace Lax945089.TransitiveClosureReductions

open Lax904597.Problems Lax904597.Relativized Lax904597.SecondOrder
open Lax535992.InflationaryFixedPoint

open FirstOrder

open Language Structure

/-- A **parameterized transitive-closure specification**: a walk on `k`-tuples
carrying a finite mode, whose step formula may mention `par` parameters beside
the current and the next tuple. It has no source and target formulas: what it
defines is the reachability *relation*. -/
structure ParamTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The modes: the finite control the walk carries beside its tuple. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The number of parameters the step formula may mention. -/
  par : ℕ
  /-- The step formula, one per pair of modes: the current tuple, the next
  tuple, then the parameters. -/
  step : Mode → Mode → L.Formula ((Fin k ⊕ Fin k) ⊕ Fin par)

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L) {A : Type} [L.Structure A]

attribute [instance] modeFinite

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple. -/
abbrev Node : Type := s.Mode × (Fin s.k → A)

/-- One step of the walk, at a valuation of the parameters. -/
def StepAt (z : Fin s.par → A) (a b : s.Node A) : Prop :=
  (s.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) z)

/-- Reachability in the walk, at a valuation of the parameters. -/
abbrev ReachAt (z : Fin s.par → A) : s.Node A → s.Node A → Prop :=
  Relation.ReflTransGen (s.StepAt z)

/-- The position of the `i`-th coordinate of the *first* tuple. -/
def leftIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨i, by have := i.isLt; omega⟩

/-- The position of the `i`-th coordinate of the *second* tuple. -/
def rightIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨s.k + i, by have := i.isLt; omega⟩

/-- The position of the `j`-th parameter. -/
def parIx (j : Fin s.par) : Fin (s.k + s.k + s.par) := ⟨s.k + s.k + j, by have := j.isLt; omega⟩

end ParamTCSpec

/-- A finite family of parameterized walks. Its relation variables – one per
walk and ordered pair of that walk's modes – are what an FO(TC) reduction's
formulas may read. -/
structure TCFamily (L : Language.{0, 0}) : Type 1 where
  /-- The index type of the family. -/
  Ix : Type
  /-- The family is finite. -/
  [ixFinite : Finite Ix]
  /-- The walk of each index. -/
  spec : Ix → ParamTCSpec L

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

attribute [instance] ixFinite

/-- The block of relation variables of a family: one variable per walk and
ordered pair of modes, of arity “two tuples and the parameters”. -/
def block : SOBlock where
  ι := Σ i : F.Ix, (F.spec i).Mode × (F.spec i).Mode
  arity := fun q => (F.spec q.1).k + (F.spec q.1).k + (F.spec q.1).par

variable {F} {A : Type} [L.Structure A]

/-- The assignment the block *has*, as opposed to one a second-order
quantifier would guess: each variable holds the reachability relation of its
walk, at the parameters read off the tuple. -/
def reachAssign (F : TCFamily L) (A : Type) [L.Structure A] : F.block.Assignment A :=
  fun q w =>
    (F.spec q.1).ReachAt (fun j => w ((F.spec q.1).parIx j))
      (q.2.1, fun i => w ((F.spec q.1).leftIx i))
      (q.2.2, fun i => w ((F.spec q.1).rightIx i))

end TCFamily

open FirstOrder

open Language Structure

/-- An **FO(TC) interpretation**: a relativized first-order interpretation
whose formulas may read the reachability relations of a finite family of
first-order walks over the base structure.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's FO(TC)
reduction, the logical form of a logarithmic-space reduction. -/
structure TCInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The walks whose reachability relations the formulas may read. -/
  fam : TCFamily L
  /-- The interpretation, over the base vocabulary expanded by the walks'
  relation variables. -/
  toRel : RelFOInterpretation (L.sum fam.block.lang) L' Tag dim

namespace TCInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : TCInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The base structure expanded by the reachability relations of the walks –
the structure the interpretation is read over. -/
@[reducible]
def expStructure : (L.sum I.fam.block.lang).Structure A :=
  SOBlock.structure₁ (L := L) I.fam.block (I.fam.reachAssign A)

/-- The universe of the interpreted structure. -/
def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A

/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  RelFOInterpretation.mapRelStructure I.toRel A

end TCInterpretation

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L)

/-- The renaming used by the uniqueness clause: the step formula is re-read
with its first tuple still the current one, its second tuple the freshly
quantified `w̄`, and its parameters unchanged. -/
def detVar : ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) → (((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) ⊕ Fin s.k)
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr i) => Sum.inr i
  | Sum.inr j => Sum.inl (Sum.inr j)

open Classical in
/-- **The determinized step formula** at a pair of modes: this step, and no
other step out of the current node. As in
`TCSpec.detStep`, the competing successor's mode is
compared statically, so the uniqueness clause has one conjunct per mode. -/
noncomputable def detStep (m n : s.Mode) : L.Formula ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) :=
  s.step m n ⊓
    Formula.iInf fun m' : s.Mode =>
      Formula.iAlls (Fin s.k)
        (((s.step m m').relabel s.detVar).imp
          (if m' = n then
            Formula.iInf fun i : Fin s.k =>
              Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (Sum.inl (Sum.inr i))))
          else ⊥))

/-- **The deterministic reading of a walk**: the same modes, arity and
parameters, with the step formula replaced by its determinization.

Reducible, so that the modes, the arity, and the parameter count of `s.det` are
those of `s` transparently – a node of the deterministic reading *is* a node,
and the block of a determinized family *is* the block of the family. -/
@[reducible]
noncomputable def det : ParamTCSpec L where
  Mode := s.Mode
  k := s.k
  par := s.par
  step := s.detStep

end ParamTCSpec

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

/-- The deterministic reading of a family: every walk read through its
determinization. Reducible, so that `F.det.block` *is* `F.block`. -/
@[reducible]
noncomputable def det : TCFamily L where
  Ix := F.Ix
  spec := fun i => (F.spec i).det

end TCFamily

/-- An **FO(DTC) reduction** from `P` to `Q` – a deterministic
logarithmic-space reduction, in the logical form of Immerman: an interpretation over the ordered
expansion whose formulas may read the reachability relations of a family of
walks, each read through its determinization. -/
structure DTCReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The walks the formulas may read – *before* determinization, which is how
  they are read. -/
  fam : TCFamily (L.sum Language.order)
  /-- The interpretation, over the base expanded by the walks' relation
  variables. -/
  toRel : RelFOInterpretation ((L.sum Language.order).sum fam.block.lang) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (TCInterpretation.Map ⟨fam.det, toRel⟩ A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (TCInterpretation.Map ⟨fam.det, toRel⟩ A)

end Lax945089.TransitiveClosureReductions
