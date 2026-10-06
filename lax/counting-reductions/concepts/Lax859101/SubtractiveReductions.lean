import Mathlib.Tactic.FinCases
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Lax366625.CountingProblems
import Lax366625.WitnessCounting
import Lax904597.Interpretations
import Lax904597.SecondOrder
import Lax366625.CountingClasses

/-!
---
title: Subtractive reductions
type: definition
---
A strong subtractive reduction from $C$ to $D$, after Durand, Hermann, and
Kolaitis, presents $D$ as the witness count of a kernel and draws two
instances of $D$ from an instance $A$ of $C$ by two first-order
interpretations with the same tags and dimension, a subtrahend and a
minuend, such that every witness at the subtrahend is a witness at the
minuend and $C(A) + D(I_s(A)) = D(I_m(A))$. Subtractive reducibility is a
finite chain of strong subtractive and relativized ordered parsimonious
steps. A counting problem is hard for a class when every member of the class
subtractively reduces to it, and complete when it is moreover a member.
-/

namespace Lax859101.SubtractiveReductions

open Lax366625.CountingProblems Lax366625.WitnessCounting Lax904597.Interpretations
open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

open FirstOrder

open Language Structure BoundedFormula

section LexFormulas

variable {L : Language.{0, 0}}

/-- `x = y`, as a formula over the ordered expansion. -/
def oEqF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x ≤ y`, as a formula over the ordered expansion. -/
def oLeF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x < y`, as a formula over the ordered expansion. -/
def oLtF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  oLeF x y ⊓ ∼(oEqF x y)

variable {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {v : α → A}

variable (L) in
/-- Lexicographic comparison of two `d`-tuples (the two arguments of a binary
relation), as a formula over the ordered expansion. -/
noncomputable def lexTupleLeF (d : ℕ) : (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  (Formula.iInf fun i : Fin d => oEqF (0, i) (1, i)) ⊔
    Formula.iSup fun j : Fin d =>
      (Formula.iInf fun i : {i : Fin d // i < j} => oEqF (0, i.1) (1, i.1)) ⊓
        oLtF (0, j) (1, j)

open Classical in
variable (L) in
/-- The full lexicographic comparison of tagged tuples, as a formula over the
ordered expansion: the tags are compared statically. -/
noncomputable def lexLeF {Tag : Type} [LinearOrder Tag] (d : ℕ) (t₁ t₂ : Tag) :
    (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  if t₁ = t₂ then lexTupleLeF L d else if t₁ < t₂ then ⊤ else ⊥

end LexFormulas

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]

variable {T : Type} [LinearOrder T] {d : ℕ}

/-- Extension of an interpretation over an ordered base to one whose target
carries the order vocabulary, interpreted by the lexicographic order on
tagged tuples. -/
noncomputable def FOInterpretation.ordExtend
    (I : FOInterpretation (L₁.sum Language.order) L₂ T d) :
    FOInterpretation (L₁.sum Language.order) (L₂.sum Language.order) T d where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => I.relFormula r
    | _, Sum.inr .le => fun t => lexLeF L₁ d (t 0) (t 1)

end OrdExtend

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

/-- The assignment `ρ` is a witness of the kernel `φ` at the instance drawn by
the interpretation `I`, ordered lexicographically. The universe of that
instance is `Tag × A ^ dim` whatever `I` is, so the witnesses at two
interpretations with the same tags and dimension are comparable. -/
def FOInterpretation.WitAt (I : FOInterpretation (L.sum Language.order) L' Tag dim)
    (B : SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] (ρ : B.Assignment (Tag × (Fin dim → A))) : Prop :=
  @Sentence.Realize ((L'.sum Language.order).sum B.lang) ((FOInterpretation.ordExtend I).Map A)
    (@sumStructure (L'.sum Language.order) B.lang ((FOInterpretation.ordExtend I).Map A)
      (FOInterpretation.mapStructure (FOInterpretation.ordExtend I) A)
        (B.structure ρ)) φ

end WitAt

/-- A **strong subtractive reduction**: the target is presented as the witness
count of a kernel, two interpretations with the same tags and dimension draw a
subtrahend and a minuend, every witness at the first is a witness at the
second, and the count of the source is the difference of the two counts. -/
structure StrongSubtractiveReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the two interpretations. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- Tags are linearly ordered: the order of the drawn instances is the
  lexicographic one. -/
  [tagOrder : LinearOrder Tag]
  /-- The dimension of the two interpretations. -/
  dim : ℕ
  /-- The second-order block of the presentation of the target. -/
  block : SOBlock
  /-- The first-order kernel of the presentation of the target. -/
  kernel : ((L'.sum Language.order).sum block.lang).Sentence
  /-- The target counts the witnesses of its presentation, whatever the linear
  order. -/
  present : ∀ (A : Type) [L'.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    D A = witnessCount block kernel A
  /-- The interpretation drawing the subtrahend. -/
  subtrahend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpretation drawing the minuend. -/
  minuend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Every witness at the subtrahend is a witness at the minuend. -/
  witness_le : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ρ : block.Assignment (Tag × (Fin dim → A))),
    FOInterpretation.WitAt subtrahend block kernel A ρ →
      FOInterpretation.WitAt minuend block kernel A ρ
  /-- The count of the source and the count at the subtrahend add up to the
  count at the minuend. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A + D (subtrahend.Map A) = D (minuend.Map A)

/-- **Subtractive reducibility**, `C ≤ˢ D`: a finite chain of steps, each a
strong subtractive reduction or a relativized ordered parsimonious
reduction. -/
inductive SubtractiveReducible : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational],
    CountingProblem L → CountingProblem L' → Prop
  /-- The empty chain. -/
  | refl {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
      SubtractiveReducible C C
  /-- A strong subtractive step, then a chain. -/
  | strong {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : StrongSubtractiveReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E
  /-- A parsimonious step, then a chain. -/
  | parsimonious {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : RelOrderedParsimoniousReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E

open Lax366625.CountingProblems Lax366625.CountingClasses

/-- A counting problem is **hard** for a class when every problem of the class
reduces to it by a subtractive reduction. -/
def SubtractiveHard (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    K.Mem D → SubtractiveReducible D C

/-- A counting problem is **complete** for a class when it belongs to it and is
hard for it, under subtractive reductions. -/
def SubtractiveComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  K.Mem C ∧ SubtractiveHard K C

end Lax859101.SubtractiveReductions
