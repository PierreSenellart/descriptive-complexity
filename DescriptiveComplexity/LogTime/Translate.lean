/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Small
import DescriptiveComplexity.LogTime.BitSum.Times
import DescriptiveComplexity.LogTime.Compile

/-!
# `FO(≤, +, ×)` into the bit logic: the machine model is AC⁰

The machine model of `DescriptiveComplexity.LogTime` is the logic `FO(≤, BIT)`
and sits **inside** `FO(≤, +, ×)`
(`DescriptiveComplexity.LTDecidable.ac0Definable`, through
`DescriptiveComplexity.powArithDef`). This file is the other direction,
`FO(≤, +, ×) ⊆ FO(≤, +, BIT)`, and with it the equality:

> Every `DescriptiveComplexity.ArithDef` relation is
> `DescriptiveComplexity.BitDef` (`DescriptiveComplexity.ArithDef.bitDef`),
> every AC⁰-definable problem is decided by a logarithmic-time machine with
> constantly many alternations
> (`DescriptiveComplexity.AC0Definable.ltDecidable`), and the two notions
> coincide (`DescriptiveComplexity.ac0Definable_iff_ltDecidable`).

The one atom the translation turns on – multiplication of ranks in the bit
logic, `DescriptiveComplexity.TimesBitDef` – is the whole of
[Immerman 1999][immerman1999descriptive] Thm 1.17(1): the Bit Sum Lemma
(`DescriptiveComplexity.BitSum.PopAll`, `LogTime/BitSum/Level1.lean`) and the
column-wise multiplication built on it
(`DescriptiveComplexity.BitSum.bitDef_times`, `LogTime/BitSum/Times.lean`).
It is proved here as `DescriptiveComplexity.timesBitDef`, so nothing below
carries a hypothesis: with `DescriptiveComplexity.ltDecidable_iff_bitDefinable`
on the machine side, **the machine model is exactly AC⁰**.

## How the induction goes

By recursion on `FirstOrder.Language.BoundedFormula`, with the free variables of
a formula with `n` bound ones carried as `α ⊕ Fin n` – the layout the `BitDef`
quantifiers already use. Three points, none of them deep, and all of them
already paid for elsewhere in the library:

* **Terms are variables.** Both vocabularies are relational, so
  `DescriptiveComplexity.relVar` reads a term as the variable it is; this is why
  that definition sits in `DescriptiveComplexity.ArithmeticDefinable`, below both
  this file and the head-program evaluator that also needs it.
* **The atom splits four ways**, on the relation symbol: an input relation, `≤`,
  `plus` and `times`, each bit-definable. It is the same four-way split as
  `DescriptiveComplexity.HeadEvalArith`, at the level of the logic instead of
  the machine.
* **The quantifier is `peelVar`**, the relabelling that moves the innermost bound
  variable out of the block and into the `Fin 1` a `BitDef` quantifier binds,
  with `DescriptiveComplexity.elim_comp_peelVar` saying that this is `Fin.snoc`
  on valuations. `DescriptiveComplexity.arithDef_prefixHolds` does the same thing
  for the other logic.

## What this is not

It is not a normal-form theorem: the bit logic is prenex by construction and the
`BitDef` API merges prefixes semantically, so no `toPrenex` is involved.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational] {α : Type}

/-! ### The last atom -/

/-- **Multiplication of ranks, in the bit logic**: the one atom of `FO(≤, +, ×)`
that `DescriptiveComplexity.BitDef` does not have as a primitive, and hence the
whole content of [Immerman 1999][immerman1999descriptive] Thm 1.17(1) – the Bit
Sum Lemma and the column-wise multiplication over it.

It is a named statement, uniformly in the variable layout, so that what it buys
is visible in a type: the same discipline `DescriptiveComplexity.PowArithDef`
follows, and the reason the two halves of Thm 1.17 can be compared at a
glance. -/
def TimesBitDef (L : Language.{0, 0}) : Prop :=
  ∀ {α : Type} (x y z : α),
    BitDef (L := L) (α := α) fun _ _ _ _ _ v => orank (v x) * orank (v y) = orank (v z)

omit [L.IsRelational] in
/-- **The last atom, proved**: the certificate of `LogTime/BitSum/Times.lean` –
column counts by the Bit Sum Lemma, one carry chain per block, an even and an
odd packing and a tail – in the shape the translation consumes. -/
theorem timesBitDef : TimesBitDef L := fun x y z => BitSum.bitDef_times x y z

/-! ### The translation -/

/-- Splitting a valuation of `α ⊕ Fin n` into its two halves and putting it back
is the identity – the one bookkeeping step the atom cases need. -/
theorem elim_proj {A : Type} {n : ℕ} (u : α ⊕ Fin n → A) :
    Sum.elim (fun a => u (Sum.inl a)) (fun i => u (Sum.inr i)) = u := by
  funext z
  rcases z with a | i <;> rfl

/-- **Every formula of `FO(≤, +, ×)` is bit-definable**: the induction over
`FirstOrder.Language.BoundedFormula`, with the bound variables carried as the
right-hand summand of the variable type. -/
theorem bitDef_realize {α : Type} :
    ∀ {n : ℕ} (φ : (L.sum Language.arith).BoundedFormula α n),
      BitDef (L := L) (α := α ⊕ Fin n)
        fun _ _ _ _ _ u => φ.Realize (fun a => u (Sum.inl a)) fun i => u (Sum.inr i) := by
  intro n φ
  induction φ with
  | falsum => exact BitDef.bot
  | equal t₁ t₂ =>
    refine (bitDef_eq (relVar t₁) (relVar t₂)).congr fun A _ _ _ _ u => ?_
    simp only [BoundedFormula.Realize, realize_relVar, elim_proj]
  | rel R ts =>
    rcases R with r | ar
    · refine (bitDef_rel r fun i => relVar (ts i)).congr fun A _ _ _ _ u => ?_
      simp only [BoundedFormula.Realize, realize_relVar, elim_proj]
      exact Iff.rfl
    · cases ar with
      | le =>
        refine (bitDef_le (relVar (ts 0)) (relVar (ts 1))).congr fun A _ _ _ _ u => ?_
        simp only [BoundedFormula.Realize, realize_relVar, elim_proj]
        exact Iff.rfl
      | plus =>
        refine (bitDef_plus (relVar (ts 0)) (relVar (ts 1)) (relVar (ts 2))).congr
          fun A _ _ _ _ u => ?_
        simp only [BoundedFormula.Realize, realize_relVar, elim_proj]
        exact Iff.rfl
      | times =>
        refine (timesBitDef (relVar (ts 0)) (relVar (ts 1)) (relVar (ts 2))).congr
          fun A _ _ _ _ u => ?_
        simp only [BoundedFormula.Realize, realize_relVar, elim_proj]
        exact Iff.rfl
  | imp φ₁ φ₂ ih₁ ih₂ =>
    refine (ih₁.imp ih₂).congr fun A _ _ _ _ u => ?_
    rw [BoundedFormula.realize_imp]
  | all φ ih =>
    refine ((ih.relabel (peelVar _)).all).congr fun A _ _ _ _ u => ?_
    rw [BoundedFormula.realize_all]
    exact forall_congr' fun a => Iff.of_eq (_root_.congrArg
      (fun w => φ.Realize (fun x => w (Sum.inl x)) fun i => w (Sum.inr i))
      (elim_comp_peelVar u a))

/-- **The two definability notions agree on relations**: a formula of the
arithmetic expansion becomes a sentence of the bit logic with the same free
variables. -/
theorem ArithDef.bitDef {R : ArithRel L α} (h : ArithDef R) : BitDef R := by
  obtain ⟨φ, hφ⟩ := h
  refine ((bitDef_realize φ).relabel (Sum.elim id Fin.elim0)).congr
    fun A _ _ _ _ v => ?_
  refine Iff.trans ?_ (hφ A v).symm
  exact Iff.of_eq (_root_.congrArg (fun xs => BoundedFormula.Realize φ v xs)
    (Subsingleton.elim _ _))

/-! ### What it buys -/

/-- **AC⁰ definability is bit-definability.** -/
theorem AC0Definable.bitDefinable {P : DecisionProblem L} (h : AC0Definable P) :
    BitDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine BitDef.bitDefinable (R := fun A _ _ _ _ v => Formula.Realize φ v)
    (ArithDef.bitDef ⟨φ, fun A _ _ _ _ v => Iff.rfl⟩) fun A _ _ _ _ => ?_
  rw [hφ A]
  exact Iff.of_eq (_root_.congrArg (fun v => Formula.Realize φ v) (Subsingleton.elim _ _))

/-- **An AC⁰ definition is a logarithmic-time machine with constantly many
alternations**: the direction of Immerman's identification that the Bit Sum
Lemma is the whole of. -/
theorem AC0Definable.ltDecidable {P : DecisionProblem L} (h : AC0Definable P) :
    LTDecidable P :=
  h.bitDefinable.ltDecidable

/-- **AC⁰ is constant-alternation logarithmic time** – the statement the whole
`DescriptiveComplexity.LogTime` development aims at, with `⊇` through
`DescriptiveComplexity.powArithDef` and `⊆` through
`DescriptiveComplexity.timesBitDef`: both halves of [Immerman
1999][immerman1999descriptive] Thm 1.17, with no hypothesis left. -/
theorem ac0Definable_iff_ltDecidable {P : DecisionProblem L} :
    AC0Definable P ↔ LTDecidable P :=
  ⟨fun h => h.ltDecidable, fun h => h.ac0Definable⟩

end DescriptiveComplexity
