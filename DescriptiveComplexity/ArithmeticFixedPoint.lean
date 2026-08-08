/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.ArithmeticDefinable
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.FixedPointHorn

/-!
# AC⁰ ⊆ PTIME: the numeric predicates are an induction

**`AC⁰ ⊆ PTIME`** (`DescriptiveComplexity.ac0Definable_mem_PTIME`): first-order
logic with `+` and `×` on the ranks is inside polynomial time, because the two
numeric predicates are themselves defined by one simultaneous induction over the
order, and `DescriptiveComplexity.StepDef` puts an **unrestricted** first-order
sentence on top of the relations it computes.

## Why the fixed-point layer, and not the machine

The tempting route is `FO(DTC)`: `x + y = z` is a walk (step two heads in
lockstep), which is deterministic, so addition is one operator. But
`DescriptiveComplexity.TCSpec` is a *single* operator over first-order kernels,
with no relation variables; multiplication is a walk whose step needs addition,
and the sentence on top needs both, so the route requires nesting that the
specification-as-data logic does not have. `DescriptiveComplexity.StepDef` has
exactly the two features that are wanted instead:

* the step formulas may read the variables being computed, so `plus` and `times`
  are one *simultaneous* induction – `times` reads `plus` positively, and no
  stratification (`DescriptiveComplexity.StepDef.stratify`) is needed;
* the output is an arbitrary first-order sentence over the expanded vocabulary,
  free to negate fixed-point atoms – which is what an AC⁰ sentence needs, its
  numeric atoms sitting anywhere.

Since the numeric predicates are *symbols*, no formula recursion is involved
either: the translation of an AC⁰ sentence is a language map
(`DescriptiveComplexity.arithToBlock`) sending `plus` and `times` to the two
relation variables, and `FirstOrder.Language.LHom.realize_onSentence` does the
rest, once the limit of the induction is proved to *be* the arithmetic.

## The induction

Two variables of arity 3, `plus` and `times`, with the clauses

* `plus x y z` ← `y` is least and `x = z`; or `y' ⋖ y`, `z' ⋖ z`, `plus x y' z'`;
* `times x y z` ← `y` and `z` are least; or `y' ⋖ y`, `times x y' w`, `plus w x z`

read inflationarily. Soundness is an induction on the stages
(`DescriptiveComplexity.inflStage_arith_sound`); completeness needs no stage
count at all, only that the limit is *closed* under the step
(`DescriptiveComplexity.StepDef.isFixedPt_inflStep_inflLimit`), and then an
induction along the order (`DescriptiveComplexity.inflLimit_plus_of_eq`,
`DescriptiveComplexity.inflLimit_times_of_eq`).

## What this does and does not give

It gives the inclusion in PTIME, hence in NP and everything above, and it gives
every consumer that a closure of AC⁰ under first-order reductions would (a
problem reducing to an AC⁰ problem is in PTIME, PTIME being closed under
reductions). It does **not** give the sharper `AC⁰ ⊆ LOGSPACE`, which needs the
arithmetic computed by a deterministic multi-head automaton
(`DescriptiveComplexity.HeadProgram`) rather than by an induction.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

/-! ### The block of the two numeric predicates -/

/-- The relation variables computing the numeric predicates: two of arity 3,
`false` for addition and `true` for multiplication. The index type is `Bool`
rather than `Fin 2` because numerals do not elaborate at a block's `ι`. -/
abbrev arithBlock : SOBlock where
  ι := Bool
  arity := fun _ => 3

/-- The addition variable, as a symbol of the expanded vocabulary. -/
abbrev plusVarSym (L : Language.{0, 0}) :
    ((L.sum Language.order).sum arithBlock.lang).Relations 3 :=
  varOutSym L arithBlock false

/-- The multiplication variable, as a symbol of the expanded vocabulary. -/
abbrev timesVarSym (L : Language.{0, 0}) :
    ((L.sum Language.order).sum arithBlock.lang).Relations 3 :=
  varOutSym L arithBlock true

section Formulas

variable {L : Language.{0, 0}} {α : Type}

/-- An order formula, transported to the vocabulary expanded by the block. -/
noncomputable def arithOrdF (φ : (L.sum Language.order).Formula α) :
    ((L.sum Language.order).sum arithBlock.lang).Formula α :=
  LHom.sumInl.onFormula φ

/-- An atom of one of the two numeric relation variables. -/
noncomputable def arithVarF (i : Bool) (a b c : α) :
    ((L.sum Language.order).sum arithBlock.lang).Formula α :=
  Relations.formula (varOutSym L arithBlock i) ![Term.var a, Term.var b, Term.var c]

/-- **The clause of addition**: either `y` is least and `z` is `x`, or `y` and
`z` both step down and the smaller triple is already there.

Stated at `Fin 3` and only then read at `Fin (arithBlock.arity i)`: numerals do
not elaborate through the `arity` projection of a block. -/
noncomputable def plusStepF (L : Language.{0, 0}) :
    ((L.sum Language.order).sum arithBlock.lang).Formula (Fin 3) :=
  (arithOrdF (minF 1) ⊓ Term.equal (Term.var 0) (Term.var 2)) ⊔
    ((arithOrdF (succF (Sum.inr 0) (Sum.inl 1)) ⊓
        arithOrdF (succF (Sum.inr 1) (Sum.inl 2)) ⊓
        arithVarF false (Sum.inl 0) (Sum.inr 0) (Sum.inr 1)).iExs (Fin 2))

/-- **The clause of multiplication**: either `y` and `z` are least, or `y` steps
down, `x * y'` is already there, and one more `x` is added to it – the addition
variable of the same simultaneous induction. -/
noncomputable def timesStepF (L : Language.{0, 0}) :
    ((L.sum Language.order).sum arithBlock.lang).Formula (Fin 3) :=
  (arithOrdF (minF 1) ⊓ arithOrdF (minF 2)) ⊔
    ((arithOrdF (succF (Sum.inr 0) (Sum.inl 1)) ⊓
        arithVarF true (Sum.inl 0) (Sum.inr 0) (Sum.inr 1) ⊓
        arithVarF false (Sum.inr 1) (Sum.inl 0) (Sum.inl 2)).iExs (Fin 2))

/-- The step formulas of the numeric induction, indexed by the block. -/
noncomputable def arithStep (L : Language.{0, 0}) :
    ∀ i : arithBlock.ι, ((L.sum Language.order).sum arithBlock.lang).Formula
      (Fin (arithBlock.arity i))
  | false => plusStepF L
  | true => timesStepF L

variable {A : Type} [L.Structure A] [LinearOrder A] (ρ : arithBlock.Assignment A)

@[simp]
theorem realize_arithOrdF (φ : (L.sum Language.order).Formula α) (v : α → A) :
    (@Formula.Realize ((L.sum Language.order).sum arithBlock.lang) A
        (arithBlock.structure₁ ρ) _ (arithOrdF φ) v) ↔ φ.Realize v := by
  letI := arithBlock.structure ρ
  rw [arithOrdF, LHom.realize_onFormula]

@[simp]
theorem realize_arithVarF (i : Bool) (a b c : α) (v : α → A) :
    (@Formula.Realize ((L.sum Language.order).sum arithBlock.lang) A
        (arithBlock.structure₁ ρ) _ (arithVarF (L := L) i a b c) v) ↔
      ρ i ![v a, v b, v c] := by
  letI := arithBlock.structure ρ
  rw [arithVarF, Formula.realize_rel]
  exact iff_of_eq (congrArg (ρ i) (funext fun j => by fin_cases j <;> rfl))

end Formulas

/-! ### The definition, and what it is meant to compute -/

section Semantics

variable {L : Language.{0, 0}}
variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The numeric induction, with an arbitrary first-order output**: the two
variables of `DescriptiveComplexity.arithBlock`, the clauses of
`DescriptiveComplexity.arithStep`, and a sentence over the expanded vocabulary.

Reducible, so that the arity of a variable of its block still reduces to `3`
where `rw` works at implicit transparency. -/
@[reducible]
noncomputable def arithStepDef (out : ((L.sum Language.order).sum arithBlock.lang).Sentence) :
    StepDef (L.sum Language.order) where
  B := arithBlock
  step := arithStep L
  out := out

variable (out : ((L.sum Language.order).sum arithBlock.lang).Sentence)

/-- One application of the numeric clauses, unfolded: the step formula realized
at the current assignment. Stated because `DescriptiveComplexity.StepDef.next` is
a `def` whose equation theorems do not rewrite. -/
theorem next_arithStepDef_iff (ρ : arithBlock.Assignment A) (i : arithBlock.ι)
    (v : Fin (arithBlock.arity i) → A) :
    (arithStepDef (L := L) out).next ρ i v ↔
      @Formula.Realize ((L.sum Language.order).sum arithBlock.lang) A
        (arithBlock.structure₁ ρ) _ (arithStep L i) v :=
  Iff.rfl

/-- **What the addition clause derives**: either the base case, or a step down
on both `y` and `z` from a triple already there. -/
theorem next_plus_iff (ρ : arithBlock.Assignment A) (v : Fin 3 → A) :
    (arithStepDef (L := L) out).next ρ false v ↔
      ((∀ a : A, v 1 ≤ a) ∧ v 0 = v 2) ∨
        ∃ y' z' : A, (y' < v 1 ∧ ∀ a : A, ¬(y' < a ∧ a < v 1)) ∧
          (z' < v 2 ∧ ∀ a : A, ¬(z' < a ∧ a < v 2)) ∧ ρ false ![v 0, y', z'] := by
  letI := arithBlock.structure ρ
  rw [next_arithStepDef_iff, arithStep, plusStepF, Formula.realize_sup]
  constructor
  · rintro (hb | hs)
    · rw [Formula.realize_inf, realize_arithOrdF, realize_minF, Formula.realize_equal] at hb
      exact Or.inl ⟨hb.1, by simpa using hb.2⟩
    · rw [Formula.realize_iExs] at hs
      obtain ⟨i, hi⟩ := hs
      rw [Formula.realize_inf, Formula.realize_inf, realize_arithOrdF, realize_arithOrdF,
        realize_succF, realize_succF, realize_arithVarF] at hi
      exact Or.inr ⟨i 0, i 1, by simpa using hi.1.1, by simpa using hi.1.2, by simpa using hi.2⟩
  · rintro (⟨hmin, heq⟩ | ⟨y', z', hy, hz, hrec⟩)
    · refine Or.inl ?_
      rw [Formula.realize_inf, realize_arithOrdF, realize_minF, Formula.realize_equal]
      exact ⟨hmin, by simpa using heq⟩
    · refine Or.inr ?_
      rw [Formula.realize_iExs]
      refine ⟨![y', z'], ?_⟩
      rw [Formula.realize_inf, Formula.realize_inf, realize_arithOrdF, realize_arithOrdF,
        realize_succF, realize_succF, realize_arithVarF]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using hy
      · simpa using hz
      · simpa using hrec

/-- **What the multiplication clause derives**: either the base case, or one copy
of `x` peeled off `y` and added back with the addition variable. -/
theorem next_times_iff (ρ : arithBlock.Assignment A) (v : Fin 3 → A) :
    (arithStepDef (L := L) out).next ρ true v ↔
      ((∀ a : A, v 1 ≤ a) ∧ ∀ a : A, v 2 ≤ a) ∨
        ∃ y' w : A, (y' < v 1 ∧ ∀ a : A, ¬(y' < a ∧ a < v 1)) ∧
          ρ true ![v 0, y', w] ∧ ρ false ![w, v 0, v 2] := by
  letI := arithBlock.structure ρ
  rw [next_arithStepDef_iff, arithStep, timesStepF, Formula.realize_sup]
  constructor
  · rintro (hb | hs)
    · rw [Formula.realize_inf, realize_arithOrdF, realize_arithOrdF, realize_minF,
        realize_minF] at hb
      exact Or.inl hb
    · rw [Formula.realize_iExs] at hs
      obtain ⟨i, hi⟩ := hs
      rw [Formula.realize_inf, Formula.realize_inf, realize_arithOrdF, realize_succF,
        realize_arithVarF, realize_arithVarF] at hi
      exact Or.inr ⟨i 0, i 1, by simpa using hi.1.1, by simpa using hi.1.2, by simpa using hi.2⟩
  · rintro (⟨h1, h2⟩ | ⟨y', w, hy, ht, hp⟩)
    · refine Or.inl ?_
      rw [Formula.realize_inf, realize_arithOrdF, realize_arithOrdF, realize_minF, realize_minF]
      exact ⟨h1, h2⟩
    · refine Or.inr ?_
      rw [Formula.realize_iExs]
      refine ⟨![y', w], ?_⟩
      rw [Formula.realize_inf, Formula.realize_inf, realize_arithOrdF, realize_succF,
        realize_arithVarF, realize_arithVarF]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using hy
      · simpa using ht
      · simpa using hp

variable [Finite A]

/-! #### Soundness: every stage holds only true facts -/

/-- **Every stage of the numeric induction is sound**: the addition variable
holds only triples whose ranks add up, and the multiplication variable only
triples whose ranks multiply. -/
theorem inflStage_arith_sound (n : ℕ) :
    (∀ v : Fin 3 → A, (arithStepDef (L := L) out).inflStage A n false v →
        orank (v 0) + orank (v 1) = orank (v 2)) ∧
      (∀ v : Fin 3 → A, (arithStepDef (L := L) out).inflStage A n true v →
        orank (v 0) * orank (v 1) = orank (v 2)) := by
  induction n with
  | zero => exact ⟨fun v hv => hv.elim, fun v hv => hv.elim⟩
  | succ n ih =>
    obtain ⟨ihp, iht⟩ := ih
    rw [StepDef.inflStage_succ]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rcases hv with hold | hnew
      · exact ihp v hold
      · rcases (next_plus_iff out _ v).mp hnew with ⟨hmin, heq⟩ | ⟨y', z', hy, hz, hrec⟩
        · rw [orank_eq_zero hmin, heq]
          omega
        · have hih := ihp _ hrec
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons] at hih
          rw [orank_eq_succ_of_pred hy.1 hy.2, orank_eq_succ_of_pred hz.1 hz.2]
          omega
    · rcases hv with hold | hnew
      · exact iht v hold
      · rcases (next_times_iff out _ v).mp hnew with ⟨h1, h2⟩ | ⟨y', w, hy, ht, hp⟩
        · rw [orank_eq_zero h1, orank_eq_zero h2]
          omega
        · have hiht := iht _ ht
          have hihp := ihp _ hp
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons] at hiht hihp
          rw [orank_eq_succ_of_pred hy.1 hy.2, Nat.mul_succ, hiht, hihp]

/-! #### Completeness: the limit is closed under the clauses -/

/-- The limit of the numeric induction is closed under the step formulas: what
one clause derives from it is already in it. -/
theorem next_inflLimit_le {i : arithBlock.ι} {v : Fin (arithBlock.arity i) → A}
    (h : (arithStepDef (L := L) out).next ((arithStepDef (L := L) out).inflLimit A) i v) :
    (arithStepDef (L := L) out).inflLimit A i v := by
  have hfix := (arithStepDef (L := L) out).isFixedPt_inflStep_inflLimit A
  have hv := congrFun (congrFun hfix i) v
  rw [← hv]
  exact Or.inr h

/-- **The addition variable holds every true triple**, by induction along the
order: the clause is applied to the limit, which is closed under it. -/
theorem inflLimit_plus_of_eq (x y z : A) (h : orank x + orank y = orank z) :
    (arithStepDef (L := L) out).inflLimit A false ![x, y, z] := by
  induction hn : orank y generalizing y z with
  | zero =>
    refine next_inflLimit_le out ((next_plus_iff out _ _).mpr (Or.inl ⟨fun a => ?_, ?_⟩))
    · exact isMin_of_orank_eq_zero (by simpa using hn) a
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact orank_inj (by omega)
  | succ k ih =>
    obtain ⟨y', hy'rank, hy'lt, hy'no⟩ := exists_pred_of_orank_succ hn
    obtain ⟨z', hz'rank, hz'lt, hz'no⟩ :=
      exists_pred_of_orank_succ (z := z) (k := orank x + k) (by omega)
    have hrec : (arithStepDef (L := L) out).inflLimit A false ![x, y', z'] :=
      ih y' z' (by omega) hy'rank
    refine next_inflLimit_le out ((next_plus_iff out _ _).mpr (Or.inr ⟨y', z', ?_, ?_, ?_⟩))
    · constructor
      · simpa using hy'lt
      · simpa using hy'no
    · constructor
      · simpa using hz'lt
      · simpa using hz'no
    · simpa using hrec

/-- **The multiplication variable holds every true triple**: the same argument,
one copy of `x` at a time, using the addition variable for the accumulation. -/
theorem inflLimit_times_of_eq (x y z : A) (h : orank x * orank y = orank z) :
    (arithStepDef (L := L) out).inflLimit A true ![x, y, z] := by
  induction hn : orank y generalizing y z with
  | zero =>
    refine next_inflLimit_le out ((next_times_iff out _ _).mpr (Or.inl ⟨fun a => ?_, fun a => ?_⟩))
    · exact isMin_of_orank_eq_zero (by simpa using hn) a
    · refine isMin_of_orank_eq_zero ?_ a
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [← h, hn, Nat.mul_zero]
  | succ k ih =>
    obtain ⟨y', hy'rank, hy'lt, hy'no⟩ := exists_pred_of_orank_succ hn
    have hzr : orank z = orank x * k + orank x := by
      rw [← h, hn, Nat.mul_succ]
    have hwlt : orank x * k < Nat.card A := by
      have := orank_lt_card z
      omega
    obtain ⟨w, hw⟩ := exists_orank_eq (A := A) hwlt
    have hrect : (arithStepDef (L := L) out).inflLimit A true ![x, y', w] := by
      refine ih y' w ?_ hy'rank
      rw [hy'rank, hw]
    have hrecp : (arithStepDef (L := L) out).inflLimit A false ![w, x, z] := by
      refine inflLimit_plus_of_eq out w x z ?_
      rw [hw, hzr]
    refine next_inflLimit_le out ((next_times_iff out _ _).mpr (Or.inr ⟨y', w, ?_, ?_, ?_⟩))
    · constructor
      · simpa using hy'lt
      · simpa using hy'no
    · simpa using hrect
    · simpa using hrecp

/-- **The limit of the numeric induction is the arithmetic of the order**: the
two variables hold exactly the true triples. -/
theorem inflLimit_arith_iff (i : arithBlock.ι) (v : Fin (arithBlock.arity i) → A) :
    (arithStepDef (L := L) out).inflLimit A i v ↔
      (if i then orank (v 0) * orank (v 1) else orank (v 0) + orank (v 1)) = orank (v 2) := by
  have hv : v = ![v 0, v 1, v 2] := by
    funext j
    fin_cases j <;> rfl
  cases i with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    refine ⟨fun ⟨n, hn⟩ => (inflStage_arith_sound out n).1 v hn, fun h => ?_⟩
    rw [hv]
    exact inflLimit_plus_of_eq out (v 0) (v 1) (v 2) (by simpa using h)
  | true =>
    simp only [if_true]
    refine ⟨fun ⟨n, hn⟩ => (inflStage_arith_sound out n).2 v hn, fun h => ?_⟩
    rw [hv]
    exact inflLimit_times_of_eq out (v 0) (v 1) (v 2) (by simpa using h)

end Semantics

/-! ### Reading an AC⁰ sentence at the limit -/

section Transport

variable (L : Language.{0, 0}) [L.IsRelational]

/-- **The translation of an AC⁰ sentence**: the numeric symbols go to the two
relation variables of the induction, the order symbol and the input symbols to
themselves. Being a language map, it needs no recursion over formulas. -/
def arithToBlock : L.sum Language.arith →ᴸ (L.sum Language.order).sum arithBlock.lang where
  onRelation := fun {_} R =>
    match R with
    | Sum.inl r => Sum.inl (Sum.inl r)
    | Sum.inr .le => Sum.inl (Sum.inr .le)
    | Sum.inr .plus => plusVarSym L
    | Sum.inr .times => timesVarSym L

end Transport


/-! ### The inclusion -/

section Inclusion

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

/-- **AC⁰ ⊆ FO(IFP)**: the numeric predicates are the limit of the simultaneous
induction of `DescriptiveComplexity.arithStep`, and an AC⁰ sentence is its
output, translated by `DescriptiveComplexity.arithToBlock`. -/
theorem AC0Definable.ifpDefinable (h : AC0Definable P) : IFPDefinable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨arithStepDef ((arithToBlock L).onSentence φ), ?_⟩
  intro A _ _ _ _
  letI := arithBlock.structure
    ((arithStepDef (L := L) ((arithToBlock L).onSentence φ)).inflLimit A)
  -- the translation is an expansion **at the limit**: this is the whole content of
  -- `DescriptiveComplexity.inflLimit_arith_iff`, read as an agreement of two structures
  haveI hexp : (arithToBlock L).IsExpansionOn A := by
    refine ⟨fun {_} f _ => isEmptyElim f, fun {_} R x => ?_⟩
    cases R with
    | inl r => rfl
    | inr r =>
      cases r with
      | le => rfl
      | plus =>
        rw [eq_iff_iff]
        change (arithStepDef (L := L) ((arithToBlock L).onSentence φ)).inflLimit A false x ↔ _
        rw [inflLimit_arith_iff]
        simp
      | times =>
        rw [eq_iff_iff]
        change (arithStepDef (L := L) ((arithToBlock L).onSentence φ)).inflLimit A true x ↔ _
        rw [inflLimit_arith_iff]
        simp
  rw [hφ A, StepDef.IFPHolds]
  exact (LHom.realize_onSentence A (arithToBlock L) φ).symm

/-- **AC⁰ ⊆ FO(LFP)**, through the equivalence of the inflationary and the least
fixed point. -/
theorem AC0Definable.lfpDefinable (h : AC0Definable P) : LFPDefinable P :=
  h.ifpDefinable.lfpDefinable

/-- **AC⁰ ⊆ PTIME.** With `DescriptiveComplexity.FODefinable.ac0Definable` and
`DescriptiveComplexity.exists_ac0Definable_not_foDefinable` this places the
arithmetic logic strictly above FO(≤) and inside polynomial time; the sharper
`AC⁰ ⊆ LOGSPACE` needs the multi-head automaton instead. -/
theorem ac0Definable_mem_PTIME (h : AC0Definable P) : P ∈ PTIME :=
  (lfpDefinable_iff_mem_PTIME P).mp h.lfpDefinable

end Inclusion

end DescriptiveComplexity
