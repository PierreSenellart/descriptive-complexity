/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.QsatTape

/-!
# The machine of a quantified Boolean formula

The program half of `QSAT ≤ᶠᵒ[≤] DTMAcceptSpace`: the states, symbols and
transitions of the machine built inside a QSAT instance, on the tape laid out
in `DescriptiveComplexity.Problems.Machine.QsatTape`.

## The program

Iterative evaluation of a quantified Boolean formula. The recursion stack is
not a stack: each variable's own cell carries its current value `b` together
with a bit `f` recording that both values have already been tried, which is
all the standard algorithm needs.

```
  Desc      ⊢ → at each cell write (0,0), moving right → ⊣, then evaluate
  Eval f d c  sweep in direction d accumulating f := f ∨ QLit c x b;
              at the marker: ¬f → the matrix is false;
                             f and c has a successor → next clause, turn round;
                             f and c is the last → the matrix is true
  ToEnd b   walk right to ⊣, turn round, and return the value b
  Proc b    at the innermost unfinished variable x:
              the level is decided (∃ and b, or ∀ and ¬b, or f already set)
                                            → move left, keep returning b
              otherwise                     → write (1,1), move right, Desc
            at ⊢: b → accept; ¬b → no transition, the run dies
```

The machine is **deterministic**, which is the whole point: `DTMAcceptSpace`
folds `DescriptiveComplexity.TMData.Deterministic` into its yes-instances, and a
deterministic run is also what makes the converse half of correctness free
(`Relation.ReflTransGen.total_of_right_unique`).

## Malformed instances

`DescriptiveComplexity.QsatHolds` requires `DescriptiveComplexity.QsatWf`, so an
instance whose prefix order is not a strict linear order on the marked
variables must map to a machine that cannot accept. That is arranged by a
**guard on the accepting predicate**
(`DescriptiveComplexity.QsatTM.QAcc`) rather than by the tape order, which
would not catch every violation.

## Semantics first

As in `DescriptiveComplexity.Problems.Machine.Hardness`, everything here is a plain
predicate on tagged tuples: the machine is assembled as a
`DescriptiveComplexity.TMData` and reasoned about directly, and only later
transcribed into defining formulas. A transition table type-checks whatever it
says, so it has to be validated by proofs – which is what the second half of
this file is.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QsatTM

noncomputable section Machine

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The instance, read -/

/-- Being a clause of the matrix. -/
def QCl (c : A) : Prop := RelMap qsIsClause ![c]

/-- The variable `x` occurs positively in the clause `c`. -/
def QPosIn (c x : A) : Prop := RelMap qsPosIn ![c, x]

/-- The variable `x` occurs negatively in the clause `c`. -/
def QNegIn (c x : A) : Prop := RelMap qsNegIn ![c, x]

/-- **The literal test**: the cell of `x`, holding the truth value `b`,
satisfies the clause `c`. This is the first-order test on the source structure
that the evaluation sweep performs. -/
def QLit (c x : A) (b : Bool) : Prop :=
  (QPosIn c x ∧ b = true) ∨ (QNegIn c x ∧ b = false)

/-- `c` is the lowest clause in the ambient order. -/
def QMinCl (c : A) : Prop := QCl c ∧ ∀ e, QCl e → c ≤ e

/-- `c` is the highest clause in the ambient order. -/
def QMaxCl (c : A) : Prop := QCl c ∧ ∀ e, QCl e → e ≤ c

/-- `c'` is the clause immediately above `c`. -/
def QNextCl (c c' : A) : Prop :=
  QCl c ∧ QCl c' ∧ c < c' ∧ ∀ e, QCl e → c < e → c' ≤ e

/-- **The level is already decided**: a returning value `v` settles the
quantifier at `x` on its own – an existential level reached by a winning
branch, a universal one by a losing branch. -/
def QShort (v : Bool) (x : A) : Prop :=
  (IsQAll x ∧ v = false) ∨ (¬IsQAll x ∧ v = true)

/-! ### The elements of the machine -/

/-- The least element of the instance, to which every constant of the machine
is pinned. -/
def qBot : A := (Finite.exists_min (id : A → A)).choose

omit [Language.qsat.Structure A] in
theorem qBot_le (a : A) : qBot (A := A) ≤ a := (Finite.exists_min (id : A → A)).choose_spec a

omit [Language.qsat.Structure A] in
theorem isMinTup_qBot : IsMinTup (fun _ => qBot (A := A)) := ⟨qBot_le, qBot_le⟩

/-- A constant of the machine: a tag on the pair of least elements. -/
def qCst (t : QTag) : QV A := (t, fun _ => qBot)

/-- A tag carrying one element, pinned in the second coordinate. -/
def qOne (t : QTag) (a : A) : QV A := (t, ![a, qBot])

/-! #### Symbols -/

/-- The left-marker symbol. -/
abbrev symStart : QV A := qCst .sStart

/-- The right-marker symbol. -/
abbrev symEnd : QV A := qCst .sEnd

/-- The symbol of the cell of `x`: value `b`, flag `f`. -/
abbrev symV (b f : Bool) (x : A) : QV A := qOne (.sVal b f) x

/-- The marker a sweep in direction `d` ends at. -/
abbrev markerSym (d : Bool) : QV A := if d then symEnd else symStart

/-! #### Positions -/

/-- The left-marker cell. -/
abbrev posStart : QV A := qCst .pStart

/-- The cell of the variable `x`. -/
abbrev posCell (x : A) : QV A := qOne .pCell x

/-- The right-marker cell. -/
abbrev posEnd : QV A := qCst .pEnd

/-! #### States -/

/-- Descending: initialising the cells to the right. -/
abbrev stDesc : QV A := qCst .qDesc

/-- Evaluating the clause `c`, flag `f`, sweeping in direction `d`. -/
abbrev stEval (f d : Bool) (c : A) : QV A := qOne (.qEval f d) c

/-- Carrying the value `b` to the right marker. -/
abbrev stToEnd (b : Bool) : QV A := qCst (.qToEnd b)

/-- Returning the value `b` through the prefix. -/
abbrev stProc (b : Bool) : QV A := qCst (.qProc b)

/-- The accepting state. -/
abbrev stAcc : QV A := qCst .qAcc

/-! ### The transition table -/

/-- The second coordinate of a tuple is the least element: the padding of the
tags that carry a single element. -/
def IsMin1 (p : QV A) : Prop := ∀ a : A, p.2 1 ≤ a

/-- Which tagged tuples are transitions. The payload is pinned exactly as far
as the transition needs it. -/
def QTr (τ : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => IsMinTup τ.2
  | .tDescCell _ _ => IsQVar (τ.2 0) ∧ IsMin1 τ
  | .tDescEndTrue => IsMinTup τ.2 ∧ ∀ e : A, ¬QCl e
  | .tDescEndEval => QMinCl (τ.2 0) ∧ IsMin1 τ
  | .tEval _ _ _ _ => QCl (τ.2 0) ∧ IsQVar (τ.2 1)
  | .tTurnNext _ => QNextCl (τ.2 0) (τ.2 1)
  | .tTurnLast _ => QMaxCl (τ.2 0) ∧ IsMin1 τ
  | .tTurnFalse _ => QCl (τ.2 0) ∧ IsMin1 τ
  | .tToEndCell _ _ _ => IsQVar (τ.2 0) ∧ IsMin1 τ
  | .tToEndStart _ => IsMinTup τ.2
  | .tToEndTurn _ => IsMinTup τ.2
  | .tProcSkip v _ f => IsQVar (τ.2 0) ∧ IsMin1 τ ∧ (QShort v (τ.2 0) ∨ f = true)
  | .tProcSwitch v _ f => IsQVar (τ.2 0) ∧ IsMin1 τ ∧ ¬QShort v (τ.2 0) ∧ f = false
  | .tProcAcc => IsMinTup τ.2
  | _ => False

/-- The state a transition applies in. -/
def QSrc (τ q : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => q = stDesc
  | .tDescCell _ _ => q = stDesc
  | .tDescEndTrue => q = stDesc
  | .tDescEndEval => q = stDesc
  | .tEval _ _ fl d => q = stEval fl d (τ.2 0)
  | .tTurnNext d => q = stEval true d (τ.2 0)
  | .tTurnLast d => q = stEval true d (τ.2 0)
  | .tTurnFalse d => q = stEval false d (τ.2 0)
  | .tToEndCell v _ _ => q = stToEnd v
  | .tToEndStart v => q = stToEnd v
  | .tToEndTurn v => q = stToEnd v
  | .tProcSkip v _ _ => q = stProc v
  | .tProcSwitch v _ _ => q = stProc v
  | .tProcAcc => q = stProc true
  | _ => False

/-- The symbol a transition reads. -/
def QRead (τ a : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => a = symStart
  | .tDescCell b f => a = symV b f (τ.2 0)
  | .tDescEndTrue => a = symEnd
  | .tDescEndEval => a = symEnd
  | .tEval b f _ _ => a = symV b f (τ.2 1)
  | .tTurnNext d => a = markerSym d
  | .tTurnLast d => a = markerSym d
  | .tTurnFalse d => a = markerSym d
  | .tToEndCell _ b f => a = symV b f (τ.2 0)
  | .tToEndStart _ => a = symStart
  | .tToEndTurn _ => a = symEnd
  | .tProcSkip _ b f => a = symV b f (τ.2 0)
  | .tProcSwitch _ b f => a = symV b f (τ.2 0)
  | .tProcAcc => a = symStart
  | _ => False

/-- The state a transition moves to. The only place the instance is consulted
is the evaluation sweep, where the new flag depends on
`DescriptiveComplexity.QsatTM.QLit`. -/
def QDst (τ q : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => q = stDesc
  | .tDescCell _ _ => q = stDesc
  | .tDescEndTrue => q = stProc true
  | .tDescEndEval => q = stEval false false (τ.2 0)
  | .tEval b _ fl d =>
      (q = stEval true d (τ.2 0) ∧ (fl = true ∨ QLit (τ.2 0) (τ.2 1) b)) ∨
        (q = stEval false d (τ.2 0) ∧ fl = false ∧ ¬QLit (τ.2 0) (τ.2 1) b)
  | .tTurnNext d => q = stEval false (!d) (τ.2 1)
  | .tTurnLast _ => q = stToEnd true
  | .tTurnFalse _ => q = stToEnd false
  | .tToEndCell v _ _ => q = stToEnd v
  | .tToEndStart v => q = stToEnd v
  | .tToEndTurn v => q = stProc v
  | .tProcSkip v _ _ => q = stProc v
  | .tProcSwitch _ _ _ => q = stDesc
  | .tProcAcc => q = stAcc
  | _ => False

/-- The symbol a transition writes: the descent resets a cell, the switch sets
the second value with the flag up, and everything else leaves the tape as it
found it. -/
def QWrite (τ a : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => a = symStart
  | .tDescCell _ _ => a = symV false false (τ.2 0)
  | .tDescEndTrue => a = symEnd
  | .tDescEndEval => a = symEnd
  | .tEval b f _ _ => a = symV b f (τ.2 1)
  | .tTurnNext d => a = markerSym d
  | .tTurnLast d => a = markerSym d
  | .tTurnFalse d => a = markerSym d
  | .tToEndCell _ b f => a = symV b f (τ.2 0)
  | .tToEndStart _ => a = symStart
  | .tToEndTurn _ => a = symEnd
  | .tProcSkip _ b f => a = symV b f (τ.2 0)
  | .tProcSwitch _ _ _ => a = symV true true (τ.2 0)
  | .tProcAcc => a = symStart
  | _ => False

/-- Which transitions move the head right: the descent and the carry always
do, a sweep goes in its own direction, a turn reverses, and the return walks
leftwards. -/
def QRight (τ : QV A) : Prop :=
  match τ.1 with
  | .tDescStart => True
  | .tDescCell _ _ => True
  | .tDescEndTrue => False
  | .tDescEndEval => False
  | .tEval _ _ _ d => d = true
  | .tTurnNext d => d = false
  | .tTurnLast d => d = false
  | .tTurnFalse d => d = false
  | .tToEndCell _ _ _ => True
  | .tToEndStart _ => True
  | .tToEndTurn _ => False
  | .tProcSkip _ _ _ => False
  | .tProcSwitch _ _ _ => True
  | .tProcAcc => True
  | _ => False

/-- **Accepting states**, guarded by well-formedness of the instance: a
malformed instance is a no-instance of QSAT, and its machine has no accepting
state at all. -/
def QAcc (q : QV A) : Prop := QsatWf A ∧ q.1 = QTag.qAcc

/-- Start states: just `DescriptiveComplexity.QsatTM.stDesc`. -/
def QStart (q : QV A) : Prop := q.1 = QTag.qDesc ∧ IsMinTup q.2

/-- **The machine of a quantified Boolean formula.** -/
def qsatMachine (A : Type) [Language.qsat.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] : TMData (QV A) where
  Posn := QPosn
  Le := QLe
  Tr := QTr
  Start := QStart
  Acc := QAcc
  Blank := QBlank
  Right := QRight
  Src := QSrc
  Read := QRead
  Dst := QDst
  Write := QWrite
  Inp := QInp


/-! ### The table is a table

Before any run is considered: each transition has exactly one destination and
symbol written, and the state together with the symbol read pins the
transition. A mistake in the table shows up here first, which is why these
come before the correctness proof. -/

section Functional

omit [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- Two elements agree when their tag and both coordinates do. -/
theorem qV_ext {τ τ' : QV A} (ht : τ.1 = τ'.1) (h0 : τ.2 0 = τ'.2 0) (h1 : τ.2 1 = τ'.2 1) :
    τ = τ' := by
  refine Prod.ext ht (funext fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1

omit [Language.qsat.Structure A] in
theorem qOne_eq_qOne_iff {t t' : QTag} {a a' : A} :
    (qOne t a : QV A) = qOne t' a' ↔ t = t' ∧ a = a' := by
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have := congrFun (congrArg Prod.snd h) 0
    simpa [qOne] using this
  · rintro ⟨rfl, rfl⟩; rfl

omit [Language.qsat.Structure A] in
/-- A transition writes exactly one symbol. -/
theorem qWrite_functional {τ a a' : QV A} (h : QWrite τ a) (h' : QWrite τ a') : a = a' := by
  unfold QWrite at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h' <;> exact h.trans h'.symm

/-- A transition moves to exactly one state. The only case with a choice is
the evaluation sweep, whose two branches are separated by the flag and by
`DescriptiveComplexity.QsatTM.QLit`. -/
theorem qDst_functional {τ q q' : QV A} (h : QDst τ q) (h' : QDst τ q') : q = q' := by
  unfold QDst at h h'
  cases hτ : τ.1 <;> rw [hτ] at h h' <;> simp only at h h'
  case tEval b f fl d =>
    rcases h with ⟨hq, hcase⟩ | ⟨hq, hf, hlit⟩ <;> rcases h' with ⟨hq', hcase'⟩ | ⟨hq', hf', hlit'⟩
    · exact hq.trans hq'.symm
    · rcases hcase with hc | hc
      · exact absurd (hc.symm.trans hf') (by decide)
      · exact absurd hc hlit'
    · rcases hcase' with hc | hc
      · exact absurd (hc.symm.trans hf) (by decide)
      · exact absurd hc hlit
    · exact hq.trans hq'.symm
  all_goals exact h.trans h'.symm

omit [Finite A] [Nonempty A] in
/-- **The end of the descent is not ambiguous**: the matrix either has a
clause or has none. -/
theorem qTr_descEnd_excl {τ τ' : QV A} (h : QTr τ) (h' : QTr τ')
    (hτ : τ.1 = QTag.tDescEndTrue) (hτ' : τ'.1 = QTag.tDescEndEval) : False := by
  unfold QTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact h.2 _ h'.1.1

omit [Finite A] [Nonempty A] in
/-- **A turn is not ambiguous**: the clause just evaluated either has a
successor or is the last one. -/
theorem qTr_turn_excl {τ τ' : QV A} {d d' : Bool} (h : QTr τ) (h' : QTr τ')
    (hτ : τ.1 = QTag.tTurnNext d) (hτ' : τ'.1 = QTag.tTurnLast d')
    (hc : τ.2 0 = τ'.2 0) : False := by
  unfold QTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  exact absurd (h'.1.2 _ h.2.1) (not_le.mpr (hc ▸ h.2.2.1))

omit [Finite A] [Nonempty A] in
/-- **The return step is not ambiguous**: a level either is decided – by the
quantifier or by its flag – or is not. -/
theorem qTr_proc_excl {τ τ' : QV A} {v b f v' b' f' : Bool} (h : QTr τ) (h' : QTr τ')
    (hτ : τ.1 = QTag.tProcSkip v b f) (hτ' : τ'.1 = QTag.tProcSwitch v' b' f')
    (hv : v = v') (hx : τ.2 0 = τ'.2 0) (hf : f = f') : False := by
  unfold QTr at h h'
  rw [hτ] at h
  rw [hτ'] at h'
  rcases h.2.2 with hsh | hft
  · exact h'.2.2.1 (hv ▸ hx ▸ hsh)
  · exact absurd (hf ▸ hft : f' = true) (by rw [h'.2.2.2]; decide)

/-! #### The tag of a transition, seen from the state and the symbol -/

/-- The tag of the state a transition applies in, as a function of its own
tag. Junk tags are sent to themselves; they are never transitions. -/
def qStateTag : QTag → QTag
  | .tDescStart => .qDesc
  | .tDescCell _ _ => .qDesc
  | .tDescEndTrue => .qDesc
  | .tDescEndEval => .qDesc
  | .tEval _ _ fl d => .qEval fl d
  | .tTurnNext d => .qEval true d
  | .tTurnLast d => .qEval true d
  | .tTurnFalse d => .qEval false d
  | .tToEndCell v _ _ => .qToEnd v
  | .tToEndStart v => .qToEnd v
  | .tToEndTurn v => .qToEnd v
  | .tProcSkip v _ _ => .qProc v
  | .tProcSwitch v _ _ => .qProc v
  | .tProcAcc => .qProc true
  | t => t

/-- The tag of the symbol a transition reads, as a function of its own tag. -/
def qReadTag : QTag → QTag
  | .tDescStart => .sStart
  | .tDescCell b f => .sVal b f
  | .tDescEndTrue => .sEnd
  | .tDescEndEval => .sEnd
  | .tEval b f _ _ => .sVal b f
  | .tTurnNext d => if d then .sEnd else .sStart
  | .tTurnLast d => if d then .sEnd else .sStart
  | .tTurnFalse d => if d then .sEnd else .sStart
  | .tToEndCell _ b f => .sVal b f
  | .tToEndStart _ => .sStart
  | .tToEndTurn _ => .sEnd
  | .tProcSkip _ b f => .sVal b f
  | .tProcSwitch _ b f => .sVal b f
  | .tProcAcc => .sStart
  | t => t

/-- **The state pins the transition's tag.** -/
theorem qSrc_tag {τ q : QV A} (hτ : QTr τ) (hs : QSrc τ q) : q.1 = qStateTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [QTr, QSrc] at hτ hs <;>
    first
      | exact False.elim hτ
      | (rw [hs]; rfl)

/-- **The symbol read pins the transition's tag.** -/
theorem qRead_tag {τ a : QV A} (hτ : QTr τ) (hr : QRead τ a) : a.1 = qReadTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> dsimp only [QTr, QRead] at hτ hr <;>
    first
      | exact False.elim hτ
      | (rw [hr]; rfl)
      | (rename_i d; cases d <;> (rw [hr]; rfl))

/-- Being the tag of a transition. -/
def qIsTrTag : QTag → Bool
  | .tDescStart | .tDescCell _ _ | .tDescEndTrue | .tDescEndEval
  | .tEval _ _ _ _ | .tTurnNext _ | .tTurnLast _ | .tTurnFalse _
  | .tToEndCell _ _ _ | .tToEndStart _ | .tToEndTurn _
  | .tProcSkip _ _ _ | .tProcSwitch _ _ _ | .tProcAcc => true
  | _ => false

/-- The tag ending the descent with no clause to evaluate. -/
def qIsDescEndTrue : QTag → Bool
  | .tDescEndTrue => true
  | _ => false

/-- The tag ending the descent with a clause to evaluate. -/
def qIsDescEndEval : QTag → Bool
  | .tDescEndEval => true
  | _ => false

/-- The tag turning to the next clause. -/
def qIsTurnNext : QTag → Bool
  | .tTurnNext _ => true
  | _ => false

/-- The tag finishing the last clause. -/
def qIsTurnLast : QTag → Bool
  | .tTurnLast _ => true
  | _ => false

/-- The tag passing a decided level on. -/
def qIsProcSkip : QTag → Bool
  | .tProcSkip _ _ _ => true
  | _ => false

/-- The tag switching a level to its second value. -/
def qIsProcSwitch : QTag → Bool
  | .tProcSwitch _ _ _ => true
  | _ => false

set_option maxRecDepth 20000 in
/-- **The state and the symbol determine the transition's tag, up to the three
known branch points**: the end of the descent, a turn, and the return step. A
finite check over the tags – no case analysis by hand. -/
theorem qTag_cases : ∀ t t' : QTag, qIsTrTag t → qIsTrTag t' →
    qStateTag t = qStateTag t' → qReadTag t = qReadTag t' →
    t = t' ∨ (qIsDescEndTrue t ∧ qIsDescEndEval t') ∨ (qIsDescEndEval t ∧ qIsDescEndTrue t')
      ∨ (qIsTurnNext t ∧ qIsTurnLast t') ∨ (qIsTurnLast t ∧ qIsTurnNext t')
      ∨ (qIsProcSkip t ∧ qIsProcSwitch t') ∨ (qIsProcSwitch t ∧ qIsProcSkip t') := by
  decide

theorem qIsDescEndTrue_iff {t : QTag} : qIsDescEndTrue t ↔ t = .tDescEndTrue := by
  cases t <;> simp [qIsDescEndTrue]

theorem qIsDescEndEval_iff {t : QTag} : qIsDescEndEval t ↔ t = .tDescEndEval := by
  cases t <;> simp [qIsDescEndEval]

theorem qIsTurnNext_iff {t : QTag} : qIsTurnNext t ↔ ∃ d, t = .tTurnNext d := by
  cases t <;> simp [qIsTurnNext]

theorem qIsTurnLast_iff {t : QTag} : qIsTurnLast t ↔ ∃ d, t = .tTurnLast d := by
  cases t <;> simp [qIsTurnLast]

theorem qIsProcSkip_iff {t : QTag} : qIsProcSkip t ↔ ∃ v b f, t = .tProcSkip v b f := by
  cases t <;> simp [qIsProcSkip]

theorem qIsProcSwitch_iff {t : QTag} : qIsProcSwitch t ↔ ∃ v b f, t = .tProcSwitch v b f := by
  cases t <;> simp [qIsProcSwitch]

omit [Finite A] [Nonempty A] in
/-- Only transitions have transition tags. -/
theorem qTr_isTrTag {τ : QV A} (hτ : QTr τ) : qIsTrTag τ.1 := by
  obtain ⟨t, w⟩ := τ
  cases t <;> first | exact False.elim hτ | rfl

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QSrc` at a turn-to-next tag. -/
theorem qSrc_turnNext {τ q : QV A} {d : Bool} (h : τ.1 = .tTurnNext d) (hs : QSrc τ q) :
    q = stEval true d (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QSrc` at a turn-to-last tag. -/
theorem qSrc_turnLast {τ q : QV A} {d : Bool} (h : τ.1 = .tTurnLast d) (hs : QSrc τ q) :
    q = stEval true d (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QSrc` at a skip tag. -/
theorem qSrc_procSkip {τ q : QV A} {v b f : Bool} (h : τ.1 = .tProcSkip v b f)
    (hs : QSrc τ q) : q = stProc v := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QSrc` at a switch tag. -/
theorem qSrc_procSwitch {τ q : QV A} {v b f : Bool} (h : τ.1 = .tProcSwitch v b f)
    (hs : QSrc τ q) : q = stProc v := by
  obtain ⟨t, w⟩ := τ; cases h; exact hs

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QRead` at a skip tag. -/
theorem qRead_procSkip {τ a : QV A} {v b f : Bool} (h : τ.1 = .tProcSkip v b f)
    (hr : QRead τ a) : a = symV b f (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hr

omit [Language.qsat.Structure A] in
/-- Reading off `DescriptiveComplexity.QsatTM.QRead` at a switch tag. -/
theorem qRead_procSwitch {τ a : QV A} {v b f : Bool} (h : τ.1 = .tProcSwitch v b f)
    (hr : QRead τ a) : a = symV b f (τ.2 0) := by
  obtain ⟨t, w⟩ := τ; cases h; exact hr

/-- Equal tags force equal payloads: the state and the symbol pin one
coordinate, the promises in `DescriptiveComplexity.QsatTM.QTr` pin the other. -/
theorem qTr_payload {τ τ' q a : QV A} (hτ : QTr τ) (hτ' : QTr τ')
    (hs : QSrc τ q) (hs' : QSrc τ' q) (hr : QRead τ a) (hr' : QRead τ' a)
    (ht : τ.1 = τ'.1) : τ = τ' := by
  have hmin : ∀ u v : A, (∀ b : A, u ≤ b) → (∀ b : A, v ≤ b) → u = v :=
    fun u v hu hv => le_antisymm (hu v) (hv u)
  obtain ⟨t, w⟩ := τ
  obtain ⟨t', w'⟩ := τ'
  cases ht
  cases t <;> dsimp only [QTr, QSrc, QRead, IsMin1] at hτ hτ' hs hs' hr hr' <;>
    first
      | exact False.elim hτ
      | exact Prod.ext rfl (isMinTup_unique hτ hτ')
      | exact Prod.ext rfl (isMinTup_unique hτ.1 hτ'.1)
      | exact qV_ext rfl (qOne_eq_qOne_iff.mp (hr.symm.trans hr')).2 (hmin _ _ hτ.2 hτ'.2)
      | exact qV_ext rfl (qOne_eq_qOne_iff.mp (hs.symm.trans hs')).2
          (qOne_eq_qOne_iff.mp (hr.symm.trans hr')).2
      | exact qV_ext rfl (qOne_eq_qOne_iff.mp (hs.symm.trans hs')).2 (hmin _ _ hτ.2 hτ'.2)
      | exact qV_ext rfl (le_antisymm (hτ.1.2 _ hτ'.1.1) (hτ'.1.2 _ hτ.1.1))
          (hmin _ _ hτ.2 hτ'.2)
      | exact qV_ext rfl (qOne_eq_qOne_iff.mp (hr.symm.trans hr')).2 (hmin _ _ hτ.2.1 hτ'.2.1)
      | (refine qV_ext rfl (qOne_eq_qOne_iff.mp (hs.symm.trans hs')).2 ?_
         have h0 := (qOne_eq_qOne_iff.mp (hs.symm.trans hs')).2
         exact le_antisymm (hτ.2.2.2 _ hτ'.2.1 (h0 ▸ hτ'.2.2.1))
           (hτ'.2.2.2 _ hτ.2.1 (h0 ▸ hτ.2.2.1)))

/-- **At most one transition applies** in a given state on a given symbol: the
state and the symbol read pin the tag (`DescriptiveComplexity.QsatTM.qTag_cases`),
the tag pins the payload (`DescriptiveComplexity.QsatTM.qTr_payload`), and the three
branch points are exclusive. -/
theorem qTr_unique {τ τ' q a : QV A} (hτ : QTr τ) (hτ' : QTr τ')
    (hs : QSrc τ q) (hs' : QSrc τ' q) (hr : QRead τ a) (hr' : QRead τ' a) : τ = τ' := by
  have hst : qStateTag τ.1 = qStateTag τ'.1 :=
    (qSrc_tag hτ hs).symm.trans (qSrc_tag hτ' hs')
  have hrd : qReadTag τ.1 = qReadTag τ'.1 :=
    (qRead_tag hτ hr).symm.trans (qRead_tag hτ' hr')
  rcases qTag_cases τ.1 τ'.1 (qTr_isTrTag hτ) (qTr_isTrTag hτ') hst hrd with
    heq | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact qTr_payload hτ hτ' hs hs' hr hr' heq
  · exact (qTr_descEnd_excl hτ hτ' (qIsDescEndTrue_iff.mp h1) (qIsDescEndEval_iff.mp h2)).elim
  · exact (qTr_descEnd_excl hτ' hτ (qIsDescEndTrue_iff.mp h2) (qIsDescEndEval_iff.mp h1)).elim
  · obtain ⟨d, hd⟩ := qIsTurnNext_iff.mp h1
    obtain ⟨d', hd'⟩ := qIsTurnLast_iff.mp h2
    exact (qTr_turn_excl hτ hτ' hd hd'
      (qOne_eq_qOne_iff.mp ((qSrc_turnNext hd hs).symm.trans (qSrc_turnLast hd' hs'))).2).elim
  · obtain ⟨d, hd⟩ := qIsTurnLast_iff.mp h1
    obtain ⟨d', hd'⟩ := qIsTurnNext_iff.mp h2
    exact (qTr_turn_excl hτ' hτ hd' hd
      (qOne_eq_qOne_iff.mp ((qSrc_turnNext hd' hs').symm.trans (qSrc_turnLast hd hs))).2).elim
  · obtain ⟨v, b, f, hv⟩ := qIsProcSkip_iff.mp h1
    obtain ⟨v', b', f', hv'⟩ := qIsProcSwitch_iff.mp h2
    have hq : (stProc v : QV A) = stProc v' :=
      (qSrc_procSkip hv hs).symm.trans (qSrc_procSwitch hv' hs')
    have hvv : v = v' := by
      have h2' := congrArg Prod.fst hq
      simp only [qCst, QTag.qProc.injEq] at h2'
      exact h2'
    have hbf := (qOne_eq_qOne_iff (A := A)).mp
      ((qRead_procSkip hv hr).symm.trans (qRead_procSwitch hv' hr'))
    have hff : f = f' := by
      have h1' := hbf.1
      simp only [QTag.sVal.injEq] at h1'
      exact h1'.2
    exact (qTr_proc_excl hτ hτ' hv hv' hvv hbf.2 hff).elim
  · obtain ⟨v, b, f, hv⟩ := qIsProcSwitch_iff.mp h1
    obtain ⟨v', b', f', hv'⟩ := qIsProcSkip_iff.mp h2
    have hq : (stProc v' : QV A) = stProc v :=
      (qSrc_procSkip hv' hs').symm.trans (qSrc_procSwitch hv hs)
    have hvv : v' = v := by
      have h2' := congrArg Prod.fst hq
      simp only [qCst, QTag.qProc.injEq] at h2'
      exact h2'
    have hbf := (qOne_eq_qOne_iff (A := A)).mp
      ((qRead_procSkip hv' hr').symm.trans (qRead_procSwitch hv hr))
    have hff : f' = f := by
      have h1' := hbf.1
      simp only [QTag.sVal.injEq] at h1'
      exact h1'.2
    exact (qTr_proc_excl hτ' hτ hv' hv hvv hbf.2 hff).elim

omit [Language.qsat.Structure A] [Finite A] [Nonempty A] in
/-- There is exactly one start state. -/
theorem qStart_unique {q q' : QV A} (h : QStart q) (h' : QStart q') : q = q' :=
  Prod.ext (h.1.trans h'.1.symm) (isMinTup_unique h.2 h'.2)

/-- **The machine is deterministic.** -/
theorem qsatMachine_deterministic : (qsatMachine A).Deterministic :=
  ⟨fun _ _ h h' => qStart_unique h h',
    fun _ _ _ _ h h' hs hs' hr hr' => qTr_unique h h' hs hs' hr hr',
    fun _ _ _ h h' => qDst_functional h h',
    fun _ _ _ h h' => qWrite_functional h h'⟩

end Functional

end Machine

end QsatTM

end DescriptiveComplexity
