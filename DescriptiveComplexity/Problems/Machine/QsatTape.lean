/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Tape
import DescriptiveComplexity.Problems.Qsat.Defs

/-!
# The tape of the QBF machine

The layout half of `QSAT ≤ᶠᵒ[≤] DTMAcceptSpace`: which tagged tuples are
positions, in what order they sit, and what the tape holds to begin with. The
program that runs on this tape – states, symbols, transitions – is separate.

## The layout

One cell per *quantified variable*, bracketed by two markers:

```
  ⊢   v₁ v₂ … vₙ   ⊣
```

There are no filler cells: `DescriptiveComplexity.TMData.AcceptsSpace` has no step
bound, so unlike the tape of `DescriptiveComplexity.Problems.Machine.Tape` this one
needs to supply space only, and the space it must supply is one bit of value
and one bit of “both values already tried” per variable – the stack of the
recursive evaluation of a quantified Boolean formula, held in the variables'
own cells.

## The order is the quantifier prefix

The head walks the variables in the order the quantifiers bind them, so the
tape order cannot be the ambient one. `DescriptiveComplexity.QsatTM.PLe` puts the
quantified variables first, in prefix order, and everything else after them in
the ambient order; it is a linear order on the universe exactly when the
instance is well formed (`DescriptiveComplexity.QsatWf`), and
`DescriptiveComplexity.QsatTM.QLe` is the lexicographic order built from it – tag
index first, then the two coordinates.

Malformed instances are *not* handled by the order: they are handled by a
guard on the accepting predicate, in the program file. `QsatWf` is first-order,
and `DescriptiveComplexity.QsatHolds` requires it, so an instance violating it must
map to a machine that cannot accept – which a guard achieves and a broken
order would not (an instance whose prefix order relates a non-variable still
has a linear `PLe`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace QsatTM

/-! ### The tags -/

/-- The tags of the QBF machine. Positions come first, so that the tape order
is the order of their indices; symbols, states and transitions follow. -/
inductive QTag : Type
  /-- The left marker cell. -/
  | pStart
  /-- The cell of a quantified variable. -/
  | pCell
  /-- The right marker cell. -/
  | pEnd
  /-- The left-marker symbol `⊢`. -/
  | sStart
  /-- The right-marker symbol `⊣`. -/
  | sEnd
  /-- The blank symbol. -/
  | sBlank
  /-- The symbol of a variable's cell: value `b`, and `f` recording that both
  values have already been tried. -/
  | sVal (b f : Bool)
  /-- Descending into the subtree: initialize the cells to the right. -/
  | qDesc
  /-- Evaluating the matrix: the clause is carried by the state, `f` is the
  accumulated flag and `d` the sweep direction (`true` = rightwards). -/
  | qEval (f d : Bool)
  /-- Carrying the value `b` back to the right marker. -/
  | qToEnd (b : Bool)
  /-- Returning the value `b` through the quantifier prefix. -/
  | qProc (b : Bool)
  /-- The accepting state, a sink. -/
  | qAcc
  /-- Descend: step over the left marker. -/
  | tDescStart
  /-- Descend: initialize a variable's cell, reading `(b, f)`. -/
  | tDescCell (b f : Bool)
  /-- Descend over, and the matrix has no clause: it is true. -/
  | tDescEndTrue
  /-- Descend over: start evaluating the lowest clause. -/
  | tDescEndEval
  /-- Evaluate: read `(b, f)` at a cell, with flag `fl`, sweeping in direction
  `d`. -/
  | tEval (b f fl d : Bool)
  /-- Evaluate: the clause is satisfied and another one follows. -/
  | tTurnNext (d : Bool)
  /-- Evaluate: the clause is satisfied and it was the last one. -/
  | tTurnLast (d : Bool)
  /-- Evaluate: the clause is not satisfied, so the matrix is false. -/
  | tTurnFalse (d : Bool)
  /-- Carry: step over a variable's cell, reading `(b, f)`. -/
  | tToEndCell (v b f : Bool)
  /-- Carry: step over the left marker. -/
  | tToEndStart (v : Bool)
  /-- Carry: the right marker is reached, turn round and return. -/
  | tToEndTurn (v : Bool)
  /-- Return: this level is decided, pass the value on. -/
  | tProcSkip (v b f : Bool)
  /-- Return: this level must try its second value. -/
  | tProcSwitch (v b f : Bool)
  /-- Return: the prefix is exhausted and the value is true. -/
  | tProcAcc
  deriving DecidableEq, Fintype

instance : Nonempty QTag := ⟨QTag.pStart⟩

open QTag in
/-- The index of a tag: the tape order on the position tags, and an arbitrary
injective numbering of the rest. -/
def qTagIdx : QTag → ℕ
  | pStart => 0
  | pCell => 1
  | pEnd => 2
  | sStart => 3
  | sEnd => 4
  | sBlank => 5
  | sVal b f => 6 + (if b then 1 else 0) + (if f then 2 else 0)
  | qDesc => 10
  | qEval f d => 11 + (if f then 1 else 0) + (if d then 2 else 0)
  | qToEnd b => 15 + (if b then 1 else 0)
  | qProc b => 17 + (if b then 1 else 0)
  | qAcc => 19
  | tDescStart => 20
  | tDescCell b f => 21 + (if b then 1 else 0) + (if f then 2 else 0)
  | tDescEndTrue => 25
  | tDescEndEval => 26
  | tEval b f fl d =>
      27 + (if b then 1 else 0) + (if f then 2 else 0) + (if fl then 4 else 0) +
        (if d then 8 else 0)
  | tTurnNext d => 43 + (if d then 1 else 0)
  | tTurnLast d => 45 + (if d then 1 else 0)
  | tTurnFalse d => 47 + (if d then 1 else 0)
  | tToEndCell v b f =>
      49 + (if v then 1 else 0) + (if b then 2 else 0) + (if f then 4 else 0)
  | tToEndStart v => 57 + (if v then 1 else 0)
  | tToEndTurn v => 59 + (if v then 1 else 0)
  | tProcSkip v b f =>
      61 + (if v then 1 else 0) + (if b then 2 else 0) + (if f then 4 else 0)
  | tProcSwitch v b f =>
      69 + (if v then 1 else 0) + (if b then 2 else 0) + (if f then 4 else 0)
  | tProcAcc => 77

theorem qTagIdx_injective : Function.Injective qTagIdx := by decide

/-! ### The prefix order, as an order on the universe

The quantified variables come first, in the order the prefix binds them; every
other element comes after, in the ambient order. -/

section Order

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A]

/-- **The tape order on elements**: quantified variables first in prefix
order, the rest afterwards in the ambient order. -/
def PLe (x y : A) : Prop :=
  (IsQVar x ∧ IsQVar y ∧ (x = y ∨ QPrec x y)) ∨
    (IsQVar x ∧ ¬IsQVar y) ∨
      (¬IsQVar x ∧ ¬IsQVar y ∧ x ≤ y)

variable (A) in
/-- **The tape order is a linear order** on a well-formed instance. -/
theorem isLinOrd_pLe (hwf : QsatWf A) : IsLinOrd (PLe (A := A)) := by
  refine ⟨fun x => ?_, fun x y z hxy hyz => ?_, fun x y hxy hyx => ?_, fun x y => ?_⟩
  · by_cases hx : IsQVar x
    · exact Or.inl ⟨hx, hx, Or.inl rfl⟩
    · exact Or.inr (Or.inr ⟨hx, hx, le_refl x⟩)
  · rcases hxy with ⟨hx, hy, hxy'⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hle⟩
    · rcases hyz with ⟨-, hz, hyz'⟩ | ⟨-, hz⟩ | ⟨hy', -, -⟩
      · refine Or.inl ⟨hx, hz, ?_⟩
        rcases hxy' with rfl | hxy'
        · exact hyz'
        · rcases hyz' with rfl | hyz'
          · exact Or.inr hxy'
          · exact Or.inr (hwf.trans _ _ _ hxy' hyz')
      · exact Or.inr (Or.inl ⟨hx, hz⟩)
      · exact absurd hy hy'
    · rcases hyz with ⟨hy', -, -⟩ | ⟨hy', -⟩ | ⟨-, hz, -⟩
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact Or.inr (Or.inl ⟨hx, hz⟩)
    · rcases hyz with ⟨hy', -, -⟩ | ⟨hy', -⟩ | ⟨-, hz, hle'⟩
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact Or.inr (Or.inr ⟨hx, hz, hle.trans hle'⟩)
  · rcases hxy with ⟨hx, hy, hxy'⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hle⟩
    · rcases hxy' with rfl | hxy'
      · rfl
      · rcases hyx with ⟨-, -, hyx'⟩ | ⟨-, hx'⟩ | ⟨-, hx', -⟩
        · rcases hyx' with rfl | hyx'
          · rfl
          · exact absurd (hwf.trans _ _ _ hxy' hyx') (hwf.irrefl x)
        · exact absurd hx hx'
        · exact absurd hx hx'
    · rcases hyx with ⟨hy', -, -⟩ | ⟨hy', -⟩ | ⟨-, hx', -⟩
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact absurd hx hx'
    · rcases hyx with ⟨hy', -, -⟩ | ⟨hy', -⟩ | ⟨-, -, hle'⟩
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact le_antisymm hle hle'
  · by_cases hx : IsQVar x <;> by_cases hy : IsQVar y
    · rcases eq_or_ne x y with rfl | hne
      · exact Or.inl (Or.inl ⟨hx, hx, Or.inl rfl⟩)
      · rcases hwf.total x y hx hy hne with h | h
        · exact Or.inl (Or.inl ⟨hx, hy, Or.inr h⟩)
        · exact Or.inr (Or.inl ⟨hy, hx, Or.inr h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨hx, hy⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
    · rcases le_total x y with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨hx, hy, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hy, hx, h⟩))

/-! ### The order on the universe -/

/-- The universe of the QBF machine: tagged pairs. -/
abbrev QV (A : Type) := QTag × (Fin 2 → A)

/-- The tape order on tuples: lexicographic in `DescriptiveComplexity.QsatTM.PLe`. -/
def QTupLe (u v : Fin 2 → A) : Prop :=
  (PLe (u 0) (v 0) ∧ u 0 ≠ v 0) ∨ (u 0 = v 0 ∧ PLe (u 1) (v 1))

/-- **The tape order**: tag index first, then the tuple lexicographically. -/
def QLe (p q : QV A) : Prop :=
  qTagIdx p.1 < qTagIdx q.1 ∨ (p.1 = q.1 ∧ QTupLe p.2 q.2)

variable (A) in
/-- **The tape order is linear** on a well-formed instance. -/
theorem isLinOrd_qLe (hwf : QsatWf A) : IsLinOrd (QLe (A := A)) := by
  obtain ⟨hrefl, htrans, hanti, htotal⟩ := isLinOrd_pLe A hwf
  have htup : IsLinOrd (QTupLe (A := A)) := by
    refine ⟨fun u => Or.inr ⟨rfl, hrefl _⟩, fun u v w huv hvw => ?_,
      fun u v huv hvu => ?_, fun u v => ?_⟩
    · rcases huv with ⟨h1, hne⟩ | ⟨h1, h2⟩ <;> rcases hvw with ⟨h1', hne'⟩ | ⟨h1', h2'⟩
      · exact Or.inl ⟨htrans _ _ _ h1 h1', fun he => hne (hanti _ _ h1 (he ▸ h1'))⟩
      · exact Or.inl ⟨h1'.symm ▸ h1, h1' ▸ hne⟩
      · exact Or.inl ⟨h1 ▸ h1', h1 ▸ hne'⟩
      · exact Or.inr ⟨h1.trans h1', htrans _ _ _ h2 h2'⟩
    · rcases huv with ⟨h1, hne⟩ | ⟨h1, h2⟩ <;> rcases hvu with ⟨h1', hne'⟩ | ⟨h1', h2'⟩
      · exact absurd (hanti _ _ h1 h1') hne
      · exact absurd h1'.symm hne
      · exact absurd h1.symm hne'
      · funext i
        fin_cases i
        · exact h1
        · exact hanti _ _ h2 h2'
    · rcases eq_or_ne (u 0) (v 0) with he | hne
      · rcases htotal (u 1) (v 1) with h | h
        · exact Or.inl (Or.inr ⟨he, h⟩)
        · exact Or.inr (Or.inr ⟨he.symm, h⟩)
      · rcases htotal (u 0) (v 0) with h | h
        · exact Or.inl (Or.inl ⟨h, hne⟩)
        · exact Or.inr (Or.inl ⟨h, fun he => hne he.symm⟩)
  refine ⟨fun p => Or.inr ⟨rfl, htup.1 _⟩, fun p q r hpq hqr => ?_,
    fun p q hpq hqp => ?_, fun p q => ?_⟩
  · rcases hpq with h | ⟨h, h2⟩ <;> rcases hqr with h' | ⟨h', h2'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inl (h' ▸ h)
    · exact Or.inl (h ▸ h')
    · exact Or.inr ⟨h.trans h', htup.2.1 _ _ _ h2 h2'⟩
  · rcases hpq with h | ⟨h, h2⟩ <;> rcases hqp with h' | ⟨h', h2'⟩
    · exact absurd (h.trans h') (Nat.lt_irrefl _)
    · exact absurd (h' ▸ h) (Nat.lt_irrefl _)
    · exact absurd (h ▸ h') (Nat.lt_irrefl _)
    · exact Prod.ext h (htup.2.2.1 _ _ h2 h2')
  · rcases lt_trichotomy (qTagIdx p.1) (qTagIdx q.1) with h | h | h
    · exact Or.inl (Or.inl h)
    · have he : p.1 = q.1 := qTagIdx_injective h
      rcases htup.2.2.2 p.2 q.2 with h2 | h2
      · exact Or.inl (Or.inr ⟨he, h2⟩)
      · exact Or.inr (Or.inr ⟨he.symm, h2⟩)
    · exact Or.inr (Or.inl h)

end Order

/-! ### Positions, blank and the initial tape -/

section Layout

variable {A : Type} [Language.qsat.Structure A] [LinearOrder A]

/-- The tagged tuples that are positions: the two markers, pinned to the tuple
of ambient minima, and one cell per quantified variable. -/
def QPosn (p : QV A) : Prop :=
  match p.1 with
  | .pStart => IsMinTup p.2
  | .pCell => IsQVar (p.2 0) ∧ ∀ a : A, p.2 1 ≤ a
  | .pEnd => IsMinTup p.2
  | _ => False

/-- The blank symbol, pinned to the tuple of ambient minima. It is never read:
every cell of the initial tape carries a symbol. -/
def QBlank (p : QV A) : Prop := p.1 = QTag.sBlank ∧ IsMinTup p.2

variable [Finite A] [Nonempty A]

omit [Language.qsat.Structure A] in
theorem exists_qBlank : ∃ p : QV A, QBlank p := by
  obtain ⟨w, hw⟩ := exists_isMinTup (A := A)
  exact ⟨(QTag.sBlank, w), rfl, hw⟩

omit [Language.qsat.Structure A] [Finite A] [Nonempty A] in
theorem qBlank_unique {p q : QV A} (hp : QBlank p) (hq : QBlank q) : p = q :=
  Prod.ext (hp.1.trans hq.1.symm) (isMinTup_unique hp.2 hq.2)

theorem exists_qPosn : ∃ p : QV A, QPosn p := by
  obtain ⟨w, hw⟩ := exists_isMinTup (A := A)
  exact ⟨(QTag.pStart, w), hw⟩

/-- **The initial tape**: the markers hold their own symbols, and a variable's
cell holds the value `false` with the flag down. -/
def QInp (p a : QV A) : Prop :=
  (p.1 = QTag.pStart ∧ a.1 = QTag.sStart ∧ IsMinTup a.2) ∨
    (p.1 = QTag.pCell ∧ a.1 = QTag.sVal false false ∧ a.2 0 = p.2 0 ∧
      ∀ b : A, a.2 1 ≤ b) ∨
      (p.1 = QTag.pEnd ∧ a.1 = QTag.sEnd ∧ IsMinTup a.2)

omit [Language.qsat.Structure A] [Finite A] [Nonempty A] in
/-- **The initial tape is functional**: a cell holds at most one symbol. -/
theorem qInp_functional {p a b : QV A} (ha : QInp p a) (hb : QInp p b) : a = b := by
  have htup : ∀ u v : Fin 2 → A, u 0 = p.2 0 → (∀ c : A, u 1 ≤ c) →
      v 0 = p.2 0 → (∀ c : A, v 1 ≤ c) → u = v := by
    intro u v hu0 hu1 hv0 hv1
    funext i
    fin_cases i
    · exact hu0.trans hv0.symm
    · exact le_antisymm (hu1 _) (hv1 _)
  rcases ha with ⟨hp, hat, haw⟩ | ⟨hp, hat, ha0, ha1⟩ | ⟨hp, hat, haw⟩ <;>
    rcases hb with ⟨hq, hbt, hbw⟩ | ⟨hq, hbt, hb0, hb1⟩ | ⟨hq, hbt, hbw⟩ <;>
      first
        | exact Prod.ext (hat.trans hbt.symm) (isMinTup_unique haw hbw)
        | exact Prod.ext (hat.trans hbt.symm) (htup _ _ ha0 ha1 hb0 hb1)
        | (rw [hp] at hq; exact absurd hq (by decide))

end Layout

end QsatTM

end DescriptiveComplexity
