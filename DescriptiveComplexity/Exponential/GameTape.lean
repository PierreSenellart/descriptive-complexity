/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Padding
import DescriptiveComplexity.Numbers.BinRel
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.SecondOrder

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

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### The tags of the tape -/

/-- **The tags of the tape**: two left sentinels, one family of cells per
region and relation variable, a right sentinel, the symbols carrying a bit and
the address of their cell, and the sentinels' own symbol. -/
inductive TapeTag (B : SOBlock) : Type
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

variable {B : SOBlock}

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

theorem fam_le_four {t : TapeTag B} (h : IsPos t) : fam t ≤ 4 := by
  cases t with
  | left b => cases b <;> simp [fam]
  | cell r i => cases r <;> simp [fam]
  | right => simp [fam]
  | val b r i => exact h.elim
  | mark b => exact h.elim

theorem eq_left_false_of_fam_zero {t : TapeTag B} (h : fam t = 0) : t = .left false := by
  cases t with
  | left b => cases b <;> simp_all [fam]
  | cell r i => cases r <;> simp [fam] at h
  | right => simp [fam] at h
  | val b r i => simp [fam] at h
  | mark b => simp [fam] at h

theorem eq_left_true_of_fam_one {t : TapeTag B} (h : fam t = 1) : t = .left true := by
  cases t with
  | left b => cases b <;> simp_all [fam]
  | cell r i => cases r <;> simp [fam] at h
  | right => simp [fam] at h
  | val b r i => simp [fam] at h
  | mark b => simp [fam] at h

theorem eq_right_of_fam_four {t : TapeTag B} (h : fam t = 4) : t = .right := by
  cases t with
  | left b => cases b <;> simp [fam] at h
  | cell r i => cases r <;> simp [fam] at h
  | right => rfl
  | val b r i => simp [fam] at h
  | mark b => simp [fam] at h

end TapeTag

/-! ### The tags of the machine, and their order -/

/-- **The tags of the machine**: the tape's, and the control's. The control is
a parameter, so this file fixes the tape without committing to the phases. -/
abbrev MachTag (B : SOBlock) (C : Type) : Type := TapeTag B ⊕ C

namespace MachTag

variable {B : SOBlock} {C : Type}

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

/-- A position's tag is a tape tag. -/
theorem exists_tapeTag_of_isPos {t : MachTag B C} (h : IsPos t) :
    ∃ s : TapeTag B, t = Sum.inl s ∧ TapeTag.IsPos s := by
  cases t with
  | inl s => exact ⟨s, rfl, h⟩
  | inr c => exact h.elim

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

variable {B : SOBlock} {C : Type} [Finite C]

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

/-- A lower tag is in a family at most as high. -/
theorem machTag_fam_le_of_le {t t' : MachTag B C}
    (h : letI := machTagOrder (B := B) (C := C); t ≤ t') : MachTag.fam t ≤ MachTag.fam t' := by
  rcases Prod.Lex.toLex_le_toLex.mp h with hlt | ⟨heq, -⟩
  · omega
  · omega

/-- A tag of a lower family is lower. -/
theorem machTag_lt_of_fam_lt {t t' : MachTag B C} (h : MachTag.fam t < MachTag.fam t') :
    letI := machTagOrder (B := B) (C := C)
    t < t' :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end Order

/-! ### The points of the emitted universe -/

section Points

variable {B : SOBlock} {C : Type} {dim : ℕ} {A : Type} [LinearOrder A]

/-- A tagged tuple of the emitted universe, before the domain is imposed. -/
abbrev Pt (B : SOBlock) (C : Type) (dim : ℕ) (A : Type) : Type := MachTag B C × (Fin dim → A)

/-- **The domain of the reduction**: every coordinate a tag does not use is a
minimum, so that a cell of the relation variable `i` corresponds to exactly one
atom of `i`. -/
def machDom (carity : C → ℕ) (p : Pt B C dim A) : Prop :=
  Canon (MachTag.arity carity p.1) p.2

/-- Being a position of the tape. -/
def machPosn (p : Pt B C dim A) : Prop := MachTag.IsPos p.1

variable (a₀ : A)

/-- The point of the cell of region `r` holding the atom `i ā`. -/
def cellPt (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) : Pt B C dim A :=
  (Sum.inl (.cell r i), pad a₀ ā)

/-- **The symbol of that cell**: the bit `b`, together with the address of the
cell it sits in. -/
def valPt (b r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) : Pt B C dim A :=
  (Sum.inl (.val b r i), pad a₀ ā)

/-- One of the two left sentinels. -/
def leftPt (b : Bool) : Pt B C dim A := (Sum.inl (.left b), fun _ => a₀)

/-- The right sentinel. -/
def rightPt : Pt B C dim A := (Sum.inl .right, fun _ => a₀)

/-- The symbol on the sentinels: `markPt a₀ false` on the left pair,
`markPt a₀ true` on the right one. The blank is `markPt a₀ false`. -/
def markPt (b : Bool) : Pt B C dim A := (Sum.inl (.mark b), fun _ => a₀)

omit [LinearOrder A] in
theorem machPosn_cellPt (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) :
    machPosn (cellPt (C := C) (dim := dim) a₀ r i ā) := trivial

omit [LinearOrder A] in
theorem machPosn_leftPt (b : Bool) : machPosn (leftPt (B := B) (C := C) (dim := dim) a₀ b) :=
  trivial

omit [LinearOrder A] in
theorem machPosn_rightPt : machPosn (rightPt (B := B) (C := C) (dim := dim) a₀) := trivial

omit [LinearOrder A] in
/-- The two ends of the tape are different points. -/
theorem leftPt_ne_rightPt (b : Bool) :
    (leftPt (B := B) (C := C) (dim := dim) a₀ b) ≠ rightPt a₀ := by
  intro h
  simpa [leftPt, rightPt] using congrArg Prod.fst h

omit [LinearOrder A] in
/-- A sentinel is not a cell, so a walk reading a mark is not reading an
atom. -/
theorem leftPt_ne_cellPt (b r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) :
    (leftPt (C := C) (dim := dim) a₀ b) ≠ cellPt a₀ r i ā := by
  intro h
  simpa [leftPt, cellPt] using congrArg Prod.fst h

omit [LinearOrder A] in
theorem rightPt_ne_cellPt (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) :
    (rightPt (C := C) (dim := dim) a₀) ≠ cellPt a₀ r i ā := by
  intro h
  simpa [rightPt, cellPt] using congrArg Prod.fst h

omit [LinearOrder A] in
/-- **A symbol determines its bit**, at a fixed cell. -/
theorem valPt_inj_bit {b b' r : Bool} {i : B.ι} {ā : Fin (B.arity i) → A}
    (h : valPt (C := C) (dim := dim) a₀ b r i ā = valPt a₀ b' r i ā) : b = b' := by
  have h1 := congrArg Prod.fst h
  simp only [valPt, Sum.inl.injEq] at h1
  injection h1

omit [LinearOrder A] in
/-- The two marks are different symbols, which is how a walk tells the ends of
the tape apart. -/
theorem markPt_ne_markPt {b b' : Bool} (h : b ≠ b') :
    markPt (B := B) (C := C) (dim := dim) a₀ b ≠ markPt a₀ b' := by
  intro hc
  exact h (by simpa [markPt] using congrArg Prod.fst hc)

omit [LinearOrder A] in
/-- A cell's symbol is not a mark. -/
theorem valPt_ne_markPt {b r : Bool} {i : B.ι} {ā : Fin (B.arity i) → A} {b' : Bool} :
    valPt (C := C) (dim := dim) a₀ b r i ā ≠ markPt a₀ b' := by
  intro hc
  simpa [valPt, markPt] using congrArg Prod.fst hc

omit [LinearOrder A] in
/-- **A symbol determines its bit, its region and its relation variable.** -/
theorem valPt_inj_tag {b b₂ r r₂ : Bool} {i i₂ : B.ι} {ā : Fin (B.arity i) → A}
    {ā₂ : Fin (B.arity i₂) → A}
    (h : valPt (C := C) (dim := dim) a₀ b r i ā = valPt a₀ b₂ r₂ i₂ ā₂) :
    b = b₂ ∧ r = r₂ ∧ i = i₂ := by
  have h1 := congrArg Prod.fst h
  simp only [valPt, Sum.inl.injEq, TapeTag.val.injEq] at h1
  exact h1

omit [LinearOrder A] in
/-- **Two symbols that are the same point sit in the same cell**, so a walk may
write back to it with a different bit. -/
theorem valPt_eq_of_valPt_eq (hdim : blockArityBound B ≤ dim) (b₃ : Bool) {b b₂ r r₂ : Bool}
    {i i₂ : B.ι} {ā : Fin (B.arity i) → A} {ā₂ : Fin (B.arity i₂) → A}
    (h : valPt (C := C) (dim := dim) a₀ b r i ā = valPt a₀ b₂ r₂ i₂ ā₂) :
    valPt (C := C) (dim := dim) a₀ b₃ r i ā = valPt a₀ b₃ r₂ i₂ ā₂ := by
  obtain ⟨rfl, rfl, rfl⟩ := valPt_inj_tag a₀ h
  have hle : B.arity i ≤ dim := (arity_le_blockArityBound B i).trans hdim
  have hā : ā = ā₂ := by
    rw [← pref_pad a₀ hle ā, ← pref_pad a₀ hle ā₂]
    exact congrArg (pref hle) (congrArg Prod.snd h)
  rw [hā]

omit [LinearOrder A] in
/-- **A symbol determines its address**, at a fixed relation variable. -/
theorem args_eq_of_valPt_eq (hdim : blockArityBound B ≤ dim) {b b₂ r r₂ : Bool} {i : B.ι}
    {ā ā₂ : Fin (B.arity i) → A}
    (h : valPt (C := C) (dim := dim) a₀ b r i ā = valPt a₀ b₂ r₂ i ā₂) : ā = ā₂ := by
  have hle : B.arity i ≤ dim := (arity_le_blockArityBound B i).trans hdim
  rw [← pref_pad a₀ hle ā, ← pref_pad a₀ hle ā₂]
  exact congrArg (pref hle) (congrArg Prod.snd h)

omit [LinearOrder A] in
/-- **The cell a symbol sits in**, from the symbol read at it. -/
theorem cellPt_eq_of_valPt_eq (hdim : blockArityBound B ≤ dim) {b b₂ r r₂ : Bool}
    {i i₂ : B.ι} {ā : Fin (B.arity i) → A} {ā₂ : Fin (B.arity i₂) → A}
    (h : valPt (C := C) (dim := dim) a₀ b r i ā = valPt a₀ b₂ r₂ i₂ ā₂) :
    cellPt (C := C) (dim := dim) a₀ r i ā = cellPt a₀ r₂ i₂ ā₂ := by
  obtain ⟨rfl, rfl, rfl⟩ := valPt_inj_tag a₀ h
  have hle : B.arity i ≤ dim := (arity_le_blockArityBound B i).trans hdim
  have hā : ā = ā₂ := by
    rw [← pref_pad a₀ hle ā, ← pref_pad a₀ hle ā₂]
    exact congrArg (pref hle) (congrArg Prod.snd h)
  rw [hā]

/-- A cell is in the domain. -/
theorem machDom_cellPt {carity : C → ℕ} (h₀ : IsBot a₀) (r : Bool) (i : B.ι)
    (ā : Fin (B.arity i) → A) : machDom (dim := dim) carity (cellPt a₀ r i ā) :=
  canon_pad h₀ _ ā

end Points

/-! ### The ends of the tape -/

section Ends

variable {B : SOBlock} {C : Type} [Finite C] {dim : ℕ} {A : Type} [LinearOrder A]
  {a₀ : A} (h₀ : IsBot a₀) {carity : C → ℕ}

include h₀

omit [Finite C] in
/-- A point of the domain whose tag uses no coordinate is the constant tuple:
the sentinels and the mark carry exactly one point each. -/
theorem eq_const_of_dom {p : Pt B C dim A} (hp : machDom carity p)
    (harity : MachTag.arity carity p.1 = 0) : p.2 = fun _ => a₀ :=
  funext fun j => le_antisymm (hp j (by omega) a₀) (h₀ _)

/-- **The lowest position is the first left sentinel.** -/
theorem minPos_leftPt :
    letI := machTagOrder (B := B) (C := C)
    MinPos (tagTupleLe (Tag := MachTag B C) (d := dim) (A := A))
      (fun p => machPosn p ∧ machDom carity p) (leftPt a₀ false) := by
  let := machTagOrder (B := B) (C := C)
  refine ⟨⟨trivial, fun j _ => h₀⟩, fun q hq => ?_⟩
  rcases Nat.eq_zero_or_pos (MachTag.fam q.1) with hf | hf
  · obtain ⟨s, hs, _⟩ := MachTag.exists_tapeTag_of_isPos hq.1
    have hs0 : s = .left false := TapeTag.eq_left_false_of_fam_zero (by rw [hs] at hf; exact hf)
    have htag : q.1 = Sum.inl (TapeTag.left false) := by rw [hs, hs0]
    have harity : MachTag.arity carity q.1 = 0 := by rw [htag]; rfl
    have hq2 : q = leftPt a₀ false := Prod.ext htag (eq_const_of_dom h₀ hq.2 harity)
    exact Or.inr ⟨congrArg Prod.fst hq2.symm, Or.inl (congrArg Prod.snd hq2.symm)⟩
  · exact Or.inl (machTag_lt_of_fam_lt (t := (leftPt a₀ false : Pt B C dim A).1) (t' := q.1) hf)

/-- **Only the two sentinels sit at or below the second one.** -/
theorem eq_leftPt_of_le {q : Pt B C dim A} (hq : machPosn q ∧ machDom carity q)
    (hle : letI := machTagOrder (B := B) (C := C)
      tagTupleLe (Tag := MachTag B C) (d := dim) (A := A) q (leftPt a₀ true)) :
    q = leftPt a₀ false ∨ q = leftPt a₀ true := by
  let := machTagOrder (B := B) (C := C)
  have hfam : MachTag.fam q.1 ≤ 1 := by
    rcases hle with h | ⟨h, -⟩
    · exact machTag_fam_le_of_le h.le
    · exact le_of_eq (congrArg MachTag.fam h)
  obtain ⟨s, hs, -⟩ := MachTag.exists_tapeTag_of_isPos hq.1
  have hsfam : TapeTag.fam s = MachTag.fam q.1 := by rw [hs]; rfl
  rcases Nat.lt_or_ge (MachTag.fam q.1) 1 with hf | hf
  · have htag : q.1 = Sum.inl (TapeTag.left false) := by
      rw [hs, TapeTag.eq_left_false_of_fam_zero (t := s) (by omega)]
    exact Or.inl (Prod.ext htag (eq_const_of_dom h₀ hq.2 (by rw [htag]; rfl)))
  · have htag : q.1 = Sum.inl (TapeTag.left true) := by
      rw [hs, TapeTag.eq_left_true_of_fam_one (t := s) (by omega)]
    exact Or.inr (Prod.ext htag (eq_const_of_dom h₀ hq.2 (by rw [htag]; rfl)))

omit h₀ in
/-- Both sentinels sit at or below the second one. -/
theorem leftPt_le_leftPt_true (b : Bool) :
    letI := machTagOrder (B := B) (C := C)
    tagTupleLe (Tag := MachTag B C) (d := dim) (A := A) (leftPt a₀ b) (leftPt a₀ true) := by
  let := machTagOrder (B := B) (C := C)
  cases b with
  | false =>
    exact Or.inl (machTag_lt_of_fam_lt (by simp [leftPt, MachTag.fam, TapeTag.fam]))
  | true => exact Or.inr ⟨rfl, Or.inl rfl⟩

/-- **The two left sentinels are adjacent.** This is the one order fact about
the layout the development needs: a rewind hands over on reading the left mark
and moves left in the same step, so it has to land on the *lowest* position,
and it does exactly because nothing sits between the two sentinels. -/
theorem succPos_leftPt :
    letI := machTagOrder (B := B) (C := C)
    SuccPos (tagTupleLe (Tag := MachTag B C) (d := dim) (A := A))
      (fun p => machPosn p ∧ machDom carity p) (leftPt a₀ false) (leftPt a₀ true) := by
  let := machTagOrder (B := B) (C := C)
  have hlt : (leftPt (B := B) (C := C) (dim := dim) a₀ false).1 <
      (leftPt (B := B) (C := C) (dim := dim) a₀ true).1 :=
    machTag_lt_of_fam_lt (by simp [leftPt, MachTag.fam, TapeTag.fam])
  exact ⟨⟨trivial, fun j _ => h₀⟩, ⟨trivial, fun j _ => h₀⟩, Or.inl hlt,
    fun hc => absurd (congrArg Prod.fst hc) (ne_of_lt hlt),
    fun q hq _ hle => eq_leftPt_of_le h₀ hq hle⟩

/-- **Nothing above the second sentinel sits next to the first**: the second one
is between them. So a leftward walk leaving a cell – or the right sentinel –
does not land on the lowest position, which is what tells a rewind that it
still has the left mark to read. -/
theorem succPos_ne_leftPt {p q : Pt B C dim A} (hfam : 1 < MachTag.fam q.1)
    (hs : letI := machTagOrder (B := B) (C := C)
      SuccPos (tagTupleLe (Tag := MachTag B C) (d := dim) (A := A))
        (fun x => machPosn x ∧ machDom carity x) p q) :
    p ≠ leftPt a₀ false := by
  let := machTagOrder (B := B) (C := C)
  rintro rfl
  rcases hs.2.2.2.2 (leftPt a₀ true) ⟨trivial, fun j _ => h₀⟩
    (succPos_leftPt h₀ (carity := carity)).2.2.1
    (Or.inl (machTag_lt_of_fam_lt (by simpa [leftPt, MachTag.fam, TapeTag.fam] using hfam)))
    with h | h
  · simpa [leftPt] using congrArg Prod.fst h
  · exfalso
    have h1 : MachTag.fam q.1 = 1 := by rw [← h]; rfl
    omega

omit [Finite C] [LinearOrder A] h₀ in
/-- A cell sits above the second sentinel. -/
theorem one_lt_fam_cellPt (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) :
    1 < MachTag.fam (cellPt (C := C) (dim := dim) a₀ r i ā).1 := by
  cases r <;> simp [cellPt, MachTag.fam, TapeTag.fam]

omit [Finite C] [LinearOrder A] h₀ in
/-- So does the right sentinel. -/
theorem one_lt_fam_rightPt : 1 < MachTag.fam (rightPt (B := B) (C := C) (dim := dim) a₀).1 := by
  simp [rightPt, MachTag.fam, TapeTag.fam]

omit [Finite C] in
/-- **What a position is**: a left sentinel, a cell, or the right sentinel –
which is where every walk's step analysis begins, the symbol under the head
following from the case. -/
theorem posn_cases_tape (hdim : blockArityBound B ≤ dim) {p : Pt B C dim A}
    (hp : machPosn p) (hd : machDom carity p) :
    (∃ b, p = leftPt a₀ b) ∨ (∃ (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A),
      p = cellPt a₀ r i ā) ∨ p = rightPt a₀ := by
  obtain ⟨s, hs, hsp⟩ := MachTag.exists_tapeTag_of_isPos hp
  have harity : MachTag.arity carity p.1 = TapeTag.arity s := by rw [hs]; rfl
  cases s with
  | left b =>
    exact Or.inl ⟨b, Prod.ext hs (eq_const_of_dom h₀ hd (by rw [harity]; rfl))⟩
  | right =>
    exact Or.inr (Or.inr (Prod.ext hs (eq_const_of_dom h₀ hd (by rw [harity]; rfl))))
  | cell r i =>
    have hle : B.arity i ≤ dim := (arity_le_blockArityBound B i).trans hdim
    refine Or.inr (Or.inl ⟨r, i, pref hle p.2, Prod.ext hs ?_⟩)
    have hc : Canon (B.arity i) p.2 := by
      have : Canon (TapeTag.arity (TapeTag.cell r i)) p.2 := harity ▸ hd
      exact this
    exact (pad_pref_of_canon h₀ hle hc).symm
  | val b r i => exact hsp.elim
  | mark b => exact hsp.elim

/-- **The highest position is the right sentinel.** -/
theorem maxPos_rightPt :
    letI := machTagOrder (B := B) (C := C)
    MaxPos (tagTupleLe (Tag := MachTag B C) (d := dim) (A := A))
      (fun p => machPosn p ∧ machDom carity p) (rightPt a₀) := by
  let := machTagOrder (B := B) (C := C)
  refine ⟨⟨trivial, fun j _ => h₀⟩, fun q hq => ?_⟩
  obtain ⟨s, hs, hsp⟩ := MachTag.exists_tapeTag_of_isPos hq.1
  rcases Nat.lt_or_ge (MachTag.fam q.1) 4 with hf | hf
  · exact Or.inl (machTag_lt_of_fam_lt (t := q.1) (t' := (rightPt a₀ : Pt B C dim A).1) hf)
  · have hf4 : TapeTag.fam s = 4 := le_antisymm (TapeTag.fam_le_four hsp) (by rwa [hs] at hf)
    have htag : q.1 = Sum.inl (TapeTag.right (B := B)) := by
      rw [hs, TapeTag.eq_right_of_fam_four hf4]
    have harity : MachTag.arity carity q.1 = 0 := by rw [htag]; rfl
    have hq2 : q = rightPt a₀ := Prod.ext htag (eq_const_of_dom h₀ hq.2 harity)
    exact Or.inr ⟨congrArg Prod.fst hq2, Or.inl (congrArg Prod.snd hq2)⟩

end Ends

/-! ### A tape is a pair of assignments -/

section Tape

variable {B : SOBlock} {C : Type} {dim : ℕ} {A : Type} (a₀ : A)

/-- **The assignment a tape holds in region `r`**: the atom `i ā` belongs to it
exactly when the cell of that atom carries the bit `true`. -/
def assignOfTape (tape : Pt B C dim A → Pt B C dim A) (r : Bool) : B.Assignment A :=
  fun i ā => tape (cellPt a₀ r i ā) = valPt a₀ true r i ā

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

open Classical in
/-- **The symbol a cell carries is the cell's own address**, tagged with the bit
the assignment gives its atom. This is what lets a walk recognize where it is
from what it reads. -/
theorem tapeOfAssign_cellPt (hdim : blockArityBound B ≤ dim) (ρ σ : B.Assignment A)
    (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) :
    tapeOfAssign (C := C) a₀ hdim ρ σ (cellPt a₀ r i ā) =
      valPt a₀ (decide (cond r σ ρ i ā)) r i ā := by
  classical
  have hle : B.arity i ≤ dim := (arity_le_blockArityBound B i).trans hdim
  simp only [tapeOfAssign, cellPt, pref_pad a₀ hle ā]

/-- The left sentinels carry the left mark. -/
theorem tapeOfAssign_leftPt (hdim : blockArityBound B ≤ dim) (ρ σ : B.Assignment A) (b : Bool) :
    tapeOfAssign (C := C) a₀ hdim ρ σ (leftPt a₀ b) = markPt a₀ false := by
  simp only [tapeOfAssign, leftPt]

/-- The right sentinel carries the right mark, which is what tells a rightward
walk that it is over. -/
theorem tapeOfAssign_rightPt (hdim : blockArityBound B ≤ dim) (ρ σ : B.Assignment A) :
    tapeOfAssign (C := C) a₀ hdim ρ σ (rightPt a₀) = markPt a₀ true := by
  simp only [tapeOfAssign, rightPt]

/-- **The tape of two assignments holds them back.** -/
theorem assignOfTape_tapeOfAssign (hdim : blockArityBound B ≤ dim) (ρ σ : B.Assignment A)
    (r : Bool) :
    assignOfTape (C := C) a₀ (tapeOfAssign a₀ hdim ρ σ) r = cond r σ ρ := by
  classical
  funext i ā
  rw [assignOfTape, tapeOfAssign_cellPt a₀ hdim ρ σ r i ā]
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · simpa using valPt_inj_bit a₀ h
  · exact congrArg (fun b => valPt a₀ b r i ā) (by simpa using h)

end Tape

/-! ### One cell of an assignment, rewritten -/

section Update

variable {B : SOBlock} {C : Type} {dim : ℕ} {A : Type} (a₀ : A)

open Classical in
/-- **An assignment with one atom's value changed**: what one step of a sweep
does to the region it is writing. Named rather than written inline, because
`DescriptiveComplexity.SOBlock.Assignment` is a non-reducible `def`. -/
noncomputable def updAssign {B : SOBlock} {A : Type} (α : B.Assignment A) (i : B.ι)
    (ā : Fin (B.arity i) → A) (b : Bool) : B.Assignment A :=
  fun i' ā' => if (⟨i', ā'⟩ : Σ j : B.ι, Fin (B.arity j) → A) = ⟨i, ā⟩ then b = true else α i' ā'

theorem updAssign_self {B : SOBlock} {A : Type} (α : B.Assignment A) (i : B.ι)
    (ā : Fin (B.arity i) → A) (b : Bool) : updAssign α i ā b i ā = (b = true) := by
  classical
  rw [updAssign, if_pos rfl]

theorem updAssign_of_ne {B : SOBlock} {A : Type} (α : B.Assignment A) (i : B.ι)
    (ā : Fin (B.arity i) → A) (b : Bool) {i' : B.ι} {ā' : Fin (B.arity i') → A}
    (h : (⟨i', ā'⟩ : Σ j : B.ι, Fin (B.arity j) → A) ≠ ⟨i, ā⟩) :
    updAssign α i ā b i' ā' = α i' ā' := by
  classical
  rw [updAssign, if_neg h]

variable [LinearOrder A] {carity : C → ℕ}

open Classical in
/-- **A sweep step rewrites one cell, and the tape is again a pair of
assignments** – a pair agreeing with the old one outside the region being
written. This is the whole content of the sweep's invariant: what it has done so
far is *some* assignment of that region. -/
theorem exists_tapeOfAssign_upd (h₀ : IsBot a₀) (hdim : blockArityBound B ≤ dim)
    (ρ' σ' : B.Assignment A) (tgt : Bool) (i : B.ι) (ā : Fin (B.arity i) → A) (b' : Bool) :
    ∃ ρ'' σ'' : B.Assignment A, (∀ rr : Bool, rr ≠ tgt → cond rr σ'' ρ'' = cond rr σ' ρ') ∧
      (∀ q : Pt B C dim A, machPosn q → machDom carity q → q ≠ cellPt a₀ tgt i ā →
        tapeOfAssign a₀ hdim ρ'' σ'' q = tapeOfAssign a₀ hdim ρ' σ' q) ∧
      tapeOfAssign (C := C) (dim := dim) a₀ hdim ρ'' σ'' (cellPt a₀ tgt i ā) =
        valPt a₀ b' tgt i ā := by
  classical
  set ρ'' : B.Assignment A := cond tgt ρ' (updAssign ρ' i ā b') with hρ''
  set σ'' : B.Assignment A := cond tgt (updAssign σ' i ā b') σ' with hσ''
  have hkeep : ∀ rr : Bool, rr ≠ tgt → cond rr σ'' ρ'' = cond rr σ' ρ' := by
    intro rr hrr
    cases tgt <;> cases rr <;> simp_all
  have htgt : cond tgt σ'' ρ'' = updAssign (cond tgt σ' ρ') i ā b' := by
    cases tgt <;> simp [hρ'', hσ'']
  refine ⟨ρ'', σ'', hkeep, ?_, ?_⟩
  · intro q hq hd hne
    rcases posn_cases_tape h₀ hdim hq hd with ⟨b, hb⟩ | ⟨r₁, i₁, ā₁, hcell⟩ | hr
    · rw [hb, tapeOfAssign_leftPt, tapeOfAssign_leftPt]
    · rw [hcell, tapeOfAssign_cellPt, tapeOfAssign_cellPt]
      by_cases hr₁ : r₁ = tgt
      · have hne' : (⟨i₁, ā₁⟩ : Σ j : B.ι, Fin (B.arity j) → A) ≠ ⟨i, ā⟩ := by
          rintro hc
          refine hne ?_
          rw [hcell, hr₁]
          obtain ⟨rfl, hā⟩ := Sigma.mk.injEq .. ▸ hc
          rw [eq_of_heq hā]
        rw [hr₁, htgt, updAssign_of_ne _ i ā b' hne']
      · rw [hkeep r₁ hr₁]
    · rw [hr, tapeOfAssign_rightPt, tapeOfAssign_rightPt]
  · rw [tapeOfAssign_cellPt]
    have hbit : decide (cond tgt σ'' ρ'' i ā) = b' := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, htgt, updAssign_self]
    rw [hbit]

end Update

/-! ### A tape is only ever read at a position -/

section Agree

variable {B : SOBlock} {C : Type} {dim : ℕ} {A : Type} [LinearOrder A] (a₀ : A)
  {carity : C → ℕ}

/-- **Two tapes that agree at the positions hold the same assignments.** A
machine reads its tape only under its head, and its head is always a position,
so this is the only sense in which a walk has to control the tape – the
*non-canonical* tagged tuples, which are not positions, keep whatever they
started with and are never read. -/
theorem assignOfTape_congr (h₀ : IsBot a₀) {t u : Pt B C dim A → Pt B C dim A}
    (h : ∀ p, machPosn p → machDom carity p → t p = u p) (r : Bool) :
    assignOfTape a₀ t r = assignOfTape a₀ u r := by
  funext i ā
  rw [assignOfTape, assignOfTape,
    h (cellPt a₀ r i ā) (machPosn_cellPt a₀ r i ā) (machDom_cellPt a₀ h₀ r i ā)]

end Agree

/-! ### The initial tape -/

section Init

variable {B : SOBlock} {C : Type} {dim : ℕ} {A : Type} (a₀ : A)
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

variable {a₀ hdim}

/-- **The input is functional.** -/
theorem machInp_functional {p x y : Pt B C dim A} (hx : machInp a₀ hdim p x)
    (hy : machInp a₀ hdim p y) : x = y := hx.2.trans hy.2.symm

variable (a₀ hdim)

end Init

end DescriptiveComplexity
