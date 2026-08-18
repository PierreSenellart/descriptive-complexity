/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawAddr
import DescriptiveComplexity.Problems.Wide.DrawTracks

/-!
# The slots of the EXPSPACE program, and the mark of a register cell

The first concrete piece of the program: which **track slots** a symbol
carries, which **control slots** a state carries, and what the input channel
writes in the cell of each element at time zero. Nothing here depends on the
program's phases, so it is fixed before they are enumerated.

## The track slots (`DescriptiveComplexity.Draw.Slot`)

| slot | held by | what it says |
|---|---|---|
| `reg` | every mark | this cell is a register |
| `regFirst`, `regLast` | the two end marks | the ends of the file, recognizable on sight |
| `blk b` | every mark, one-hot | the argument block of the cell's tag (`none` off the arguments) |
| `name j` | padded marks | the cell's element's `j`-th coordinate – an *element*, not a bit |
| `pdd` | every mark | the cell's element is canonically padded |
| `mir`, `tgt`, `sav`, `val` | register cells | MIRROR, TARGET, SAV, VAL – the machine's registers |
| `wk`, `bot` | the working area | the working-cell marker, the bottom marker |
| `ltp` | the working area | the end marker of the logical interval, planted at startup |
| `old i`, `new i` | the working area | the current and next stage of variable `i` |

The name slots are the budgeted register naming: a
mark cannot carry its cell's *full* name (`|Q| + |W| ≤ dd`), but the encodings
only inhabit the first `dd₀ < dd` coordinates, and those fit. Together with
`pdd` and the one-hot `blk` family they are what the navigation-by-name scans
(`DescriptiveComplexity.Draw.Prog.reaches_toCell`) read.

## The control slots (`DescriptiveComplexity.Draw.Ctl`)

Loop variables (elements of the source structure, for the element loops of the
atom subroutines), the fold accumulators of the inner loop, the accumulators of
the element-loop sub-folds, the atom verdicts of the matrix, and a few scratch
flags. All bits are stored as the two designated elements
(`DescriptiveComplexity.Draw.bitVal`).

`DescriptiveComplexity.Draw.slotMark` is the mark itself, with one read-back
lemma per slot kind; `DescriptiveComplexity.Draw.slotMark_name` is the one the
counting argument of `Problems/Wide/Marks.lean` allows, and the one everything
else was built to reach.
-/

namespace DescriptiveComplexity

namespace Draw

/-! ### The track slots -/

/-- **The track slots of the program's symbols.** `ι` is the index type of the
fixed-point variables, `ko`/`ki` the numbers of outer and inner argument
blocks, `dd0` the coordinate width of the encodings. -/
inductive Slot (ι : Type) (ko ki dd0 : ℕ) : Type
  /-- This cell is a register. -/
  | reg : Slot ι ko ki dd0
  /-- This cell is the first register of the file. -/
  | regFirst : Slot ι ko ki dd0
  /-- This cell is the last register of the file. -/
  | regLast : Slot ι ko ki dd0
  /-- One-hot: the argument block of the cell's element's tag. -/
  | blk : Option (Fin ko ⊕ Fin ki) → Slot ι ko ki dd0
  /-- The cell's element's `j`-th coordinate, when it is padded. -/
  | name : Fin dd0 → Slot ι ko ki dd0
  /-- The cell's element is canonically padded. -/
  | pdd : Slot ι ko ki dd0
  /-- The mirror of the working cell's address. -/
  | mir : Slot ι ko ki dd0
  /-- The target of a random access. -/
  | tgt : Slot ι ko ki dd0
  /-- The saved mirror, across a random access. -/
  | sav : Slot ι ko ki dd0
  /-- The valuation of the quantifier prefix, enumerated by the inner loop. -/
  | val : Slot ι ko ki dd0
  /-- The working-cell marker. -/
  | wk : Slot ι ko ki dd0
  /-- The bottom marker, written at the empty address at startup. -/
  | bot : Slot ι ko ki dd0
  /-- The end marker of the logical interval, planted at
  `DescriptiveComplexity.Draw.logicalTop` at startup: what the plain sweeps
  stop at. -/
  | ltp : Slot ι ko ki dd0
  /-- The current stage of variable `i`. -/
  | old : ι → Slot ι ko ki dd0
  /-- The next stage of variable `i`. -/
  | new : ι → Slot ι ko ki dd0
  deriving DecidableEq

namespace Slot

variable {ι : Type} {ko ki dd0 : ℕ}

private def toSum : Slot ι ko ki dd0 →
    (Option (Fin ko ⊕ Fin ki) ⊕ Fin dd0 ⊕ ι ⊕ ι) ⊕ Fin 11
  | .blk b => Sum.inl (Sum.inl b)
  | .name j => Sum.inl (Sum.inr (Sum.inl j))
  | .old i => Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))
  | .new i => Sum.inl (Sum.inr (Sum.inr (Sum.inr i)))
  | .reg => Sum.inr 0
  | .regFirst => Sum.inr 1
  | .regLast => Sum.inr 2
  | .pdd => Sum.inr 3
  | .mir => Sum.inr 4
  | .tgt => Sum.inr 5
  | .sav => Sum.inr 6
  | .val => Sum.inr 7
  | .wk => Sum.inr 8
  | .bot => Sum.inr 9
  | .ltp => Sum.inr 10

instance [Finite ι] : Finite (Slot ι ko ki dd0) := by
  refine Finite.of_injective toSum ?_
  intro a b h
  cases a <;> cases b <;> simp_all [toSum]

noncomputable instance [Finite ι] : Fintype (Slot ι ko ki dd0) := Fintype.ofFinite _

end Slot

/-! ### The control slots -/

/-- **The control slots of the program's states**: loop variables, the inner
fold's accumulators, the sub-folds' accumulators, the atom verdicts, the
leaf-read and tag-witness flags, and scratch flags. -/
inductive Ctl (e na nat nf ntg : ℕ) : Type
  /-- A loop variable of an element loop. -/
  | lv : Fin e → Ctl e na nat nf ntg
  /-- An accumulator of the inner fold. -/
  | acc : Fin na → Ctl e na nat nf ntg
  /-- An accumulator of an element-loop sub-fold. -/
  | sac : Fin e → Ctl e na nat nf ntg
  /-- The verdict of an atom of the matrix. -/
  | av : Fin nat → Ctl e na nat nf ntg
  /-- The verdict of a leaf read of the current element-loop round. -/
  | rdf : Fin nf → Ctl e na nat nf ntg
  /-- A tag-witness flag, one-hot over argument positions and tags. -/
  | tgf : Fin ntg → Ctl e na nat nf ntg
  /-- A scratch flag. -/
  | flag : Fin 8 → Ctl e na nat nf ntg
  deriving DecidableEq

namespace Ctl

variable {e na nat nf ntg : ℕ}

private def toSum : Ctl e na nat nf ntg →
    Fin e ⊕ Fin na ⊕ Fin e ⊕ Fin nat ⊕ Fin nf ⊕ Fin ntg ⊕ Fin 8
  | .lv j => Sum.inl j
  | .acc j => Sum.inr (Sum.inl j)
  | .sac j => Sum.inr (Sum.inr (Sum.inl j))
  | .av a => Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))
  | .rdf a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))
  | .tgf a => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))))
  | .flag k => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr k)))))

instance : Finite (Ctl e na nat nf ntg) := by
  refine Finite.of_injective toSum ?_
  intro a b h
  cases a <;> cases b <;> simp_all [toSum]

noncomputable instance : Fintype (Ctl e na nat nf ntg) := Fintype.ofFinite _

end Ctl

/-! ### The mark of a register cell -/

section Mark

variable {R P ι : Type} {ko ki dd0 dd : ℕ} {A : Type}
variable [LinearOrder R] [LinearOrder P]

/-- The argument block of a tag, `none` off the arguments: what the one-hot
`blk` slots of a mark record. -/
def tagBlk : Tag R P (Fin ko ⊕ₗ Fin ki) → Option (Fin ko ⊕ Fin ki)
  | .arg i => some (ofLex i)
  | _ => none

omit [LinearOrder R] [LinearOrder P] in
/-- **The block mark decodes the tag**: only an argument tag has a block, and it
has its own. -/
theorem tagBlk_eq_some_iff (τ : Tag R P (Fin ko ⊕ₗ Fin ki))
    (b' : Fin ko ⊕ Fin ki) :
    tagBlk τ = some b' ↔ τ = Tag.arg (toLex b') := by
  cases τ with
  | ctrl r => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | sym => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | phase p => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | arg i =>
    constructor
    · intro h
      have h' : ofLex i = b' := Option.some.inj h
      subst h'
      rfl
    · intro h
      have h' : i = toLex b' := by injection h
      subst h'
      rfl

variable [LinearOrder A]

open Classical in
/-- **The mark of the cell of an element**: what the input channel writes there
at time zero. The name slots carry the element's first `dd0` coordinates, the
`blk` slots its tag's block one-hot, `pdd` whether it is canonically padded,
the two end slots whether it is an extremum of the universe order; the
machine's registers and the working-area tracks start clear. -/
noncomputable def slotMark (zero one : A) (hdd : dd0 ≤ dd)
    (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) : Slot ι ko ki dd0 → A
  | .reg => one
  | .regFirst => bitVal zero one (∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, tagTupleLe x y)
  | .regLast => bitVal zero one (∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, tagTupleLe y x)
  | .blk b => bitVal zero one (tagBlk x.1 = b)
  | .name j => x.2 (Fin.castLE hdd j)
  | .pdd => bitVal zero one (∀ j : Fin dd, dd0 ≤ (j : ℕ) → x.2 j = zero)
  | .mir => zero
  | .tgt => zero
  | .sav => zero
  | .val => zero
  | .wk => zero
  | .bot => zero
  | .ltp => zero
  | .old _ => zero
  | .new _ => zero

variable {zero one : A} {hdd : dd0 ≤ dd}

@[simp]
theorem slotMark_reg (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) :
    slotMark (ι := ι) zero one hdd x .reg = one := rfl

@[simp]
theorem slotMark_name (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) (j : Fin dd0) :
    slotMark (ι := ι) zero one hdd x (.name j) = x.2 (Fin.castLE hdd j) := rfl

/-- **Being the greatest element that carries no argument block**: the element
the *register* channel marks below its file, so that every logical address stays
clear of it and the file lies above the working area
(`DescriptiveComplexity.wmSetLt_wmRegSeg_of_above`). -/
def IsTopNonArg (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) : Prop :=
  (∀ i, x.1 ≠ Tag.arg i) ∧
    ∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, (∀ i, y.1 ≠ Tag.arg i) → tagTupleLe y x

/-- **There is only one greatest element carrying no argument block**: two of
them bound each other. -/
theorem IsTopNonArg.unique {x y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd}
    (hx : IsTopNonArg x) (hy : IsTopNonArg y) : x = y :=
  (Wide.isLinOrd_tagTupleLe (Tag := Tag R P (Fin ko ⊕ₗ Fin ki)) (A := A)
    (d := dd)).2.2.1 x y (hy.2 x hx.1) (hx.2 y hy.1)

open Classical in
/-- **The mark of the cell of an element, at the register channel**: the mark
above with one slot changed. The channel writes for the argument elements and
for one element below them, so the file's *first* register is not the least
element of the universe but the greatest element carrying no argument block –
and that is what the `regFirst` slot has to say, the walks reading the file's
ends off these two slots. The `regLast` slot needs no change: the argument tags
being the greatest, the last register is the last element. -/
noncomputable def regSlotMark (zero one : A) (hdd : dd0 ≤ dd)
    (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) (s : Slot ι ko ki dd0) : A :=
  match s with
  | .regFirst => bitVal zero one (IsTopNonArg x)
  | s => slotMark zero one hdd x s

@[simp]
theorem regSlotMark_regFirst (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) :
    regSlotMark (ι := ι) zero one hdd x .regFirst = bitVal zero one (IsTopNonArg x) := rfl

@[simp]
theorem regSlotMark_reg (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) :
    regSlotMark (ι := ι) zero one hdd x .reg = one := rfl

@[simp]
theorem regSlotMark_name (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) (j : Fin dd0) :
    regSlotMark (ι := ι) zero one hdd x (.name j) = x.2 (Fin.castLE hdd j) := rfl

@[simp]
theorem regSlotMark_regLast (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) :
    regSlotMark (ι := ι) zero one hdd x .regLast =
      bitVal zero one (∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, tagTupleLe y x) := rfl

@[simp]
theorem regSlotMark_blk (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd)
    (b : Option (Fin ko ⊕ Fin ki)) :
    regSlotMark (ι := ι) zero one hdd x (.blk b) = bitVal zero one (tagBlk x.1 = b) := rfl

@[simp]
theorem regSlotMark_pdd (x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd) :
    regSlotMark (ι := ι) zero one hdd x .pdd =
      bitVal zero one (∀ j : Fin dd, dd0 ≤ (j : ℕ) → x.2 j = zero) := rfl

/-- **The least element carries no argument block**: the argument tags are the
greatest ones (`DescriptiveComplexity.Draw.lt_arg`), so the minimum of the
universe is tagged by the control, the alphabet or a phase. This is what puts
every logical address strictly below the register file: the file's first cell
is the segment of the least element, and no logical address contains it. -/
theorem tagBlk_eq_none_of_least {x : Univ A R P (Fin ko ⊕ₗ Fin ki) dd}
    (hleast : ∀ y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd, tagTupleLe x y) :
    tagBlk (ko := ko) (ki := ki) x.1 = none := by
  match hg : x.1 with
  | .ctrl r => rfl
  | .sym => rfl
  | .phase p => rfl
  | .arg i =>
    exfalso
    rcases hleast (Tag.sym, x.2) with hlt | ⟨he, -⟩
    · rw [hg] at hlt
      exact absurd hlt (asymm (lt_arg Tag.sym i (fun j => fun h => nomatch h)))
    · rw [hg] at he
      exact nomatch he

omit [LinearOrder R] [LinearOrder P] [LinearOrder A] in
/-- **A mark determines its cell among the padded cells**: two padded elements
with the same tag block one-hots and the same name slots are equal, provided
their tags are argument tags (the block determines an argument tag). This is
what makes the navigation-by-name scans stop at exactly one cell. -/
theorem eq_of_slotMark_name
    {x y : Univ A R P (Fin ko ⊕ₗ Fin ki) dd}
    (hblk : tagBlk x.1 = tagBlk y.1) {b : Fin ko ⊕ Fin ki}
    (hb : tagBlk x.1 = some b)
    (hnm : ∀ j : Fin dd0, x.2 (Fin.castLE hdd j) = y.2 (Fin.castLE hdd j))
    (hpx : ∀ j : Fin dd, dd0 ≤ (j : ℕ) → x.2 j = zero)
    (hpy : ∀ j : Fin dd, dd0 ≤ (j : ℕ) → y.2 j = zero) : x = y := by
  obtain ⟨tx, vx⟩ := x
  obtain ⟨ty, vy⟩ := y
  have htag : tx = ty := by
    match tx, ty with
    | .arg i, .arg i' =>
      have : some (ofLex i) = some (ofLex i') := by
        simpa [tagBlk] using hblk
      have hii : ofLex i = ofLex i' := Option.some.inj this
      exact congrArg Tag.arg (ofLex.injective.eq_iff.mp hii)
    | .arg i, .ctrl r => simp [tagBlk] at hblk
    | .arg i, .sym => simp [tagBlk] at hblk
    | .arg i, .phase p => simp [tagBlk] at hblk
    | .ctrl r, _ => simp [tagBlk] at hb
    | .sym, _ => simp [tagBlk] at hb
    | .phase p, _ => simp [tagBlk] at hb
  refine Prod.ext htag (funext fun j => ?_)
  by_cases hj : (j : ℕ) < dd0
  · have := hnm ⟨(j : ℕ), hj⟩
    simpa using this
  · rw [hpx j (Nat.not_lt.mp hj), hpy j (Nat.not_lt.mp hj)]

end Mark

end Draw

end DescriptiveComplexity
