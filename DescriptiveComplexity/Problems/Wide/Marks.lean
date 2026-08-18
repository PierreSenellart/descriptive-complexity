/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Roam

/-!
# The cells a wide machine can recognize

A wide machine cannot read the digits of the address it is on, so a program
needs cells it can *identify by their contents*. The vocabulary gives it exactly
`n` of them, for free, through the input channel:

> `wmInp x a` puts the symbol `a` in the cell at the address `{y | y ≤ x}`, the
> **initial segment** cut by `x`, and every other cell starts blank.

So a reduction that writes a mark in every element's cell obtains `n`
distinguished cells, spread through the tape in the instance's own order
(`DescriptiveComplexity.wmSetLt_wmSeg`), findable by scanning
(`DescriptiveComplexity.Problems.Wide.Roam`) and reusable as the machine's
**register file**: one tape track over these `n` cells is one `n`-bit register,
and an `n`-bit register is a *mirror* of an address – the thing the head cannot
read off itself.

**The marks cannot all be different, and need not be.** A symbol *is* an element
and there is one register per element, so distinct names would need as many
symbols as elements, leaving none to be the blank – and the blank must differ from
every mark, or a blank cell of the working area would stop a scan looking for a
register. What a program actually needs is far less: the walks of
`DescriptiveComplexity.Problems.Wide.Walk` carry their pointer in the *control*
and only ever ask "is this cell a register?", so one generic mark serves them all.
Only the two ends of the file have to be recognized on sight – to begin a downward
pass and to come back from one – and two distinguished symbols pay for that.

This file says what those cells are and where they sit:

| fact | theorem |
|---|---|
| the marked cell of an element | `DescriptiveComplexity.wmSeg` |
| an address is a cell exactly when it is a segment | `DescriptiveComplexity.wmDown_iff_eq_wmSeg` |
| they are ordered like the elements | `DescriptiveComplexity.wmSetLt_wmSeg_iff` |
| nothing is marked between consecutive ones | `DescriptiveComplexity.not_wmSeg_between` |
| distinct elements mark distinct cells | `DescriptiveComplexity.wmSeg_injective` |
| the head does not start on one | `DescriptiveComplexity.wmSetLt_empty_wmSeg` |
| they all sit above the working area | `DescriptiveComplexity.wmSetLt_wmSeg_of_not_bot` |
| the working area is the interval below them | `DescriptiveComplexity.wmIncr_wmWorkTop` |
| a marked cell holds its symbol at time zero | `DescriptiveComplexity.initTape_wmSeg` |
| every other cell starts blank | `DescriptiveComplexity.initTape_of_not_wmDown` |
| the initial configuration, marks and all | `DescriptiveComplexity.isInit_wide_marks` |

Nothing here is about a program: these are facts about the vocabulary, settled
before any transition table is written.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Marks

variable {A : Type} [Language.wide.Structure A]

/-! ### The marked cell of an element -/

/-- **The cell an element marks**: the initial segment it cuts, which is where
the input channel writes its symbol. -/
def wmSeg (x : A) : A → Prop := fun y => WMLe y x

/-- The cell of an element is the address the vocabulary calls its own. -/
theorem wmDown_wmSeg (x : A) : WMDown WMLe (wmSeg x) x := fun _ => Iff.rfl

/-- **An address is the cell of an element exactly when it is its segment**, so
`DescriptiveComplexity.WMDown` never has to be unfolded again. -/
theorem wmDown_iff_eq_wmSeg (s : A → Prop) (x : A) : WMDown WMLe s x ↔ s = wmSeg x :=
  ⟨fun hd => funext fun y => propext (hd y), fun he => he ▸ wmDown_wmSeg x⟩

/-- An element lies in its own cell, so no cell is the empty address. -/
theorem wmSeg_self (h : IsLinOrd (WMLe (A := A))) (x : A) : wmSeg x x := h.1 x

variable [Finite A]

/-! ### Where the marked cells sit -/

/-- **The marked cells are ordered like the elements that mark them.** A scan
rightwards therefore meets them in the instance's own order, which is what lets a
program walk its register file with a pointer in its control. -/
theorem wmSetLt_wmSeg (h : IsLinOrd (WMLe (A := A))) {x y : A} (hlt : WMLt WMLe x y) :
    WMSetLt WMLe (wmSeg x) (wmSeg y) := by
  -- The least element of the segment of `y` that is outside that of `x`.
  obtain ⟨z, ⟨hzy, hzx⟩, hmin⟩ := exists_least h (P := fun z => wmSeg y z ∧ ¬wmSeg x z)
    ⟨y, h.1 y, fun hc => hlt.2 hc⟩
  refine ⟨z, fun w hw => ?_, hzx, hzy⟩
  refine ⟨fun hwx => h.2.1 w x y hwx hlt.1, fun hwy => ?_⟩
  by_contra hwx
  exact hw.2 (hmin w ⟨hwy, hwx⟩)

/-- **Distinct elements mark distinct cells.** This is about the *addresses*: no
two elements cut the same initial segment, so the register file really has one
cell per element. It says nothing about the symbols in them, which cannot all be
distinct (see the module docstring). -/
theorem wmSeg_injective (h : IsLinOrd (WMLe (A := A))) :
    Function.Injective (wmSeg (A := A)) := by
  intro x y he
  rcases eq_or_ne x y with rfl | hne
  · rfl
  · exfalso
    have hlin := isLinOrd_wmSetLe h
    rcases h.2.2.2 x y with hle | hle
    · exact (wmSetLt_iff _ _).mp (wmSetLt_wmSeg h ⟨hle, fun hc => hne (h.2.2.1 x y hle hc)⟩)
        |>.2 he
    · exact (wmSetLt_iff _ _).mp (wmSetLt_wmSeg h ⟨hle, fun hc => hne (h.2.2.1 x y hc hle)⟩)
        |>.2 he.symm

/-- **The marked cells are ordered *exactly* like the elements**, so a program
reading its register file recovers the order of the instance and nothing else.
The direction that matters is the one this adds: a mark below another mark comes
from an element below the other's. -/
theorem wmSetLt_wmSeg_iff (h : IsLinOrd (WMLe (A := A))) (x y : A) :
    WMSetLt WMLe (wmSeg x) (wmSeg y) ↔ WMLt WMLe x y := by
  refine ⟨fun hlt => ?_, wmSetLt_wmSeg h⟩
  have hlin := isLinOrd_wmSetLe h
  by_contra hc
  rcases h.2.2.2 y x with hyx | hxy
  · rcases eq_or_ne y x with rfl | hne
    · exact ((wmSetLt_iff _ _).mp hlt).2 rfl
    · exact ((wmSetLt_iff _ _).mp hlt).2 (hlin.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt).1
        ((wmSetLt_iff _ _).mp (wmSetLt_wmSeg h ⟨hyx, fun hcon => hne (h.2.2.1 y x hyx hcon)⟩)).1)
  · exact hc ⟨hxy, fun hcon => ((wmSetLt_iff _ _).mp hlt).2
      (congrArg wmSeg (h.2.2.1 x y hxy hcon))⟩

/-- **Consecutive elements mark consecutive cells**: no cell strictly between the
cell of an element and the cell of its successor is marked. That is what a
program walking its register file needs – one scan carries it from each register
to the next, and nothing it passes can be mistaken for a register. -/
theorem not_wmSeg_between (h : IsLinOrd (WMLe (A := A))) {u u' : A}
    (hsucc : ∀ v : A, WMLt WMLe u v → WMLe u' v) {r : A → Prop}
    (h1 : WMSetLt WMLe (wmSeg u) r) (h2 : WMSetLt WMLe r (wmSeg u')) (x : A) : r ≠ wmSeg x := by
  rintro rfl
  have hux : WMLt WMLe u x := (wmSetLt_wmSeg_iff h u x).mp h1
  exact ((wmSetLt_wmSeg_iff h x u').mp h2).2 (hsucc x hux)

/-- **The head does not start on a marked cell**: it starts on the empty address,
and every marked cell holds the element that marks it. So a program may write its
own left-end marker where it stands without disturbing the register file. -/
theorem wmSetLt_empty_wmSeg (h : IsLinOrd (WMLe (A := A))) (x : A) :
    WMSetLt WMLe (fun _ => False) (wmSeg x) := by
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_empty h (fun _ hc => hc) _, fun hc => ?_⟩
  have hx : wmSeg x x := wmSeg_self h x
  rw [← hc] at hx
  exact hx

/-! ### The register file and the working area

The least element of the instance is the **most significant** digit of an address
(`DescriptiveComplexity.Problems.Wide.Increment`), and every marked cell contains
it. So the register file sits entirely in the upper half of the tape and the
addresses that do *not* contain the least element – the **working area**, half the
tape, exponentially many cells – lie below every register. A program's data
therefore cannot collide with its registers: it reaches the file by scanning
right and comes back by scanning left. -/

omit [Finite A] in
/-- **Every marked cell contains the least element.** -/
theorem wmSeg_bot {bot : A} (hbot : ∀ v : A, WMLe bot v) (x : A) : wmSeg x bot := hbot x

omit [Finite A] in
/-- **The working area lies below the register file.** An address missing the
least element is below every marked cell, that element being the most significant
digit – so the two never meet, whatever a program writes. -/
theorem wmSetLt_wmSeg_of_not_bot {bot : A} (hbot : ∀ v : A, WMLe bot v) {r : A → Prop}
    (hr : ¬r bot) (x : A) : WMSetLt WMLe r (wmSeg x) :=
  ⟨bot, fun y hy => absurd (hbot y) hy.2, hr, hbot x⟩

/-- **The last cell of the working area**: the address holding every element but
the least. A program's loops run over the interval from the empty address to this
one, and `DescriptiveComplexity.reaches_of_wideRounds` is given those two
endpoints. -/
def wmWorkTop (bot : A) : A → Prop := fun v => v ≠ bot

omit [Finite A] in
/-- **The working area ends exactly where the register file begins**: the top of
the working area is the *predecessor* of the first register. So a machine that
runs off the end of its data steps straight onto its registers, and nothing lies
between. -/
theorem wmIncr_wmWorkTop (h : IsLinOrd (WMLe (A := A))) {bot : A} (hbot : ∀ v : A, WMLe bot v) :
    WMIncr WMLe (wmWorkTop bot) (wmSeg bot) := by
  refine ⟨bot, fun hc => hc rfl, fun v hv => hv.2 ∘ fun hc => hc ▸ hbot v, fun v => ?_⟩
  refine ⟨fun hle => Or.inl (h.2.2.1 v bot hle (hbot v)), ?_⟩
  rintro (heq | ⟨-, hnlt⟩)
  · rw [heq]
    exact h.1 bot
  · by_contra hc
    exact hnlt ⟨hbot v, hc⟩

/-! ### The initial tape -/

omit [Finite A] in
/-- **A marked cell starts holding its symbol.** The input is functional in a
well-formed instance, so this is the only symbol it can hold. -/
theorem initTape_wmSeg {x a : A} (hinp : WMInp x a) :
    (wideData A).InitTape (Sum.inl (wmSeg x)) (Sum.inr a) :=
  Or.inl ⟨x, wmDown_wmSeg x, hinp⟩

omit [Finite A] in
/-- **Every unmarked cell starts blank.** Two ways for a cell to be unmarked: it
is not the segment of any element, or the elements whose segment it is carry no
input symbol. -/
theorem initTape_of_not_wmDown {s : A → Prop} (hno : ∀ x y : A, WMDown WMLe s x → ¬WMInp x y)
    (a : WPoint A) : (wideData A).InitTape (Sum.inl s) a ↔ (wideData A).Blank a := by
  have hinp : ∀ b : WPoint A, ¬(wideData A).Inp (Sum.inl s) b := by
    rintro (t | y)
    · exact fun hc => hc
    · rintro ⟨x, hd, hi⟩
      exact hno x y hd hi
  exact ⟨fun hc => hc.elim (fun hc' => absurd hc' (hinp a)) fun hc' => hc'.2,
    fun hc => Or.inr ⟨hinp, hc⟩⟩

omit [Finite A] in
/-- **The initial tape of a program with a register file**: the naming symbol of
`x` in the cell of `x`, the blank in every other cell. A reduction gives the
symbol as a function `sym` of the element and marks nothing else; the tape it
gets is then a *function*, which is what a run has to be given. -/
theorem initTape_of_marks {b : A} (hb : WMBlank b) {sym : A → A}
    (hinp : ∀ x : A, WMInp x (sym x)) {tp : WPoint A → WPoint A}
    (hmark : ∀ x : A, tp (Sum.inl (wmSeg x)) = Sum.inr (sym x))
    (hrest : ∀ p : WPoint A, (∀ x : A, p ≠ Sum.inl (wmSeg x)) → tp p = Sum.inr b) :
    ∀ p, (wideData A).InitTape p (tp p) := by
  rintro (s | y)
  · by_cases hex : ∃ x : A, s = wmSeg x
    · obtain ⟨x, rfl⟩ := hex
      rw [hmark x]
      exact initTape_wmSeg (hinp x)
    · rw [hrest _ fun x hc => hex ⟨x, Sum.inl_injective hc⟩]
      exact (initTape_of_not_wmDown
        (fun z c hd _ => hex ⟨z, (wmDown_iff_eq_wmSeg _ z).mp hd⟩) _).mpr hb
  · rw [hrest _ fun x hc => Sum.inl_ne_inr hc.symm]
    exact Or.inr ⟨fun c hc => hc, hb⟩

/-- **The initial configuration of a program with a register file**: a start
state, the head on the empty address – which is no element's cell – and the
marked tape of `DescriptiveComplexity.initTape_of_marks`. -/
theorem isInit_wide_marks (h : IsLinOrd (WMLe (A := A))) {b : A} (hb : WMBlank b)
    {sym : A → A} (hinp : ∀ x : A, WMInp x (sym x)) {tp : WPoint A → WPoint A}
    (hmark : ∀ x : A, tp (Sum.inl (wmSeg x)) = Sum.inr (sym x))
    (hrest : ∀ p : WPoint A, (∀ x : A, p ≠ Sum.inl (wmSeg x)) → tp p = Sum.inr b)
    {q₀ : A} (hq : WMStart q₀) :
    (wideData A).IsInit ⟨Sum.inr q₀, Sum.inl fun _ => False, tp⟩ :=
  ⟨hq, minPos_wpLe h, initTape_of_marks hb hinp hmark hrest⟩

end Marks

end DescriptiveComplexity
