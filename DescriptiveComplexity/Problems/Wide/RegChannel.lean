/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Wide.Marks
import DescriptiveComplexity.Problems.Wide.Roam
import DescriptiveComplexity.Problems.Wide.RegFile

/-!
# The wide machine with a register channel

`DescriptiveComplexity.WideAccept` writes the input symbol of an element `x` at
the address `{y | y ≤ x}`, the initial segment `x` cuts. The order on addresses
reads the *least* element as the most significant digit, so that address is
above `2 ^ (n − 1)` whatever `x` is: the input lies on a geometric ruler in the
**top half** of the tape. A machine with space to spare walks there as often as
it likes, and the EXPSPACE build does; a machine on a clock can go there once
and never return, and it cannot lay a file of its own
either (`DescriptiveComplexity.Problems.Wide.Limits`).

This file adds a second problem – it changes nothing, and both existing
completeness theorems stand – whose channel writes the input of `x` at the
segment `x` cuts **among the elements the channel writes for**:

  `wmRegSeg x = {y | y ≤ x ∧ y carries an input symbol}`.

Two properties, and they are exactly the two a register file has to have.

* It is **monotone**: below a greater element the file has strictly more, and
  what it gains is greater than everything the two share, so the address grows
  (`wmSetLt_wmRegSeg`). The whole walk, mirror and increment layer is stated for
  a file whose registers grow with the elements they stand for, so it applies
  here unchanged – which is what the *singleton* channel `{x}` would not give:
  its cells shrink as the elements grow.
* It is **low**: every cell is supported on the elements that carry input, so
  it lies below `2 ^ t` with `t` their number (`wideRank_wmRegSeg_lt`). A
  reduction that gives input symbols to its argument elements alone therefore
  has its file inside the working region, where the segment channel's ruler is
  in the top half.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The cell of an element, at the register channel -/

section RegCell

variable {A : Type} [Language.wide.Structure A]

/-- **An element the channel writes for**: one that carries an input symbol.
These are the elements the file has registers for. -/
def WMHasInp (x : A) : Prop := ∃ a : A, WMInp x a

/-- **The cell of an element at the register channel**: the elements that carry
input, up to `x`. -/
def wmRegSeg (x : A) : A → Prop := fun y => WMLe y x ∧ WMHasInp y

/-- **Being the cell of an element at the register channel**, as the model reads
it off an address. -/
def WMRegSeg (s : A → Prop) (x : A) : Prop := ∀ y, s y ↔ (WMLe y x ∧ WMHasInp y)

theorem wmRegSeg_self (x : A) : WMRegSeg (wmRegSeg x) x := fun _ => Iff.rfl

/-- **An address is a cell exactly when it is that segment**, so `WMRegSeg`
never has to be unfolded again. -/
theorem wmRegSeg_iff_eq (s : A → Prop) (x : A) : WMRegSeg s x ↔ s = wmRegSeg x :=
  ⟨fun h => funext fun y => propext (h y), fun h y => by rw [h]; exact Iff.rfl⟩

/-- **The cell of an element the channel writes for is not empty**: the element
is in its own cell. -/
theorem wmRegSeg_nonempty (h : IsLinOrd (WMLe (A := A))) {x : A} (hx : WMHasInp x) :
    ∃ y, wmRegSeg x y := ⟨x, h.1 x, hx⟩

/-- **The cells grow with the elements**: what the greater cell gains is greater
than everything the two share, and the order on addresses weighs the least
element most. -/
theorem wmSetLt_wmRegSeg (h : IsLinOrd (WMLe (A := A))) [Finite A] {x y : A}
    (hlt : WMLt WMLe x y) (hy : WMHasInp y) :
    WMSetLt WMLe (wmRegSeg x) (wmRegSeg y) := by
  obtain ⟨z, ⟨hzy, hzx⟩, hmin⟩ := exists_least h
    (P := fun z => wmRegSeg y z ∧ ¬wmRegSeg x z) ⟨y, ⟨h.1 y, hy⟩, fun hc => hlt.2 hc.1⟩
  refine ⟨z, fun w hw => ?_, hzx, hzy⟩
  refine ⟨fun hwx => ⟨h.2.1 w x y hwx.1 hlt.1, hwx.2⟩, fun hwy => ?_⟩
  by_contra hwx
  exact hw.2 (hmin w ⟨hwy, hwx⟩)

/-- **Distinct elements the channel writes for have distinct cells.** -/
theorem wmRegSeg_injOn (h : IsLinOrd (WMLe (A := A))) [Finite A] {x y : A}
    (hx : WMHasInp x) (hy : WMHasInp y) (hxy : wmRegSeg x = wmRegSeg y) : x = y := by
  by_contra hne
  rcases h.2.2.2 x y with hle | hle
  · exact absurd hxy (fun hc =>
      ((wmSetLt_iff _ _).mp (wmSetLt_wmRegSeg h ⟨hle, fun hc' => hne (h.2.2.1 x y hle hc')⟩
        hy)).2 hc)
  · exact absurd hxy.symm (fun hc =>
      ((wmSetLt_iff _ _).mp (wmSetLt_wmRegSeg h
        ⟨hle, fun hc' => hne (h.2.2.1 x y hc' hle)⟩ hx)).2 hc)

/-- **Where a cell lies**: it is supported on the elements the channel writes
for, and – when those are upward closed, which is what a reduction arranges by
giving input to its greatest tags – so is every address below it. Its rank is
then below `2 ^` their number, which is what puts the file inside a clocked
program's working region. -/
theorem wideRank_wmRegSeg_lt [Finite A] (h : IsLinOrd (WMLe (A := A)))
    (hup : ∀ x y : A, WMLe x y → WMHasInp x → WMHasInp y) (x : A) :
    wideRank (wmRegSeg x) < 2 ^ Nat.card {y : A // WMHasInp y} := by
  refine wideRank_lt_two_pow_supported h (Q := fun y => WMHasInp y) ?_
  rintro t (hag | ⟨p, hbelow, hnp, hp⟩) y hty
  · exact ((hag y).mp hty).2
  · rcases em (y = p) with rfl | hne
    · exact absurd hty hnp
    · rcases h.2.2.2 y p with hyp | hpy
      · exact ((hbelow y ⟨hyp, fun hc => hne (h.2.2.1 y p hyp hc)⟩).mp hty).2
      · exact hup p y hpy hp.2

/-- **The working area lies below the file, at the register channel too** – but
for a different reason, and under a condition the reduction has to arrange. A
cell is the *down-set* of a marked element, so every cell holds the **least**
marked element `bot`, which is the most significant digit any of them has. An
address is therefore below every cell exactly when it stays strictly above
`bot`.

This is the geometry that decides where a reduction may put its marks. Marking
the argument elements alone would not do: a logical address is a set of argument
elements, so it would hold the least marked element itself and land *among* the
registers. Marking one further element **below** the argument tags fixes it: no
logical address reaches down to it, every cell does, and the file sits in a band
of its own directly above the working area – while staying inside `2 ^` the
number of marks, which is what
`DescriptiveComplexity.wideRank_wmRegSeg_lt` bounds. -/
theorem wmSetLt_wmRegSeg_of_above (h : IsLinOrd (WMLe (A := A))) {bot : A}
    (hbot : WMHasInp bot) (hleast : ∀ y, WMHasInp y → WMLe bot y)
    {r : A → Prop} (hr : ∀ y, r y → WMLt WMLe bot y) {x : A} (hx : WMHasInp x) :
    WMSetLt WMLe r (wmRegSeg x) := by
  refine ⟨bot, fun y hy => iff_of_false (fun hc => hy.2 (hr y hc).1)
      (fun hc => hy.2 (hleast y hc.2)), fun hc => ?_, ⟨hleast x hx, hbot⟩⟩
  exact (hr bot hc).2 (h.1 bot)

/-- **The bottom register is the marked element's own singleton**: the least
marked element cuts nothing below itself, so the file starts at the address that
holds it alone. -/
theorem wmRegSeg_least (h : IsLinOrd (WMLe (A := A))) {bot : A} (hbot : WMHasInp bot)
    (hleast : ∀ y, WMHasInp y → WMLe bot y) : wmRegSeg bot = fun y => y = bot :=
  funext fun y => propext ⟨fun hy => h.2.2.1 y bot hy.1 (hleast y hy.2),
    fun hy => by subst hy; exact ⟨h.1 y, hbot⟩⟩

end RegCell

/-! ### The file the channel hands over -/

section RegFile

variable {A : Type} [Language.wide.Structure A] [Finite A]

end RegFile

/-! ### The machine an instance describes, at the register channel -/

section Machine

variable {A : Type} [Language.wide.Structure A]

/-- The initial tape of the register channel: the cell of `x` holds the input
symbol of `x`. -/
def wpInpReg : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMRegSeg s x ∧ WMInp x y
  | _, _ => False

variable (A) in
/-- **The wide machine an instance describes, at the register channel**: the
machine of `DescriptiveComplexity.wideData` with its input written on the file
of the elements that carry input, instead of on the ruler of all the segments.
Every other field is the same one. -/
def wideRegData : TMData (WPoint A) :=
  { wideData A with Inp := wpInpReg }

@[simp]
theorem wideRegData_inp (x y : WPoint A) :
    (wideRegData A).Inp x y ↔ wpInpReg x y := Iff.rfl

end Machine

/-! ### Isomorphism-invariance -/

section Transport

variable {A B : Type} [Language.wide.Structure A] [Language.wide.Structure B]

/-- The cell of an element transports along an equivalence of instances. -/
theorem wmRegSeg_congr (e : A ≃[Language.wide] B) (s : A → Prop) (x : A) :
    WMRegSeg s x ↔ WMRegSeg (fun y => s (e.symm y)) (e x) := by
  have hle : ∀ x y : A, WMLe x y ↔ WMLe (e x) (e y) := fun x y => relMap_equiv₂ e wmLe x y
  have hinp : ∀ x y : A, WMInp x y ↔ WMInp (e x) (e y) := fun x y =>
    relMap_equiv₂ e wmInp x y
  have hhas : ∀ x : A, WMHasInp x ↔ WMHasInp (e x) := by
    intro x
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨e a, (hinp x a).mp ha⟩
    · rintro ⟨b, hb⟩
      refine ⟨e.symm b, (hinp x (e.symm b)).mpr ?_⟩
      have he : (e (e.symm b) : B) = b := e.toEquiv.apply_symm_apply b
      rw [he]
      exact hb
  constructor
  · intro h y
    change s (e.symm y) ↔ _
    rw [h (e.symm y), hle (e.symm y) x, hhas (e.symm y),
      show (e (e.symm y) : B) = y from e.toEquiv.apply_symm_apply y]
  · intro h y
    have hy : s (e.symm (e y)) ↔ (WMLe (e y) (e x) ∧ WMHasInp (e y)) := h (e y)
    rw [show (e.symm (e y) : A) = y from e.toEquiv.symm_apply_apply y] at hy
    rw [hy, ← hle y x, ← hhas y]

/-- **An isomorphism makes the two register-channel machines agree**: every
field but the channel is `DescriptiveComplexity.wideData_agree`'s, and the
channel transports because both what it compares and what it marks do. -/
theorem wideRegData_agree (e : A ≃[Language.wide] B) :
    TMData.Agree (wpointEquiv e) (wideRegData A) (wideRegData B) :=
  { wideData_agree e with
    inp := by
      have hinp : ∀ x y : A, WMInp x y ↔ WMInp (e.toEquiv x) (e.toEquiv y) := fun x y =>
        relMap_equiv₂ e wmInp x y
      rintro (s | x) <;> rintro (t | y) <;> try exact Iff.rfl
      constructor
      · rintro ⟨z, hd, hi⟩
        exact ⟨e.toEquiv z, (wmRegSeg_congr e s z).mp hd, (hinp z y).mp hi⟩
      · rintro ⟨z, hd, hi⟩
        refine ⟨e.toEquiv.symm z, ?_, (hinp _ y).mpr ?_⟩
        · rw [wmRegSeg_congr e s (e.toEquiv.symm z),
            show (e (e.toEquiv.symm z) : B) = z from e.toEquiv.apply_symm_apply z]
          exact hd
        · rw [show (e.toEquiv (e.toEquiv.symm z) : B) = z from
            e.toEquiv.apply_symm_apply z]
          exact hi }

end Transport

/-! ### The problems -/

section Problem

/-- **Wide machine acceptance at the register channel**: the question
`DescriptiveComplexity.WideAccept` asks, of the machine whose input is written
on the file of the elements that carry it. The clock is the same, the universe
is the same, and what a reduction gains is a file it can reach. -/
def WideRegAccept : DecisionProblem Language.wide where
  Holds := fun A _ => (wideRegData A).WellFormed ∧ (wideRegData A).Accepts
  iso_invariant := fun {A B} _ _ e => by
    have h := wideRegData_agree e
    exact and_congr h.wellFormed h.accepts

/-- **Wide machine acceptance at the register channel, in bounded space.** -/
def WideRegAcceptSpace : DecisionProblem Language.wide where
  Holds := fun A _ => (wideRegData A).WellFormed ∧ (wideRegData A).AcceptsSpace
  iso_invariant := fun {A B} _ _ e => by
    have h := wideRegData_agree e
    exact and_congr h.wellFormed h.acceptsSpace

end Problem

end DescriptiveComplexity
