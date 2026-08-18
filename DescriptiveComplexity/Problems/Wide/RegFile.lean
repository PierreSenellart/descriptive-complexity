/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Tape

/-!
# What a register file has to be

A wide machine cannot read the digits of the address it is on, so every program
for one keeps a **register file**: one recognizable cell per element of the
instance, holding one bit of a track. The walks, the tests and the mirror ask
four things of that file and nothing else:

> stand on the cell of `u`, write there, move to the cell of the next element,
> recognize the two ends.

This file says what a family of cells has to satisfy for those four to work, and
the answer is short: it has to be **strictly monotone**, and no register may be
the empty address.

The index is arbitrary. A space-bounded program's file has one register per
element and that is what `DescriptiveComplexity.RegFile` names, but a program
that has to *lay its file out* on a clock cannot afford that index – a rule sees
the control and the cell under the head and nothing else, so the only addresses
it can locate are a fixed number of tuple roll-overs from where it starts, and
the elements are more. `DescriptiveComplexity.IxFile` is therefore the interface
at an arbitrary ordered index, and `DescriptiveComplexity.RegFile` is its
diagonal case (`DescriptiveComplexity.RegFile.toIx`), every elementwise
statement below being the general one read there. Two linear orders are in play
in the general form and only one at the diagonal: that of the **addresses**,
over which the cells are compared, and that of the **index**, in which the
registers are laid out.

* Monotonicity gives injectivity (`DescriptiveComplexity.RegFile.injective`) and
  the converse comparison (`DescriptiveComplexity.RegFile.lt_iff`), so the file is
  ordered exactly like the instance and a walk recovers the order and nothing
  else. It also gives the fact that turns a move between consecutive registers
  into a single scan: **nothing is a register between two consecutive ones**
  (`DescriptiveComplexity.RegFile.gap`), so the scan cannot overshoot or stop
  early.
* Nonemptiness of a cell (`DescriptiveComplexity.RegFile.cell_nonempty`) is what
  lets the head step *below* the first register, which is where a downward pass
  ends.

Two files satisfy this. The one a space-bounded program uses is the ladder the
input channel marks – `DescriptiveComplexity.wmSegFile`, whose cell for `x` is the
initial segment `{y | y ≤ x}` – and it is free, being in the instance before any
transition is written. It is also, as `DescriptiveComplexity.Problems.Wide.Marks`
explains, a geometric ruler lying in the top half of the tape, which a clocked
program cannot afford to walk twice. A clocked program therefore builds its own
file low on the tape and instantiates the same walks at it: that is what this
interface is for, and why the walks above it name a `DescriptiveComplexity.RegFile`
rather than `DescriptiveComplexity.wmSeg`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Registers

variable {A : Type} [Language.wide.Structure A]

/-! ### An ordered index, its successors and its ranks

Everything a register walk asks of a file is about the order its cells are laid
out in, and nothing about *what* indexes them. The index of the file a
space-bounded program uses is the instance itself, which is why the elementwise
names below read as “per element”; a program that has to lay its file out on a
clock cannot afford that index, so the general form comes first and the
elementwise one is its diagonal. -/

section Ix

variable {I : Type} (ile : I → I → Prop)

/-- **The successor in an index's order**: the least index strictly above one.
The pointer of a register walk steps by this, in the control, while the head
scans from one register to the next. -/
def IxSucc (u u' : I) : Prop := WMLt ile u u' ∧ ∀ v : I, WMLt ile u v → ile u' v

/-- **Every index but the greatest has a successor.** -/
theorem exists_ixSucc [Finite I] (h : IsLinOrd ile) {u : I} (hne : ∃ v : I, WMLt ile u v) :
    ∃ u', IxSucc ile u u' := by
  obtain ⟨u', hu', hmin⟩ := exists_least h hne
  exact ⟨u', hu', hmin⟩

/-- **The rank of an index**: the number of indices strictly below it, which is
how many registers a walk has already crossed when its pointer reaches it. Every
budget of a register walk is a difference of two of these, exactly as every
budget of an address sweep is a difference of two
`DescriptiveComplexity.wideRank`s. -/
noncomputable def ixRank (u : I) : ℕ := bitRank ile (fun _ => True) u

section IxRank

variable [Finite I]

/-- Rank increases strictly along the order. -/
theorem ixRank_lt (h : IsLinOrd ile) {u u' : I} (hlt : WMLt ile u u') :
    ixRank ile u < ixRank ile u' :=
  bitRank_lt h trivial hlt.1 fun hc => hlt.2 (hc ▸ h.1 u)

/-- Rank is monotone along the order. -/
theorem ixRank_le_of_le (h : IsLinOrd ile) {u u' : I} (hle : ile u u') :
    ixRank ile u ≤ ixRank ile u' := by
  rcases eq_or_ne u u' with rfl | hne
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (ixRank_lt ile h ⟨hle, fun hc => hne (h.2.2.1 u u' hle hc)⟩)

/-- **The rank of an index is below the number of indices**, so a walk of the
file crosses fewer registers than there are of them. -/
theorem ixRank_lt_card (u : I) : ixRank ile u < Nat.card I := by
  have h := bitRank_lt_card (Le := ile) (Posn := fun _ => True) (p := u) trivial
  rwa [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ : I => trivial)] at h

/-- **Rank increases by exactly one along a successor**, which is what makes a
difference of ranks a count of registers. -/
theorem ixRank_succ (h : IsLinOrd ile) {u u' : I} (hs : IxSucc ile u u') :
    ixRank ile u' = ixRank ile u + 1 := by
  refine bitRank_succPos h ⟨trivial, trivial, hs.1.1, fun hc => hs.1.2 (hc ▸ h.1 u), ?_⟩
  intro r _ hur hru
  rcases eq_or_ne r u with rfl | hne
  · exact Or.inl rfl
  · exact Or.inr (h.2.2.1 r u' hru
      (hs.2 r ⟨hur, fun hc => hne (h.2.2.1 r u hc hur)⟩))

end IxRank

end Ix

/-! ### The successor of an element -/

variable (A) in
/-- **The successor of an element in the instance's order**: the least element
strictly above it, i.e., `DescriptiveComplexity.IxSucc` at the diagonal index. -/
def WMSucc (u u' : A) : Prop := IxSucc (WMLe (A := A)) u u'

variable [Finite A]

/-! ### The rank of an element -/

/-- **The rank of an element**: the number of elements strictly below it. -/
noncomputable def wmRank (u : A) : ℕ := ixRank (WMLe (A := A)) u

omit [Finite A] in
/-- The rank of an element is the general rank at the diagonal index. -/
@[simp]
theorem wmRank_eq_ixRank (u : A) : wmRank u = ixRank (WMLe (A := A)) u := rfl

/-- Rank increases strictly along the order. -/
theorem wmRank_lt (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hlt : WMLt WMLe u u') :
    wmRank u < wmRank u' :=
  ixRank_lt _ h hlt

/-- **The rank of an element is below the number of elements**, so a walk of the
file crosses fewer registers than there are elements. -/
theorem wmRank_lt_card (u : A) : wmRank u < Nat.card A :=
  ixRank_lt_card _ u

/-! ### The interface, at an arbitrary index

A file is a family of addresses indexed by something ordered, and the four
things a walk asks of it are about that order alone. The index of the file a
space-bounded program uses is the instance itself, which is why the interface
below reads as “one cell per element”; a program that has to *lay its file out*
on a clock cannot afford that index – it can only locate a fixed number of tuple
roll-overs from where it starts, and the elements are more – so the interface is
stated at an arbitrary ordered index and the elementwise one is its diagonal
case.

Two linear orders are in play and they are not the same: the one of the
**addresses** (`DescriptiveComplexity.WMLe`, over which the cells are compared)
and the one of the **index** (which says in what order the registers are laid
out). At the diagonal they coincide, which is why the elementwise statements
below take one hypothesis where the general ones take two. -/

section IxI

variable {I : Type} (ile : I → I → Prop)

variable (A I) in
/-- **A register file over an index**: one cell per index, ordered like the
index, none of them the empty address.

Strict monotonicity is the whole of the interface. Everything a walk needs
follows from it: the cells are distinct, they are comparable exactly as their
indices are, and consecutive indices have no register between them, so one scan
carries the head from each register to the next. -/
structure IxFile where
  /-- The address of the register of an index. -/
  cell : I → (A → Prop)
  /-- The registers are ordered like the indices that name them. -/
  strictMono : ∀ u v : I, WMLt ile u v → WMSetLt WMLe (cell u) (cell v)
  /-- No register is the empty address, so the head can always step below one. -/
  cell_nonempty : ∀ u : I, ∃ x : A, cell u x

namespace IxFile

variable {ile} (F : IxFile A I ile)

/-- **The registers are ordered *exactly* like the indices**, so a program
reading its file recovers that order and nothing else. -/
theorem lt_iff (h : IsLinOrd ile) (u v : I)
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) :
    WMSetLt WMLe (F.cell u) (F.cell v) ↔ WMLt ile u v := by
  refine ⟨fun hlt => ?_, F.strictMono u v⟩
  have hlin := isLinOrd_wmSetLe ha
  by_contra hc
  rcases h.2.2.2 v u with hvu | huv
  · rcases eq_or_ne v u with rfl | hne
    · exact ((wmSetLt_iff _ _).mp hlt).2 rfl
    · exact ((wmSetLt_iff _ _).mp hlt).2 (hlin.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt).1
        ((wmSetLt_iff _ _).mp
          (F.strictMono v u ⟨hvu, fun hcon => hne (h.2.2.1 v u hvu hcon)⟩)).1)
  · exact hc ⟨huv, fun hcon =>
      ((wmSetLt_iff _ _).mp hlt).2 (congrArg F.cell (h.2.2.1 u v huv hcon))⟩

omit [Finite A] in
/-- **Distinct indices have distinct registers.** -/
theorem injective (h : IsLinOrd ile) : Function.Injective F.cell := by
  intro u v he
  rcases eq_or_ne u v with rfl | hne
  · rfl
  · exfalso
    rcases h.2.2.2 u v with hle | hle
    · exact ((wmSetLt_iff _ _).mp
        (F.strictMono u v ⟨hle, fun hc => hne (h.2.2.1 u v hle hc)⟩)).2 he
    · exact ((wmSetLt_iff _ _).mp
        (F.strictMono v u ⟨hle, fun hc => hne (h.2.2.1 u v hc hle)⟩)).2 he.symm

/-- **Consecutive indices have consecutive registers**: no address strictly
between the register of an index and the register of its successor is a
register. -/
theorem gap (h : IsLinOrd ile) {u u' : I}
    (hs : IxSucc ile u u') {r : A → Prop} (h1 : WMSetLt WMLe (F.cell u) r)
    (h2 : WMSetLt WMLe r (F.cell u')) (x : I)
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) : r ≠ F.cell x := by
  rintro rfl
  exact ((F.lt_iff h x u').mp h2).2 (hs.2 x ((F.lt_iff h u x).mp h1))

/-- **The empty address is below every register**, no register being empty. -/
theorem wmSetLt_empty_cell (u : I) (ha : IsLinOrd (WMLe (A := A)) := by assumption) :
    WMSetLt WMLe (fun _ => False) (F.cell u) := by
  obtain ⟨x, hx⟩ := F.cell_nonempty u
  refine (wmSetLt_iff _ _).mpr ⟨wmSetLe_of_empty ha (fun _ hc => hc) _, fun hc => ?_⟩
  rw [← hc] at hx
  exact hx

/-- **The registers are ordered like the indices non-strictly too.** -/
theorem cell_le (h : IsLinOrd ile) {u v : I} (hle : ile u v)
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) :
    WMSetLe WMLe (F.cell u) (F.cell v) := by
  rcases eq_or_ne u v with rfl | hne
  · exact (isLinOrd_wmSetLe ha).1 _
  · exact ((wmSetLt_iff _ _).mp
      (F.strictMono u v ⟨hle, fun hc => hne (h.2.2.1 u v hle hc)⟩)).1

/-- **Nothing below the least register is a register**, in existential form. -/
theorem not_exists_cell_of_lt_bot (h : IsLinOrd ile) {gbot : I}
    (hbot : ∀ y : I, ile gbot y) {s : A → Prop} (hs : WMSetLt WMLe s (F.cell gbot))
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) :
    ¬∃ u : I, s = F.cell u := fun hc => ((F.lt_iff h hc.choose gbot).mp
  (hc.choose_spec ▸ hs)).2 (hbot hc.choose)

/-- **Anything below the file is below its top register.** -/
theorem le_cell_top_of_le (h : IsLinOrd ile) {gtop gbot : I}
    (hbot : ∀ y : I, ile gbot y) {s : A → Prop}
    (hs : WMSetLe WMLe s (F.cell gbot))
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) : WMSetLe WMLe s (F.cell gtop) :=
  (isLinOrd_wmSetLe ha).2.1 _ _ _ hs (F.cell_le h (hbot gtop))

theorem le_cell_top (h : IsLinOrd ile) {gtop gbot : I}
    (hbot : ∀ y : I, ile gbot y) {s : A → Prop}
    (hs : WMSetLt WMLe s (F.cell gbot))
    (ha : IsLinOrd (WMLe (A := A)) := by assumption) : WMSetLe WMLe s (F.cell gtop) :=
  F.le_cell_top_of_le h hbot ((wmSetLt_iff _ _).mp hs).1

/-- **Nothing strictly below the least register is a register.** -/
theorem ne_cell_of_lt_cell (h : IsLinOrd ile) {gbot : I}
    (hbot : ∀ y : I, ile gbot y) {r : A → Prop} (hlt : WMSetLt WMLe r (F.cell gbot))
    (u : I) (ha : IsLinOrd (WMLe (A := A)) := by assumption) : r ≠ F.cell u := by
  rintro rfl
  exact ((F.lt_iff h u gbot).mp hlt).2 (hbot u)

omit [Finite A] in
/-- **A register below another is not the whole tape.** -/
theorem exists_not_cell {u v : I} (hlt : WMLt ile u v) : ∃ x : A, ¬F.cell u x := by
  obtain ⟨x, -, hx, -⟩ := F.strictMono u v hlt
  exact ⟨x, hx⟩

end IxFile

end IxI

/-! ### The interface -/

variable (A) in
/-- **A register file**: one cell per element, ordered like the elements, none of
them the empty address.

Strict monotonicity is the whole of the interface. Everything a walk needs
follows from it: the cells are distinct, they are comparable exactly as their
elements are, and consecutive elements have no register between them, so one
scan carries the head from each register to the next. -/
structure RegFile where
  /-- The address of the register of an element. -/
  cell : A → (A → Prop)
  /-- The registers are ordered like the elements that name them. -/
  strictMono : ∀ u v : A, WMLt WMLe u v → WMSetLt WMLe (cell u) (cell v)
  /-- No register is the empty address, so the head can always step below one. -/
  cell_nonempty : ∀ u : A, ∃ x : A, cell u x

namespace RegFile

variable (F : RegFile A)

/-- **The elementwise file is the general one at its diagonal**: index the
instance, ordered by the instance's own order. Every statement below is its
general form read there, the two linear orders having become one. -/
@[reducible] def toIx : IxFile A A (WMLe (A := A)) :=
  ⟨F.cell, F.strictMono, F.cell_nonempty⟩

omit [Finite A] in
@[simp]
theorem cell_toIx : F.toIx.cell = F.cell := rfl

/-- **The registers are ordered *exactly* like the elements**, so a program
reading its file recovers the order of the instance and nothing else. The
direction this adds to the interface is the one that matters: a register below
another comes from an element below the other's. -/
theorem lt_iff (h : IsLinOrd (WMLe (A := A))) (u v : A) :
    WMSetLt WMLe (F.cell u) (F.cell v) ↔ WMLt WMLe u v :=
  F.toIx.lt_iff h u v

omit [Finite A] in
/-- **Distinct elements have distinct registers.** This is about the *addresses*;
it says nothing about the symbols in them, which in a file marked by the input
channel cannot all be distinct. -/
theorem injective (h : IsLinOrd (WMLe (A := A))) : Function.Injective F.cell :=
  F.toIx.injective h

/-- **Consecutive elements have consecutive registers**: no address strictly
between the register of an element and the register of its successor is a
register. That is what makes a move between two registers one scan – the machine
cannot overshoot, and nothing it passes can be mistaken for a register. -/
theorem gap (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u') {r : A → Prop}
    (h1 : WMSetLt WMLe (F.cell u) r) (h2 : WMSetLt WMLe r (F.cell u')) (x : A) :
    r ≠ F.cell x :=
  F.toIx.gap h hs h1 h2 x

/-- **The empty address is below every register**, no register being empty: the
head starts below its file, wherever the file sits. -/
theorem wmSetLt_empty_cell (h : IsLinOrd (WMLe (A := A))) (u : A) :
    WMSetLt WMLe (fun _ => False) (F.cell u) :=
  F.toIx.wmSetLt_empty_cell u

/-- **The registers are ordered like the elements non-strictly too**: what a walk
between two named registers is bounded by. -/
theorem cell_le (h : IsLinOrd (WMLe (A := A))) {u v : A} (hle : WMLe u v) :
    WMSetLe WMLe (F.cell u) (F.cell v) :=
  F.toIx.cell_le h hle

/-- **Nothing below the least register is a register**, in existential form: the
shape a walk's junk-address side condition takes. -/
theorem not_exists_cell_of_lt_bot (h : IsLinOrd (WMLe (A := A))) {gbot : A}
    (hbot : ∀ y : A, WMLe gbot y) {s : A → Prop} (hs : WMSetLt WMLe s (F.cell gbot)) :
    ¬∃ u : A, s = F.cell u :=
  F.toIx.not_exists_cell_of_lt_bot h hbot hs

/-- **Anything below the file is below its top register**: what a walk up to the
file needs of where it starts. At the input channel's ladder the top register is
the whole tape and the bound is free; at a file a program builds it is not, and
this is how a caller supplies it. -/
theorem le_cell_top_of_le (h : IsLinOrd (WMLe (A := A))) {gtop gbot : A}
    (hbot : ∀ y : A, WMLe gbot y) {s : A → Prop}
    (hs : WMSetLe WMLe s (F.cell gbot)) : WMSetLe WMLe s (F.cell gtop) :=
  F.toIx.le_cell_top_of_le h hbot hs

theorem le_cell_top (h : IsLinOrd (WMLe (A := A))) {gtop gbot : A}
    (hbot : ∀ y : A, WMLe gbot y) {s : A → Prop}
    (hs : WMSetLt WMLe s (F.cell gbot)) : WMSetLe WMLe s (F.cell gtop) :=
  F.toIx.le_cell_top h hbot hs

/-- **Nothing strictly below the least register is a register**, so a program
working under its file can never mistake its own data for one. -/
theorem ne_cell_of_lt_cell (h : IsLinOrd (WMLe (A := A))) {gbot : A}
    (hbot : ∀ y : A, WMLe gbot y) {r : A → Prop} (hlt : WMSetLt WMLe r (F.cell gbot))
    (u : A) : r ≠ F.cell u :=
  F.toIx.ne_cell_of_lt_cell h hbot hlt u

omit [Finite A] in
/-- **A register below another is not the whole tape**, so the head standing on it
can step up. -/
theorem exists_not_cell {u v : A} (hlt : WMLt WMLe u v) : ∃ x : A, ¬F.cell u x :=
  F.toIx.exists_not_cell hlt

end RegFile

/-! ### Where a file sits relative to the data

A walk asks nothing of *where* the file is, but a program does: it needs to know
that what it writes in its working area cannot land on a register. For the file
the input channel marks that is a fact about the layout – every marked cell holds
the least element, and the addresses that do not are the working area – and a
program that builds its own file has to arrange the same thing by choosing where
to put it. Either way it is one condition, so it is asked for once. -/

variable (A) in
/-- **A register file, and the addresses a program works in**: every working
address lies strictly below every register, so the program's data and its
registers cannot collide. -/
structure SitedFile extends RegFile A where
  /-- The addresses the program computes with. -/
  Work : (A → Prop) → Prop
  /-- They all lie below the file. -/
  work_lt_cell : ∀ {r : A → Prop}, Work r → ∀ u : A, WMSetLt WMLe r (toRegFile.cell u)

/-! ### The file the input channel marks

The register file a space-bounded program gets for free: the cell of `x` is the
initial segment `x` cuts, which is where the vocabulary's input channel writes.
The facts of `DescriptiveComplexity.Problems.Wide.Marks` are exactly the two
fields. -/

/-- **The register file of the input channel.**

Reducible: a program written at an arbitrary file is read at this one by
unification, and `rw` matches at `instances` transparency, so the projection
`(wmSegFile h).cell` has to reduce to `DescriptiveComplexity.wmSeg` there. -/
@[reducible] def wmSegFile (h : IsLinOrd (WMLe (A := A))) : RegFile A where
  cell := wmSeg
  strictMono := fun _ _ hlt => wmSetLt_wmSeg h hlt
  cell_nonempty := fun u => ⟨u, wmSeg_self h u⟩

@[simp]
theorem cell_wmSegFile (h : IsLinOrd (WMLe (A := A))) : (wmSegFile h).cell = wmSeg (A := A) :=
  rfl

end Registers

end DescriptiveComplexity
