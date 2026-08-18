/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpTracks
import DescriptiveComplexity.Problems.Wide.Walk

/-!
# A program, written rule by rule

`DescriptiveComplexity.Pfp.Table` is a transition table stated the way a
*finished* table wants to be stated: every attribute a function of the rule and
of the rule's data, with the data a bare tuple. That presentation is wrong for
*writing* a program, where one wants to say

> in this phase, standing on a symbol whose tracks are `g`, with the pointer `f`
> in the control: go to that phase, write these tracks, and move left.

This file is that presentation, and the translation into a table.

## The data of a rule is a state and a symbol

The one decision the layer rests on. A transition's data must carry **both**
payloads – the state's and the symbol's – because neither determines the other:
the symbol under the head cannot name the register the head is on (the registers
are anonymous, `DescriptiveComplexity.Problems.Wide.Marks`), and the state cannot
name the symbol it is about to read. So the slots of a rule's data are
`Q ⊕ W`: the **control slots** `Q`, which a state uses and a symbol leaves at the
designated element, and the **track slots** `W`, the other way round
(`DescriptiveComplexity.Pfp.stVec`, `DescriptiveComplexity.Pfp.syVec`).

Two things fall out of that, and they are the point of the file.

* **Firing a rule needs no equations.** The data of the rule that fires is
  `Sum.elim f g` – the pointer and the tracks side by side – so
  `DescriptiveComplexity.Pfp.Prog.fire_left` and its rightward twin hand a program
  its six attributes at the elements it named, with no payload arithmetic
  anywhere.
* **Determinism reduces to a statement about rules.** The state and the symbol
  occupy *disjoint* coordinates, so a transition's data is recovered from the two
  of them; `DescriptiveComplexity.Pfp.Table.Sep` therefore reduces to
  `DescriptiveComplexity.Pfp.Prog.sep_of`: two rules that fire on the same symbol
  from the same state must be the same rule. That is a check on pairs of rule
  families, which is what a program can actually carry out.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### Control slots and track slots -/

section Vectors

variable {A Q W : Type}

/-- **The data a state occupies**: its own slots, the designated element in the
track slots. -/
def stVec (zero : A) (f : Q → A) : Q ⊕ W → A := Sum.elim f fun _ => zero

/-- **The data a symbol occupies**: the track slots, the designated element in the
control slots. -/
def syVec (zero : A) (g : W → A) : Q ⊕ W → A := Sum.elim (fun _ => zero) g

variable {zero : A}

@[simp]
theorem stVec_inl (f : Q → A) (q : Q) : stVec (W := W) zero f (Sum.inl q) = f q := rfl

@[simp]
theorem syVec_inr (g : W → A) (s : W) : syVec (Q := Q) zero g (Sum.inr s) = g s := rfl

theorem stVec_injective : Function.Injective (stVec (W := W) (Q := Q) zero) :=
  fun _f _g h => funext fun q => congrFun h (Sum.inl q)

theorem syVec_injective : Function.Injective (syVec (W := W) (Q := Q) zero) :=
  fun _f _g h => funext fun s => congrFun h (Sum.inr s)

variable [Fintype Q] [Fintype W]

/-- The payload of a state. -/
noncomputable def stPl (zero : A) (f : Q → A) : Fin (Fintype.card (Q ⊕ W)) → A :=
  slotPl (stVec zero f)

/-- The payload of a symbol. -/
noncomputable def syPl (zero : A) (g : W → A) : Fin (Fintype.card (Q ⊕ W)) → A :=
  slotPl (syVec zero g)

theorem stPl_injective : Function.Injective (stPl (W := W) (Q := Q) zero) :=
  fun f g h => stVec_injective
    (slotPl_injective (show slotPl (stVec zero f) = slotPl (stVec (W := W) zero g) from h))

theorem syPl_injective : Function.Injective (syPl (W := W) (Q := Q) zero) :=
  fun f g h => syVec_injective
    (slotPl_injective (show slotPl (syVec zero f) = slotPl (syVec (Q := Q) zero g) from h))

end Vectors

/-! ### Rules -/

/-- **One rule of a program**: what it applies to, where it goes, what it writes
and which way it moves. The guard sees the pointer and the tracks separately, and
so do the two things the rule computes. -/
structure Rule (A Q W P : Type) where
  /-- When the rule applies: at this pointer, reading these tracks. -/
  guard : (Q → A) → (W → A) → Prop
  /-- The phase the rule applies in. -/
  srcPh : P
  /-- The phase the rule moves to. -/
  dstPh : P
  /-- The pointer the rule leaves in the control. -/
  dstSt : (Q → A) → (W → A) → (Q → A)
  /-- The tracks the rule writes. -/
  wr : (Q → A) → (W → A) → (W → A)
  /-- Whether the rule moves the head right. -/
  moveRight : Prop

/-- **A program**: the two designated elements, a rule for each rule name, and the
machine's constants – where it starts, which states accept, what the blank is, and
the mark each element's register cell holds at time zero. -/
structure Prog (A R P Q W K : Type) (dd : ℕ) [Fintype Q] [Fintype W] where
  /-- The designated element a track holds when its bit is clear. -/
  zero : A
  /-- The designated element a track holds when its bit is set. -/
  one : A
  /-- The two designated elements differ. -/
  zero_ne_one : zero ≠ one
  /-- The slots fit in the tuples of the universe. -/
  payload_le : Fintype.card (Q ⊕ W) ≤ dd
  /-- The rules. -/
  rules : R → Rule A Q W P
  /-- The phase the machine starts in. -/
  startPh : P
  /-- The pointer the machine starts with. -/
  startSt : Q → A
  /-- Which states accept. -/
  accept : P → (Q → A) → Prop
  /-- The tracks of the blank. -/
  blank : W → A
  /-- The tracks of the mark in the cell of an element. -/
  mark : Univ A R P K dd → W → A
  /-- **Which elements the channel writes for.** Every one of them by default –
  the channel of `DescriptiveComplexity.WideAccept` writes for all – and a
  program emitted into the *register* channel of
  `DescriptiveComplexity.WideRegAccept` restricts it, the elements it leaves out
  having no register in the file it is handed. -/
  marked : Univ A R P K dd → Prop := fun _ => True

namespace Prog

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W]
variable (PR : Prog A R P Q W K dd)

/-- **A state of the program**, as an element of the emitted universe. -/
noncomputable def stElt (p : P) (f : Q → A) : Univ A R P K dd :=
  stateElt PR.zero p (stPl (W := W) PR.zero f)

/-- **A symbol of the program**, as an element of the emitted universe. -/
noncomputable def syElt (g : W → A) : Univ A R P K dd :=
  symElt PR.zero (syPl (Q := Q) PR.zero g)

/-- **The table a program is.** Every attribute is read off the rule of the tag
and the two halves of the data. -/
noncomputable def table : Table A R P K (Fintype.card (Q ⊕ W)) dd where
  zero := PR.zero
  one := PR.one
  zero_ne_one := PR.zero_ne_one
  payload_le := PR.payload_le
  guard r w := (PR.rules r).guard (fun q => unslot w (Sum.inl q)) fun s => unslot w (Sum.inr s)
  srcPh r := (PR.rules r).srcPh
  dstPh r := (PR.rules r).dstPh
  srcPl _r w := stPl (W := W) PR.zero fun q => unslot w (Sum.inl q)
  dstPl r w := stPl (W := W) PR.zero ((PR.rules r).dstSt (fun q => unslot w (Sum.inl q))
    fun s => unslot w (Sum.inr s))
  readPl _r w := syPl (Q := Q) PR.zero fun s => unslot w (Sum.inr s)
  writePl r w := syPl (Q := Q) PR.zero ((PR.rules r).wr (fun q => unslot w (Sum.inl q))
    fun s => unslot w (Sum.inr s))
  moveRight r := (PR.rules r).moveRight
  startPh := PR.startPh
  startPl := stPl (W := W) PR.zero PR.startSt
  accept p v := PR.accept p fun q => unslot v (Sum.inl q)
  blankPl := syPl (Q := Q) PR.zero PR.blank
  markPl x := syPl (Q := Q) PR.zero (PR.mark x)
  Marked := PR.marked

/-! ### Firing a rule

The data of the rule that fires is the pointer and the tracks side by side, so
each of the table's six attributes is what the rule says at the elements the
program named. -/

variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
private theorem data_inl (f : Q → A) (g : W → A) (q : Q) :
    unslot (slotPl (Sum.elim f g)) (Sum.inl q) = f q := by
  rw [unslot_slotPl]
  rfl

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
private theorem data_inr (f : Q → A) (g : W → A) (s : W) :
    unslot (slotPl (Sum.elim f g)) (Sum.inr s) = g s := by
  rw [unslot_slotPl]
  rfl

/-- **A rule fires, moving left**: the shape every subroutine of the address layer
asks for, at the state and the symbol the rule names. -/
theorem fire_left (hR : PR.table.Reads) (r : R) (f : Q → A) (g : W → A)
    (hg : (PR.rules r).guard f g) (hd : ¬(PR.rules r).moveRight) :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ (PR.stElt (PR.rules r).srcPh f) ∧
      WMRead τ (PR.syElt g) ∧
      WMDst τ (PR.stElt (PR.rules r).dstPh ((PR.rules r).dstSt f g)) ∧
      WMWrite τ (PR.syElt ((PR.rules r).wr f g)) ∧ ¬WMRight τ := by
  have hf : (fun q => unslot (slotPl (Sum.elim f g)) (Sum.inl q)) = f :=
    funext fun q => data_inl f g q
  have hs : (fun s => unslot (slotPl (Sum.elim f g)) (Sum.inr s)) = g :=
    funext fun s => data_inr f g s
  refine PR.table.fire_left hR (w := slotPl (Sum.elim f g)) ?_ hd ?_ ?_ ?_ ?_
  · change (PR.rules r).guard _ _
    rw [hf, hs]
    exact hg
  · simp only [table, stElt, hf]
  · simp only [table, syElt, hs]
  · simp only [table, stElt, hf, hs]
  · simp only [table, syElt, hf, hs]

/-- **A rule fires, moving right.** -/
theorem fire_right (hR : PR.table.Reads) (r : R) (f : Q → A) (g : W → A)
    (hg : (PR.rules r).guard f g) (hd : (PR.rules r).moveRight) :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ (PR.stElt (PR.rules r).srcPh f) ∧
      WMRead τ (PR.syElt g) ∧
      WMDst τ (PR.stElt (PR.rules r).dstPh ((PR.rules r).dstSt f g)) ∧
      WMWrite τ (PR.syElt ((PR.rules r).wr f g)) ∧ WMRight τ := by
  have hf : (fun q => unslot (slotPl (Sum.elim f g)) (Sum.inl q)) = f :=
    funext fun q => data_inl f g q
  have hs : (fun s => unslot (slotPl (Sum.elim f g)) (Sum.inr s)) = g :=
    funext fun s => data_inr f g s
  refine PR.table.fire_right hR (w := slotPl (Sum.elim f g)) ?_ hd ?_ ?_ ?_ ?_
  · change (PR.rules r).guard _ _
    rw [hf, hs]
    exact hg
  · simp only [table, stElt, hf]
  · simp only [table, syElt, hs]
  · simp only [table, stElt, hf, hs]
  · simp only [table, syElt, hf, hs]

/-! ### Determinism, as a check on pairs of rules -/

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
/-- **The separation condition of a program**: two rules that fire in the same
phase, at the same pointer, reading the same tracks, are the same rule. The
control slots and the track slots being disjoint is what turns
`DescriptiveComplexity.Pfp.Table.Sep` into this – a check a program can carry out
rule family by rule family, with no payload in sight. -/
theorem sep_of (h : ∀ (r r' : R) (f : Q → A) (g : W → A), (PR.rules r).guard f g →
    (PR.rules r').guard f g → (PR.rules r).srcPh = (PR.rules r').srcPh → r = r') :
    PR.table.Sep := by
  intro r r' w w' hg hg' hph hst hread
  have hf : (fun q => unslot w (Sum.inl q)) = fun q => unslot w' (Sum.inl q) :=
    stPl_injective hst
  have hs : (fun s => unslot w (Sum.inr s)) = fun s => unslot w' (Sum.inr s) :=
    syPl_injective hread
  have hww : w = w' := by
    rw [← slotPl_unslot w, ← slotPl_unslot w']
    refine congrArg slotPl (funext fun d => ?_)
    match d with
    | Sum.inl q => exact congrFun hf q
    | Sum.inr s => exact congrFun hs s
  subst hww
  exact ⟨h r r' _ _ hg hg' hph, rfl⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
/-- **Separation at some phases only**, the same reading of a rule set at a
program that guesses: the two halves of the data are recovered from the
injections exactly as above, and the phase restriction is carried through
untouched. -/
theorem sepOn_of {Ph : P → Prop}
    (h : ∀ (r r' : R) (f : Q → A) (g : W → A), Ph (PR.rules r).srcPh →
      (PR.rules r).guard f g → (PR.rules r').guard f g →
      (PR.rules r).srcPh = (PR.rules r').srcPh → r = r') :
    PR.table.SepOn Ph := by
  intro r r' w w' hph0 hg hg' hph hst hread
  have hf : (fun q => unslot w (Sum.inl q)) = fun q => unslot w' (Sum.inl q) :=
    stPl_injective hst
  have hs : (fun s => unslot w (Sum.inr s)) = fun s => unslot w' (Sum.inr s) :=
    syPl_injective hread
  have hww : w = w' := by
    rw [← slotPl_unslot w, ← slotPl_unslot w']
    refine congrArg slotPl (funext fun d => ?_)
    match d with
    | Sum.inl q => exact congrFun hf q
    | Sum.inr s => exact congrFun hs s
  subst hww
  exact ⟨h r r' _ _ hph0 hg hg' hph, rfl⟩

/-! ### The tape of a register pass

The tape all three passes of `DescriptiveComplexity.Problems.Wide.Mirror` and
`DescriptiveComplexity.Problems.Wide.Test` run over: at the slot being walked
the symbol carries the digit of the track there as a bit
(`DescriptiveComplexity.regBit`, set only at the register cells); every other
slot holds whatever **element** the program keeps at that cell – the marks of
the register file carry elements, not bits – and rides along untouched. -/

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **The tape a program presents while it walks a track**, over an arbitrary
register file. The walked slot holds the track's digit as a bit; the background
is **element-valued**, so it can carry the name marks of a file whose cells are
recognized by an element rather than by a bit.

The file enters as its *cells* and not as a `DescriptiveComplexity.RegFile`,
since a tape is a definition and a file carries proofs; the proofs are wanted
only in the three lemmas below. What indexes the cells is a parameter for the
same reason it is one in `DescriptiveComplexity.IxFile`: a program on a clock
cannot give every element of the universe a register, and a tape does not care
which does. -/
noncomputable def trackTapeAt [DecidableEq W] {I : Type}
    (cell : I → (Univ A R P K dd → Prop)) (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m : I → Prop)
    (r : Univ A R P K dd → Prop) : Univ A R P K dd :=
  PR.syElt fun s => if s = t then bitVal PR.zero PR.one (bitAtOf cell m r) else rest r s

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
/-- **The coherence condition of the three register passes, discharged**, at an
arbitrary file: two tracks agreeing off one element present the same symbol at
every cell but that element's register. The track enters the tape only through
`DescriptiveComplexity.bitAtOf`, and `DescriptiveComplexity.bitAtOf_congr` says
that does not move. Every caller of the register passes is given this and owes
nothing. -/
theorem trackTapeAt_coh [DecidableEq W] {I : Type}
    (cell : I → (Univ A R P K dd → Prop)) (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m m' : I → Prop)
    (u : I) (hag : ∀ v, v ≠ u → (m v ↔ m' v))
    (r : Univ A R P K dd → Prop) (hr : r ≠ cell u) :
    PR.trackTapeAt cell t rest m r = PR.trackTapeAt cell t rest m' r := by
  rw [trackTapeAt, trackTapeAt, bitAtOf_congr hag hr]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] in
/-- **What a track shows away from a file**: the walked slot is clear at every
cell that is nobody's register, whatever the track holds. So a register pass
leaves the rest of the tape alone by construction. -/
theorem trackTapeAt_of_not_reg [DecidableEq W]
    (cell : Univ A R P K dd → (Univ A R P K dd → Prop)) (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m : Univ A R P K dd → Prop)
    {r : Univ A R P K dd → Prop} (hno : ∀ u : Univ A R P K dd, r ≠ cell u) :
    PR.trackTapeAt cell t rest m r =
      PR.syElt fun s => if s = t then PR.zero else rest r s := by
  refine congrArg _ (congrArg _ (funext fun s => ?_))
  by_cases hs : s = t
  · rw [if_pos hs, if_pos hs]
    exact bitVal_neg (bitAtOf_of_not_reg hno)
  · rw [if_neg hs, if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **What a track shows at a register of a file**: the track's digit at that
element, in the slot being walked. This is what a rule's guard reads, and the one
statement of the three that needs the file rather than its cells – a cell must
name at most one element. -/
theorem trackTapeAt_cell [DecidableEq W] [Finite (Univ A R P K dd)] {I : Type} {ile : I → I → Prop}
    (F : IxFile (Univ A R P K dd) I ile) (hix : IsLinOrd ile) (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m : I → Prop) (u : I) :
    PR.trackTapeAt F.cell t rest m (F.cell u) =
      PR.syElt fun s =>
        if s = t then bitVal PR.zero PR.one (m u) else rest (F.cell u) s := by
  refine congrArg _ (congrArg _ (funext fun s => ?_))
  by_cases hs : s = t
  · rw [if_pos hs, if_pos hs]
    exact bitVal_congr (F.bitAt_cell hix m u)
  · rw [if_neg hs, if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **The coherence condition of the three register passes, discharged.** -/
theorem trackTape_coh [DecidableEq W] (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m m' : Univ A R P K dd → Prop)
    (u : Univ A R P K dd) (hag : ∀ v, v ≠ u → (m v ↔ m' v))
    (r : Univ A R P K dd → Prop) (hr : r ≠ wmSeg u) :
    PR.trackTapeAt wmSeg t rest m r = PR.trackTapeAt wmSeg t rest m' r :=
  PR.trackTapeAt_coh wmSeg t rest m m' u hag r hr

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **What a track shows away from the register file.** -/
theorem trackTape_of_not_reg [DecidableEq W] (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m : Univ A R P K dd → Prop)
    {r : Univ A R P K dd → Prop} (hno : ∀ u : Univ A R P K dd, r ≠ wmSeg u) :
    PR.trackTapeAt wmSeg t rest m r =
      PR.syElt fun s => if s = t then PR.zero else rest r s :=
  PR.trackTapeAt_of_not_reg wmSeg t rest m hno

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- **What a track shows at a register**: the track's digit at that element, in
the slot being walked. -/
theorem trackTape_wmSeg [DecidableEq W] [Finite (Univ A R P K dd)]
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) (t : W)
    (rest : (Univ A R P K dd → Prop) → W → A) (m : Univ A R P K dd → Prop)
    (u : Univ A R P K dd) :
    PR.trackTapeAt wmSeg t rest m (wmSeg u) =
      PR.syElt fun s =>
        if s = t then bitVal PR.zero PR.one (m u) else rest (wmSeg u) s :=
  PR.trackTapeAt_cell (wmSegFile hlin).toIx hlin t rest m u

end Prog

end Pfp

end DescriptiveComplexity
