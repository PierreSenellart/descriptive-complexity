/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSites

/-!
# The background: the machine's mutable state, presented as a tape

Every kit discharge takes a family of **slot equations** – the register mark
is set exactly at the register cells, the marker at one working-area
address, and so on. They are all facts about one object: the machine's
mutable state – its registers, its stage tracks, its markers – laid over the
permanent marks of `DescriptiveComplexity.Draw.slotMark`. This file is that
object, `DescriptiveComplexity.Draw.TapeSt`, its presentation
`DescriptiveComplexity.Draw.Data.back` as the `rest` family the pass layer
walks, and the slot equations, proved once: the discharges of
`DrawRun` will cite them instead of re-deriving per call site.

The split of a track's home: the four machine registers (`mir`, `tgt`,
`sav`, `val`) hold bits **per element** – their digit at a cell is
`DescriptiveComplexity.regBit`, set only at register cells – while the stage
tracks (`old i`, `new i`) and the working-area markers (`wk`, `bot`, `ltp`)
hold bits **per cell**, anywhere on the tape. The permanent mark slots
(`reg`, the ends, `blk`, `name`, `pdd`) read
`DescriptiveComplexity.Draw.slotMark` at register cells and are clear
elsewhere, which is what their read-back equations say.

**What indexes the file is a parameter.**
`DescriptiveComplexity.Draw.Data.ixBack` reads a background at an arbitrary
index, because a program on a clock cannot give every element of the universe a
register and nothing here needs it to: a slot depends on the register's block,
on the tuple it names, on where it sits in the layout order, and on nothing else
about the index. The state carries the index with it – the four machine
registers hold a bit *per register* and the stage tracks and markers a bit *per
cell*, so `DescriptiveComplexity.Draw.TapeSt` takes the index and
`DescriptiveComplexity.Draw.TapeStD` is the elementwise case.
`DescriptiveComplexity.Draw.Data.back` is that at the
diagonal – the index the universe itself, the order its own – which is what a
space-bounded program uses, and every slot equation below is stated there. The
two ends are already general
(`DescriptiveComplexity.Draw.Data.ixBack_regFirst`,
`DescriptiveComplexity.Draw.Data.ixBack_regLast`): which cell carries them is
a fact about the layout order and about nothing else.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **The machine's mutable state**: the four registers (bits per element),
the stage tracks and markers (bits per cell). The permanent marks are not
here – they never change. -/
structure TapeSt (dt : Data L) (A R' P' I : Type) : Type 1 where
  /-- The MIRROR register. -/
  mir : I → Prop
  /-- The TARGET register. -/
  tgt : I → Prop
  /-- The SAV register. -/
  sav : I → Prop
  /-- The VAL register. -/
  val : I → Prop
  /-- The current stage of each variable, a bit per cell. -/
  old : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The next stage of each variable, a bit per cell. -/
  new : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The working-cell marker, a bit per cell. -/
  wk : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The bottom marker, a bit per cell. -/
  bot : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop
  /-- The end marker of the logical interval, a bit per cell. -/
  ltp : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop

/-- **The machine's state at the elementwise file**: one register per element
of the universe, which is what a space-bounded program has. -/
abbrev TapeStD (dt : Data L) (A R' P' : Type) : Type 1 :=
  TapeSt dt A R' P' (Univ A R' P' dt.KIx dt.dd)

/-- **The tuple a control names**: the coordinates it computes below `dd₀`, the
designated zero above – the canonical padding of every register a scan by name
stops at. -/
def padTup {L : Language.{0, 0}} {dt : Data L} {A : Type}
    (zero : A) (c : Fin dt.dd0 → A) : Fin dt.dd → A :=
  fun j => if h : (j : ℕ) < dt.dd0 then c ⟨j, h⟩ else zero

/-- **What a register file is, as the background reads it**: the cells, the
order they are laid out in, the block each register belongs to and the tuple it
names. Those four are everything a slot depends on, and none of them asks the
index to be the universe.

Bundled rather than passed one at a time because the whole evaluation layer
carries it, and because a bare family of cells is what a *definition* can take:
a register file carries proofs as well, and only the statements need those. -/
structure Layout (dt : Data L) (A R' P' I : Type) : Type where
  /-- The address of the register an index names. -/
  cell : I → (Univ A R' P' dt.KIx dt.dd → Prop)
  /-- The order the registers are laid out in. -/
  le : I → I → Prop
  /-- The block a register belongs to. -/
  blk : I → Option dt.KIx
  /-- The tuple a register names. -/
  arg : I → Fin dt.dd → A

namespace Layout

/-- **A layout whose registers are told apart by their marks**: two registers of
one and the same block, both canonically padded, whose named coordinates agree,
are the same register.

This is what a navigation-by-name scan asks of its stopping condition, and it is
where a layout does real work: the elementwise one has it because a register
*is* its tag and its tuple, and a clocked program's file has it because its
index carries the block and the tuple and nothing else. -/
def NameSep {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
    (lay : Layout dt A R' P' I) (zero : A) (hdd : dt.dd0 ≤ dt.dd) : Prop :=
  ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (u u' : I), lay.blk u = some b → lay.blk u' = some b →
    (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u j = zero) →
    (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u' j = zero) →
    (∀ j : Fin dt.dd0, lay.arg u (Fin.castLE hdd j) = lay.arg u' (Fin.castLE hdd j)) →
    u = u'

/-- **A layout with a register for every named tuple**: whatever block and
whatever tuple the control names, some register carries them.

This is the second half of what a navigation-by-name scan needs – `NameSep`
says the name identifies *at most* one register, this says it identifies at
least one – and it is what a clocked program's file is built to have: its index
*is* the pair of a block and a tuple.

The tuples asked for are the **named** ones, `DescriptiveComplexity.Draw.padTup`
of what a control holds: a mark carries `dd₀` coordinates and nothing reads a
register's tuple above them, so a file that has one register per named tuple has
every register the machine can navigate to, and is smaller than one per tuple by
the factor the padding accounts for. -/
def HasName {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
    (lay : Layout dt A R' P' I) (zero : A) : Prop :=
  ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
    ∃ u : I, lay.blk u = some b ∧ lay.arg u = padTup zero c

/-- **The register a name picks out**: the one `HasName` provides, chosen. A
layout that also has `NameSep` has only one, so this is *the* register of the
block and the tuple, and everything the evaluation layer reads at «the cell of
this tuple» is read here.

Chosen rather than a field, because the two properties are what a file has to
prove and this adds nothing to them. -/
noncomputable def reg {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
    (lay : Layout dt A R' P' I) {zero : A} (hhas : lay.HasName zero)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) : I :=
  (hhas b c).choose

/-- The named register is in the named block. -/
theorem blk_reg {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
    {lay : Layout dt A R' P' I} {zero : A} (hhas : lay.HasName zero)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    lay.blk (lay.reg hhas b c) = some b :=
  (hhas b c).choose_spec.1

/-- The named register carries the named tuple, canonically padded. -/
theorem arg_reg {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
    {lay : Layout dt A R' P' I} {zero : A} (hhas : lay.HasName zero)
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    lay.arg (lay.reg hhas b c) = padTup zero c :=
  (hhas b c).choose_spec.2

end Layout

/-- **A register file together with its layout**: the cells, the order they are
laid out in, the block each register belongs to and the tuple it names, plus the
two conditions that make a family of addresses a file – the cells grow with the
index, and none of them is empty.

This is what the evaluation layer carries. The kits ask for the file alone
(`DescriptiveComplexity.Draw.LaidFile.toIxFile`) and the background for the
layout alone (`DescriptiveComplexity.Draw.LaidFile.toLayout`); carrying the two
together is what lets one parameter stand where
`DescriptiveComplexity.RegFile` stood. -/
structure LaidFile (dt : Data L) (A R' P' I : Type)
    [LinearOrder A] [LinearOrder R'] [LinearOrder P']
    [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] : Type where
  /-- The address of the register an index names. -/
  cell : I → (Univ A R' P' dt.KIx dt.dd → Prop)
  /-- The order the registers are laid out in. -/
  le : I → I → Prop
  /-- The block a register belongs to. -/
  blk : I → Option dt.KIx
  /-- The tuple a register names. -/
  arg : I → Fin dt.dd → A
  /-- Registers laid out later have strictly greater addresses. -/
  strictMono : ∀ u v : I, WMLt le u v → WMSetLt WMLe (cell u) (cell v)
  /-- No register's address is empty. -/
  cell_nonempty : ∀ u : I, ∃ x : Univ A R' P' dt.KIx dt.dd, cell u x

namespace LaidFile

variable {L : Language.{0, 0}} {dt : Data L} {A R' P' I : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

/-- The layout of a laid file: what the background reads. -/
@[reducible] def toLayout (F : LaidFile dt A R' P' I) : Layout dt A R' P' I :=
  ⟨F.cell, F.le, F.blk, F.arg⟩

/-- The file of a laid file: what the kits walk. -/
@[reducible] def toIxFile (F : LaidFile dt A R' P' I) :
    IxFile (Univ A R' P' dt.KIx dt.dd) I F.le :=
  ⟨F.cell, F.strictMono, F.cell_nonempty⟩

end LaidFile

/-- **The laid file a space-bounded program uses**: one register per element of
the universe, in the universe's own order, each naming its own tag's block and
its own tuple. -/
@[reducible] noncomputable def laidFile {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
    [LinearOrder A] [LinearOrder R'] [LinearOrder P']
    [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
    (F : RegFile (Univ A R' P' dt.KIx dt.dd))
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    LaidFile dt A R' P' (Univ A R' P' dt.KIx dt.dd) :=
  ⟨F.cell, tagTupleLe, fun u => tagBlk u.1, fun u => u.2,
    fun u v hlt => F.strictMono u v ⟨(hord u v).mpr hlt.1,
      fun hc => hlt.2 ((hord v u).mp hc)⟩,
    F.cell_nonempty⟩

/-- **The elementwise file's layout order is linear**, given that the universe's
is and that the two agree – which is the `hord` every diagonal statement of the
layer already carries. -/
theorem isLinOrd_laidFile_le {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}
    [LinearOrder A] [LinearOrder R'] [LinearOrder P']
    [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
    {F : RegFile (Univ A R' P' dt.KIx dt.dd)}
    {hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y}
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd))) :
    IsLinOrd (laidFile (dt := dt) F hord).le :=
  show IsLinOrd (tagTupleLe (A := A) (Tag := Tag R' P' dt.KIx)) from
    (funext fun x => funext fun y => propext (hord x y) :
      (WMLe (A := Univ A R' P' dt.KIx dt.dd)) = tagTupleLe) ▸ hlin

namespace Data

variable (dt : Data L) {A R' P' : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

open Classical in
/-- **The state, presented as a background, at an arbitrary index for the
file**: the value of each slot at each cell. The walked track of a pass is
carved out of this by `DescriptiveComplexity.Draw.Prog.trackTapeAt`; everything
else rides along.

What the file is indexed by is a parameter, because a clocked program cannot
give every element of the universe a register and
nothing here needs it to: a register's contents depend on its **block**, on the
**tuple** it names, and on where it sits in the layout order, and on nothing
else about the index. `DescriptiveComplexity.Data.back` is this at the
diagonal, which is what a space-bounded program uses. -/
noncomputable def ixBack {I : Type} (lay : Layout dt A R' P' I)
    (zero one : A) (hdd : dt.dd0 ≤ dt.dd)
    (st : TapeSt dt A R' P' I) (r : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.SlotIx → A
  | .reg => bitVal zero one (∃ u : I, r = lay.cell u)
  | .regFirst => bitVal zero one (∃ u : I, r = lay.cell u ∧ ∀ y : I, lay.le u y)
  | .regLast => bitVal zero one (∃ u : I, r = lay.cell u ∧ ∀ y : I, lay.le y u)
  | .blk b => bitVal zero one (∃ u : I, r = lay.cell u ∧ lay.blk u = b)
  | .name j =>
    if h : ∃ u : I, r = lay.cell u then lay.arg h.choose (Fin.castLE hdd j) else zero
  | .pdd =>
    bitVal zero one (∃ u : I, r = lay.cell u ∧
      ∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u j = zero)
  | .mir => bitVal zero one (bitAtOf lay.cell st.mir r)
  | .tgt => bitVal zero one (bitAtOf lay.cell st.tgt r)
  | .sav => bitVal zero one (bitAtOf lay.cell st.sav r)
  | .val => bitVal zero one (bitAtOf lay.cell st.val r)
  | .wk => bitVal zero one (st.wk r)
  | .bot => bitVal zero one (st.bot r)
  | .ltp => bitVal zero one (st.ltp r)
  | .old i => bitVal zero one (st.old i r)
  | .new i => bitVal zero one (st.new i r)

/-- **The layout a space-bounded program's file has**: one register per element
of the universe, in the universe's own order, each naming its own tag's block
and its own tuple. -/
@[reducible] noncomputable def diagLayout
    (cell : Univ A R' P' dt.KIx dt.dd → (Univ A R' P' dt.KIx dt.dd → Prop)) :
    Layout dt A R' P' (Univ A R' P' dt.KIx dt.dd) where
  cell := cell
  le := tagTupleLe
  blk := fun u => tagBlk u.1
  arg := fun u => u.2

/-- **The elementwise file, laid out**: one register per element of the
universe, in the universe's own order, each naming its own tag's block and its
own tuple. This is what a space-bounded program's register file is, read as a
`DescriptiveComplexity.Draw.LaidFile`, so that the runs stated at an arbitrary
file apply to it – its layout is `DescriptiveComplexity.Draw.Data.diagLayout`
on the nose, so its background is `DescriptiveComplexity.Draw.Data.back`. -/
noncomputable def diagLaid (RF : RegFile (Univ A R' P' dt.KIx dt.dd))
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    LaidFile dt A R' P' (Univ A R' P' dt.KIx dt.dd) where
  cell := RF.cell
  le := tagTupleLe
  blk := fun u => tagBlk u.1
  arg := Prod.snd
  strictMono := fun u v h => RF.strictMono u v
    ⟨(hord u v).mpr h.1, fun hc => h.2 ((hord v u).mp hc)⟩
  cell_nonempty := RF.cell_nonempty

/-- **The elementwise layout order is linear**, being the address order. -/
theorem isLinOrd_diagLaid_le (RF : RegFile (Univ A R' P' dt.KIx dt.dd))
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd))) :
    IsLinOrd (dt.diagLaid RF hord).le := by
  refine ⟨fun u => (hord u u).mp (hlin.1 u), fun u v w h₁ h₂ =>
    (hord u w).mp (hlin.2.1 u v w ((hord u v).mpr h₁) ((hord v w).mpr h₂)),
    fun u v h₁ h₂ => hlin.2.2.1 u v ((hord u v).mpr h₁) ((hord v u).mpr h₂),
    fun u v => ?_⟩
  rcases hlin.2.2.2 u v with h | h
  · exact Or.inl ((hord u v).mp h)
  · exact Or.inr ((hord v u).mp h)

/-- **The elementwise file names each element by itself**, which is the identity
embedding of `DescriptiveComplexity.ixAddr`. -/
theorem wmLt_diagLaid_le (RF : RegFile (Univ A R' P' dt.KIx dt.dd))
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    (u u' : Univ A R' P' dt.KIx dt.dd) :
    WMLt (dt.diagLaid RF hord).le u u' ↔ WMLt WMLe (id u) (id u') :=
  ⟨fun h => ⟨(hord u u').mpr h.1, fun hc => h.2 ((hord u' u).mp hc)⟩,
    fun h => ⟨(hord u u').mp h.1, fun hc => h.2 ((hord u' u).mpr hc)⟩⟩

/-- **The state, presented as a background**: `DescriptiveComplexity.Data.ixBack`
at the layout a space-bounded program's file has. -/
noncomputable def back (cell : Univ A R' P' dt.KIx dt.dd → (Univ A R' P' dt.KIx dt.dd → Prop))
    (zero one : A) (hdd : dt.dd0 ≤ dt.dd)
    (st : TapeStD dt A R' P') (r : Univ A R' P' dt.KIx dt.dd → Prop) : dt.SlotIx → A :=
  dt.ixBack (dt.diagLayout cell) zero one hdd st r

section IxSlots

/-! ### The slot equations, at an arbitrary layout

Everything a slot of the background is depends on the layout and nothing else,
so the equations that read one back are stated there once. The diagonal forms
below are their instances at `DescriptiveComplexity.Draw.Data.diagLayout`,
kept under their own names because that is what the whole evaluation layer
rewrites with. -/

variable {I : Type} {lay : Layout dt A R' P' I}
variable {zero one : A} {hdd : dt.dd0 ≤ dt.dd} {stI : TapeSt dt A R' P' I}

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The marker slot, at an arbitrary layout. -/
theorem ixBack_wk :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.ixBack lay zero one hdd stI r .wk = bitVal zero one (stI.wk r) :=
  fun _ => rfl

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the file, a state with no track set presents the blank**, at an
arbitrary layout. -/
theorem ixBack_of_not_reg {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : I, r ≠ lay.cell u)
    (hwk : ¬stI.wk r) (hbot : ¬stI.bot r) (hltp : ¬stI.ltp r)
    (hold : ∀ i : dt.d.B.ι, ¬stI.old i r) (hnew : ∀ i : dt.d.B.ι, ¬stI.new i r) :
    dt.ixBack lay zero one hdd stI r = fun _ => zero := by
  have hno : ¬∃ u : I, r = lay.cell u := fun hc => hr hc.choose hc.choose_spec
  funext sl
  cases sl with
  | reg => exact bitVal_neg hno
  | regFirst => exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
  | regLast => exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
  | blk b => exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
  | name j => exact dif_neg hno
  | pdd => exact bitVal_neg fun hc => hr hc.choose hc.choose_spec.1
  | mir => exact bitVal_neg (bitAtOf_of_not_reg hr)
  | tgt => exact bitVal_neg (bitAtOf_of_not_reg hr)
  | sav => exact bitVal_neg (bitAtOf_of_not_reg hr)
  | val => exact bitVal_neg (bitAtOf_of_not_reg hr)
  | wk => exact bitVal_neg hwk
  | bot => exact bitVal_neg hbot
  | ltp => exact bitVal_neg hltp
  | old i => exact bitVal_neg (hold i)
  | new i => exact bitVal_neg (hnew i)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The background reads the stage tracks at one cell**, at an arbitrary
layout. -/
theorem ixBack_old_congr (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {r : Univ A R' P' dt.KIx dt.dd → Prop} (hr : ∀ i : dt.d.B.ι, (σ i r ↔ stI.old i r)) :
    dt.ixBack lay zero one hdd { stI with old := σ } r =
      dt.ixBack lay zero one hdd stI r := by
  funext sl
  cases sl with
  | old i => exact bitVal_congr (hr i)
  | _ => rfl

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the file the background is blind to every register**, at an arbitrary
layout. -/
theorem ixBack_congr_off_reg {stI stI' : TapeSt dt A R' P' I}
    (hwk : stI.wk = stI'.wk) (hbot : stI.bot = stI'.bot) (hltp : stI.ltp = stI'.ltp)
    (hold : stI.old = stI'.old) (hnew : stI.new = stI'.new)
    {r : Univ A R' P' dt.KIx dt.dd → Prop} (hr : ¬∃ u : I, r = lay.cell u) :
    dt.ixBack lay zero one hdd stI r = dt.ixBack lay zero one hdd stI' r := by
  have hreg : ∀ m : I → Prop, ¬bitAtOf lay.cell m r :=
    fun m hc => hr ⟨hc.choose, hc.choose_spec.1⟩
  funext sl
  cases sl with
  | mir => exact bitVal_congr (iff_of_false (hreg stI.mir) (hreg stI'.mir))
  | tgt => exact bitVal_congr (iff_of_false (hreg stI.tgt) (hreg stI'.tgt))
  | sav => exact bitVal_congr (iff_of_false (hreg stI.sav) (hreg stI'.sav))
  | val => exact bitVal_congr (iff_of_false (hreg stI.val) (hreg stI'.val))
  | wk => exact congrArg (bitVal zero one) (congrFun hwk r)
  | bot => exact congrArg (bitVal zero one) (congrFun hbot r)
  | ltp => exact congrArg (bitVal zero one) (congrFun hltp r)
  | old i => exact congrArg (bitVal zero one) (congrFun (congrFun hold i) r)
  | new i => exact congrArg (bitVal zero one) (congrFun (congrFun hnew i) r)
  | _ => rfl

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The block one-hot, at a register cell of an arbitrary layout. -/
theorem ixBack_blk_cell (hinj : Function.Injective lay.cell)
    (u : I) (b : Option (Fin dt.ko ⊕ Fin dt.ki)) :
    dt.ixBack lay zero one hdd stI (lay.cell u) (.blk b) =
      bitVal zero one (lay.blk u = b) := by
  refine bitVal_congr ⟨?_, fun h => ⟨u, rfl, h⟩⟩
  rintro ⟨v, hv, hvb⟩
  rw [hinj hv]
  exact hvb

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The padding mark, at a register cell of an arbitrary layout. -/
theorem ixBack_pdd_cell (hinj : Function.Injective lay.cell) (u : I) :
    dt.ixBack lay zero one hdd stI (lay.cell u) .pdd =
      bitVal zero one (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u j = zero) := by
  refine bitVal_congr ⟨?_, fun h => ⟨u, rfl, h⟩⟩
  rintro ⟨v, hv, hvb⟩
  rw [hinj hv]
  exact hvb

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- A name slot, at a register cell of an arbitrary layout. -/
theorem ixBack_name_cell (hinj : Function.Injective lay.cell) (u : I) (j : Fin dt.dd0) :
    dt.ixBack lay zero one hdd stI (lay.cell u) (.name j) = lay.arg u (Fin.castLE hdd j) := by
  classical
  change (if h : ∃ v : I, lay.cell u = lay.cell v then
    lay.arg h.choose (Fin.castLE hdd j) else zero) = _
  rw [dif_pos ⟨u, rfl⟩]
  have hspec := (⟨u, rfl⟩ : ∃ v : I, lay.cell u = lay.cell v).choose_spec
  rw [show (⟨u, rfl⟩ : ∃ v : I, lay.cell u = lay.cell v).choose = u from (hinj hspec).symm]

end IxSlots

variable {cell : Univ A R' P' dt.KIx dt.dd → (Univ A R' P' dt.KIx dt.dd → Prop)}
variable {zero one : A} {hdd : dt.dd0 ≤ dt.dd} {st : TapeStD dt A R' P'}

/-! ### The slot equations, once -/

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The register mark: set exactly at the register cells – the equation
every discharge's `hrg` is. -/
theorem back_reg :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r .reg =
        bitVal zero one (∃ u : Univ A R' P' dt.KIx dt.dd, r = cell u) :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The marker slot, read back. -/
theorem back_wk :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r .wk = bitVal zero one (st.wk r) :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The bottom mark, read back. -/
theorem back_bot :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r .bot = bitVal zero one (st.bot r) :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The end mark, read back. -/
theorem back_ltp :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r .ltp = bitVal zero one (st.ltp r) :=
  fun _ => rfl

open Classical in
omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **A name slot, read back**: the coordinate the register's own index carries,
and the designated `zero` where there is no register. Stated because the
definition matches on the slot, so `rw` cannot reach the branch on its own. -/
theorem back_name (j : Fin dt.dd0) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r (.name j) =
        if h : ∃ u : Univ A R' P' dt.KIx dt.dd, r = cell u then h.choose.2 (Fin.castLE hdd j)
        else zero :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- A stage track, read back. -/
theorem back_old (i : dt.d.B.ι) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r (.old i) = bitVal zero one (st.old i r) :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The next-stage track, read back. -/
theorem back_new (i : dt.d.B.ι) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r (.new i) = bitVal zero one (st.new i r) :=
  fun _ => rfl

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the file, a state with no track set presents the blank.** Every slot
of the background at a cell that is nobody's register is either a permanent
mark – existentially quantified over the registers, hence false there – or a
register digit, false for the same reason, or one of the five per-cell tracks,
which the hypotheses ask to be clear.

This is what makes the phase that *builds* a file a sweep of the file's stretch
and nothing more: below the stretch and above it the background the phase has to
produce is already the blank the machine started from, so the two ends of the
sweep are the two ends of the file. -/
theorem back_of_not_reg {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : Univ A R' P' dt.KIx dt.dd, r ≠ cell u)
    (hwk : ¬st.wk r) (hbot : ¬st.bot r) (hltp : ¬st.ltp r)
    (hold : ∀ i : dt.d.B.ι, ¬st.old i r) (hnew : ∀ i : dt.d.B.ι, ¬st.new i r) :
    dt.back cell zero one hdd st r = fun _ => zero :=
  dt.ixBack_of_not_reg hr hwk hbot hltp hold hnew

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The background reads the stage tracks at one cell.** Two states differing
in the `old` tracks alone present the same background at every cell where those
tracks agree – the other slots being marks, register digits, or per-cell tracks
the update leaves alone.

This is what a *guessing* phase needs: it rewrites the `old` tracks cell by cell,
and the congruence is what says the cells it has not reached yet still read what
they did. -/
theorem back_old_congr (σ : dt.d.B.ι → (Univ A R' P' dt.KIx dt.dd → Prop) → Prop)
    {r : Univ A R' P' dt.KIx dt.dd → Prop} (hr : ∀ i : dt.d.B.ι, (σ i r ↔ st.old i r)) :
    dt.back cell zero one hdd { st with old := σ } r =
      dt.back cell zero one hdd st r :=
  dt.ixBack_old_congr σ hr

/-! ### What a state's scratch registers do not decide

The VAL loop threads SAV and TARGET and nothing else
(`DescriptiveComplexity.Draw.Data.roundEndSt_eq`), so its rounds run at
states that differ from the machinery's entry state in those two registers
alone. `ScratchEq` names that relation, and the lemmas below say what it
buys: every per-cell mark and track is shared, hence so is the background
at every cell of the working area — the four register slots being
`DescriptiveComplexity.regBit`s, set at a register cell only. -/

/-- **Two states differing in the two scratch registers alone**: every mark
and every track is shared, the saved mirror and the target need not be. -/
def ScratchEq {I : Type} (st st' : TapeSt dt A R' P' I) : Prop :=
  st.wk = st'.wk ∧ st.mir = st'.mir ∧ st.val = st'.val ∧ st.old = st'.old ∧
    st.new = st'.new ∧ st.bot = st'.bot ∧ st.ltp = st'.ltp

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- Rewriting the two scratch registers is a `ScratchEq`. -/
theorem scratchEq_scratch (st : TapeStD dt A R' P')
    (X Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with sav := X, tgt := Y } st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` is symmetric. -/
theorem ScratchEq.symm {I : Type} {st st' : TapeSt dt A R' P' I}
    (h : dt.ScratchEq st st') : dt.ScratchEq st' st :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm,
    h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` is transitive. -/
theorem ScratchEq.trans {I : Type} {st st' st'' : TapeSt dt A R' P' I}
    (h : dt.ScratchEq st st') (h' : dt.ScratchEq st' st'') :
    dt.ScratchEq st st'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.1.trans h'.2.2.2.2.1,
    h.2.2.2.2.2.1.trans h'.2.2.2.2.2.1,
    h.2.2.2.2.2.2.trans h'.2.2.2.2.2.2⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same scratch registers on both
sides. -/
theorem ScratchEq.scratch {st st' : TapeStD dt A R' P'}
    (h : dt.ScratchEq st st') (X Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with sav := X, tgt := Y }
      { st' with sav := X, tgt := Y } :=
  h

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same target on both sides. -/
theorem ScratchEq.tgt {st st' : TapeStD dt A R' P'}
    (h : dt.ScratchEq st st') (Y : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with tgt := Y } { st' with tgt := Y } :=
  h

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same VAL register on both sides. -/
theorem ScratchEq.val {st st' : TapeStD dt A R' P'}
    (h : dt.ScratchEq st st') (m : Univ A R' P' dt.KIx dt.dd → Prop) :
    dt.ScratchEq { st with val := m } { st' with val := m } :=
  ⟨h.1, h.2.1, rfl, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the register file the background is blind to every register**: the
four register slots read `DescriptiveComplexity.bitAtOf`, which is set at a
register cell only, so at a cell of the working area two states agree as
soon as their per-cell marks and tracks do — whatever their mirror, their
target, their saved mirror or their VAL content is. This is what lets the
control of the VAL loop's *threaded* states be the control of the
unthreaded ones: threading rewrites the two scratch registers, and the
rounds read their background at the working cell. -/
theorem back_congr_off_reg {st st' : TapeStD dt A R' P'}
    (hwk : st.wk = st'.wk) (hbot : st.bot = st'.bot) (hltp : st.ltp = st'.ltp)
    (hold : st.old = st'.old) (hnew : st.new = st'.new)
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ¬∃ u : Univ A R' P' dt.KIx dt.dd, r = cell u) :
    dt.back cell zero one hdd st r = dt.back cell zero one hdd st' r :=
  dt.ixBack_congr_off_reg hwk hbot hltp hold hnew hr

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- `ScratchEq` survives writing the same save and target on both sides, at an
arbitrary file. -/
theorem ScratchEq.ixScratch {I : Type} {st st' : TapeSt dt A R' P' I}
    (h : dt.ScratchEq st st') (X Y : I → Prop) :
    dt.ScratchEq { st with sav := X, tgt := Y } { st' with sav := X, tgt := Y } := h

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- **The background at a working cell, off a `ScratchEq`, at an arbitrary
layout**: two states differing in the two scratch registers alone present the
same background wherever no register is. -/
theorem ScratchEq.ixBack {I : Type} {lay : Layout dt A R' P' I}
    {st st' : TapeSt dt A R' P' I} (h : dt.ScratchEq st st')
    {zero one : A} {hdd : dt.dd0 ≤ dt.dd}
    {r : Univ A R' P' dt.KIx dt.dd → Prop} (hr : ¬∃ u : I, r = lay.cell u) :
    dt.ixBack lay zero one hdd st r = dt.ixBack lay zero one hdd st' r :=
  dt.ixBack_congr_off_reg h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 h.2.2.2.1
    h.2.2.2.2.1 hr

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
variable {dt} in
/-- The background at a working cell, off a `ScratchEq`. -/
theorem ScratchEq.back {st st' : TapeStD dt A R' P'} (h : dt.ScratchEq st st')
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ¬∃ u : Univ A R' P' dt.KIx dt.dd, r = cell u) :
    dt.back cell zero one hdd st r = dt.back cell zero one hdd st' r :=
  dt.back_congr_off_reg h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 h.2.2.2.1
    h.2.2.2.2.1 hr

section IxName

/-! ### The navigation by name, at an arbitrary layout

The three equations above are all a name scan reads, so the guard's reading is
stated at the layout too. Only the *uniqueness* asks anything of the layout –
`DescriptiveComplexity.Draw.Layout.NameSep`, that the marks tell the registers
apart – and the elementwise layout has it because a register is its tag and its
tuple. -/

variable {I : Type} {lay : Layout dt A R' P' I}
variable {zero one : A} {hdd : dt.dd0 ≤ dt.dd} {stI : TapeSt dt A R' P' I}

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The name guard, at a register cell of an arbitrary layout**: the register
is in the named block, canonically padded, and carries the coordinates the
control computes. -/
theorem ixNameGF_cell (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A)
    (fc : Q → A) (u : I) :
    dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI (lay.cell u)) ↔
      (lay.blk u = some b ∧
        (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → lay.arg u j = zero) ∧
        ∀ j : Fin dt.dd0, lay.arg u (Fin.castLE hdd j) = cf fc j) := by
  rw [Data.nameGF, dt.ixBack_blk_cell hinj, dt.ixBack_pdd_cell hinj]
  refine and_congr (bitVal_iff hzo) (and_congr (bitVal_iff hzo) ?_)
  exact forall_congr' fun j => iff_of_eq (congrArg (· = cf fc j)
    (dt.ixBack_name_cell hinj u j))

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The name guard identifies one register**, at a layout whose marks tell
them apart. -/
theorem ixNameGF_unique (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    (hsep : lay.NameSep zero hdd)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {u u' : I}
    (h : dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI (lay.cell u)))
    (h' : dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI (lay.cell u'))) :
    u = u' := by
  obtain ⟨hb, hp, hn⟩ := (dt.ixNameGF_cell hzo hinj b cf fc u).mp h
  obtain ⟨hb', hp', hn'⟩ := (dt.ixNameGF_cell hzo hinj b cf fc u').mp h'
  exact hsep b u u' hb hb' hp hp' fun j => (hn j).trans (hn' j).symm

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the file the name guard fails**, at an arbitrary layout: the block
one-hot is clear there, so no scan stops in the working area. -/
theorem ixNot_nameGF_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : I, r ≠ lay.cell u) :
    ¬dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI r) := by
  rintro ⟨hb, -, -⟩
  obtain ⟨u, hu, -⟩ := (bitVal_iff hzo).mp hb
  exact hr u hu

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- A named tuple is canonically padded. -/
theorem padTup_pad (zero : A) (c : Fin dt.dd0 → A) {j : Fin dt.dd}
    (hj : dt.dd0 ≤ (j : ℕ)) : padTup zero c j = zero :=
  dif_neg (by omega)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- A named tuple carries the control's coordinates. -/
theorem padTup_coord (zero : A) (c : Fin dt.dd0 → A) (hdd : dt.dd0 ≤ dt.dd)
    (j : Fin dt.dd0) : padTup zero c (Fin.castLE hdd j) = c j := by
  have h : ((Fin.castLE hdd j : Fin dt.dd) : ℕ) < dt.dd0 := j.isLt
  change (if h : ((Fin.castLE hdd j : Fin dt.dd) : ℕ) < dt.dd0 then
    c ⟨_, h⟩ else zero) = c j
  rw [dif_pos h]
  exact congrArg c (Fin.ext rfl)

end IxName

section IxSeek

/-! ### The register a name identifies

Put the two halves together: on a layout whose marks tell its registers apart
(`DescriptiveComplexity.Draw.Layout.NameSep`) and which has a register for every
name (`DescriptiveComplexity.Draw.Layout.HasName`), the guard of a scan by name
holds at **one** register of the file and nowhere else on it. That is exactly
the pair of hypotheses `DescriptiveComplexity.Draw.Prog.reaches_toCell` asks
for, so a caller's scan arrives at a register it can name.

This is what replaces the address-carrying random access at a clocked program's
file: `DescriptiveComplexity.Draw.SeekKit` steps a marker until the walked
mirror equals a **target written across the file**, which needs one register per
address; a scan by name needs only the `dd₀` coordinates the control already
holds. -/

variable {I : Type} {lay : Layout dt A R' P' I}
variable {zero one : A} {hdd : dt.dd0 ≤ dt.dd} {stI : TapeSt dt A R' P' I}
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The name guard holds at the named register.** -/
theorem nameGF_named (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {u : I} (hb : lay.blk u = some b)
    (ha : lay.arg u = padTup zero (cf fc)) :
    dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI (lay.cell u)) :=
  (dt.ixNameGF_cell hzo hinj b cf fc u).mpr
    ⟨hb, fun j hj => by rw [ha]; exact dt.padTup_pad zero (cf fc) hj,
      fun j => by rw [ha]; exact dt.padTup_coord zero (cf fc) hdd j⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The name guard holds at exactly one address of the file**: at the named
register, and at no other register nor anywhere off the file. The stopping
condition of a scan by name, in the shape a scan asks for. -/
theorem nameGF_unique_addr (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    (hsep : lay.NameSep zero hdd)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {u : I} (hb : lay.blk u = some b)
    (ha : lay.arg u = padTup zero (cf fc))
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI r)) :
    r = lay.cell u := by
  by_cases hreg : ∃ w : I, r = lay.cell w
  · obtain ⟨w, rfl⟩ := hreg
    exact congrArg lay.cell
      (dt.ixNameGF_unique hzo hinj hsep hr (dt.nameGF_named hzo hinj hb ha))
  · exact absurd hr (dt.ixNot_nameGF_of_not_reg hzo
      fun w hw => hreg ⟨w, hw⟩)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A computed name at a register says which register it is**: on a layout
that has a register for every name and tells them apart, the guard holds at
exactly the register whose coordinates the control computes. The trips of the
evaluation layer ask *which* cell they stopped at, and this is the answer,
whatever function of the control the coordinates are. -/
theorem ixNameGF_iff (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    (hsep : lay.NameSep zero hdd) (hhas : lay.HasName zero)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A)
    (fc : Q → A) (u : I) :
    dt.nameGF one b cf fc (dt.ixBack lay zero one hdd stI (lay.cell u)) ↔
      u = lay.reg hhas b (cf fc) := by
  constructor
  · intro hg
    exact dt.ixNameGF_unique hzo hinj hsep hg
      (dt.nameGF_named hzo hinj (Layout.blk_reg hhas b _) (Layout.arg_reg hhas b _))
  · rintro rfl
    exact dt.nameGF_named hzo hinj (Layout.blk_reg hhas b _) (Layout.arg_reg hhas b _)

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The name guard at a register says which register it is**, the coordinates
read straight off the control: `DescriptiveComplexity.Draw.Data.ixNameGF_iff`
at the coordinate slots the copy loops use. -/
theorem ixNameG_iff (hzo : zero ≠ one) (hinj : Function.Injective lay.cell)
    (hsep : lay.NameSep zero hdd) (hhas : lay.HasName zero)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q) (fc : Q → A)
    (u : I) :
    dt.nameG one b coord fc (dt.ixBack lay zero one hdd stI (lay.cell u)) ↔
      u = lay.reg hhas b fun j => fc (coord j) :=
  dt.ixNameGF_iff hzo hinj hsep hhas b (fun f j => f (coord j)) fc u

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **Off the file the coordinate-loop trips' guard fails**, at an arbitrary
layout: the shape the evaluation layer's «the scan stopped nowhere else»
arguments are written against. -/
theorem ixNot_nameG_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : I, r ≠ lay.cell u) :
    ¬dt.nameG one b coord fc (dt.ixBack lay zero one hdd stI r) :=
  dt.ixNot_nameGF_of_not_reg hzo hr

end IxSeek

section Name

variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

/-! ### The permanent marks at a register cell, and the navigation by name

The mark slots are stated existentially – "some element's cell, whose tag's
block is `b`" – because the background is a function of the *address*. At a
register cell the existential collapses, by injectivity of the
cell family, and what is left is the mark of the element
itself. Those three equations are what the navigation-by-name scans read:
`DescriptiveComplexity.Draw.Data.nameG` holds at exactly one cell, the
canonically padded cell of the element whose coordinates the control holds
(`DescriptiveComplexity.Draw.Data.nameG_unique`), and nowhere off the
register file. -/

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- The block one-hot, at a register cell. -/
theorem back_blk_cell (hinj : Function.Injective cell)
    (u : Univ A R' P' dt.KIx dt.dd) (b : Option (Fin dt.ko ⊕ Fin dt.ki)) :
    dt.back cell zero one hdd st (cell u) (.blk b) =
      bitVal zero one (tagBlk u.1 = b) :=
  dt.ixBack_blk_cell hinj u b

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- The padding mark, at a register cell. -/
theorem back_pdd_cell (hinj : Function.Injective cell) (u : Univ A R' P' dt.KIx dt.dd) :
    dt.back cell zero one hdd st (cell u) .pdd =
      bitVal zero one (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) :=
  dt.ixBack_pdd_cell hinj u

omit [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- A name slot, at a register cell: the element's own coordinate. -/
theorem back_name_cell (hinj : Function.Injective cell)
    (u : Univ A R' P' dt.KIx dt.dd) (j : Fin dt.dd0) :
    dt.back cell zero one hdd st (cell u) (.name j) = u.2 (Fin.castLE hdd j) :=
  dt.ixBack_name_cell hinj u j

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The name guard, at a register cell**: the cell's element is in the
named block, canonically padded, and carries the coordinates the control
computes. -/
theorem nameGF_cell (hzo : zero ≠ one)
    (hinj : Function.Injective cell)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A)
    (fc : Q → A) (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameGF one b cf fc (dt.back cell zero one hdd st (cell u)) ↔
      (tagBlk u.1 = some b ∧
        (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) ∧
        ∀ j : Fin dt.dd0, u.2 (Fin.castLE hdd j) = cf fc j) :=
  dt.ixNameGF_cell hzo hinj b cf fc u

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The elementwise layout's marks tell its registers apart**: a register *is*
its tag and its tuple, so the block and the named coordinates spell it. -/
theorem nameSep_diagLayout :
    (dt.diagLayout cell).NameSep zero hdd :=
  fun _ _ _ hb hb' hp hp' hn =>
    eq_of_slotMark_name (hdd := hdd) (hb.trans hb'.symm) hb hn hp hp'

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **A named tuple is the padded one**: `DescriptiveComplexity.Draw.padTup` and
`DescriptiveComplexity.Draw.pad` are the same function, written once for the name
a control holds and once for the geometry. -/
theorem padTup_eq_pad (zero : A) (c : Fin dt.dd0 → A) :
    padTup (dt := dt) zero c = pad (dd := dt.dd) zero c :=
  rfl

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The elementwise layout has a register for every name**: a register is an
element, and every block and tuple names one. -/
theorem hasName_diagLayout : (dt.diagLayout cell).HasName zero := by
  intro b c
  refine ⟨(Tag.arg (toLex b), padTup zero c), ?_, rfl⟩
  exact (tagBlk_eq_some_iff (R := R') (P := P') (Tag.arg (toLex b)) b).mpr rfl

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **At the elementwise layout the named register is the obvious one**: the
element whose tag is the block and whose tuple is the padded name. Chosen by
`DescriptiveComplexity.Draw.Layout.reg`, pinned by `NameSep`. -/
theorem reg_diagLayout (hdd : dt.dd0 ≤ dt.dd) (b : Fin dt.ko ⊕ Fin dt.ki)
    (c : Fin dt.dd0 → A) :
    (dt.diagLayout cell).reg (dt.hasName_diagLayout (zero := zero)) b c =
      (Tag.arg (toLex b), padTup zero c) :=
  dt.nameSep_diagLayout (cell := cell) (zero := zero) (hdd := hdd) b _ _
    (Layout.blk_reg _ b c)
    ((tagBlk_eq_some_iff (R := R') (P := P') (Tag.arg (toLex b)) b).mpr rfl)
    (fun j hj => by rw [Layout.arg_reg]; exact dt.padTup_pad zero c hj)
    (fun j hj => dt.padTup_pad zero c hj)
    (fun j => by rw [Layout.arg_reg])

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The name guard identifies one cell**: two register cells it holds at
are the same. This is what a navigation-by-name scan needs of its stopping
condition (`DescriptiveComplexity.Draw.Prog.reaches_toCell`). -/
theorem nameGF_unique (hzo : zero ≠ one)
    (hinj : Function.Injective cell)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {u u' : Univ A R' P' dt.KIx dt.dd}
    (h : dt.nameGF one b cf fc (dt.back cell zero one hdd st (cell u)))
    (h' : dt.nameGF one b cf fc (dt.back cell zero one hdd st (cell u'))) :
    u = u' :=
  dt.ixNameGF_unique hzo hinj dt.nameSep_diagLayout h h'

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **Off the register file the name guard fails**: the block one-hot is
clear there, so no scan stops in the working area. -/
theorem not_nameGF_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {cf : (Q → A) → Fin dt.dd0 → A}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : Univ A R' P' dt.KIx dt.dd, r ≠ cell u) :
    ¬dt.nameGF one b cf fc (dt.back cell zero one hdd st r) :=
  dt.ixNot_nameGF_of_not_reg hzo hr

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The coordinate-loop trips' guard, at a register cell. -/
theorem nameG_cell (hzo : zero ≠ one)
    (hinj : Function.Injective cell)
    {Q : Type} (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q)
    (fc : Q → A) (u : Univ A R' P' dt.KIx dt.dd) :
    dt.nameG one b coord fc (dt.back cell zero one hdd st (cell u)) ↔
      (tagBlk u.1 = some b ∧
        (∀ j : Fin dt.dd, dt.dd0 ≤ (j : ℕ) → u.2 j = zero) ∧
        ∀ j : Fin dt.dd0, u.2 (Fin.castLE hdd j) = fc (coord j)) :=
  dt.nameGF_cell hzo hinj b _ fc u

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- The coordinate-loop trips' guard identifies one cell. -/
theorem nameG_unique (hzo : zero ≠ one)
    (hinj : Function.Injective cell)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {fc : Q → A} {u u' : Univ A R' P' dt.KIx dt.dd}
    (h : dt.nameG one b coord fc (dt.back cell zero one hdd st (cell u)))
    (h' : dt.nameG one b coord fc (dt.back cell zero one hdd st (cell u'))) :
    u = u' :=
  dt.nameGF_unique hzo hinj h h'

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- Off the register file the coordinate-loop trips' guard fails. -/
theorem not_nameG_of_not_reg (hzo : zero ≠ one)
    {Q : Type} {b : Fin dt.ko ⊕ Fin dt.ki} {coord : Fin dt.dd0 → Q}
    {fc : Q → A} {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ u : Univ A R' P' dt.KIx dt.dd, r ≠ cell u) :
    ¬dt.nameG one b coord fc (dt.back cell zero one hdd st r) :=
  dt.not_nameGF_of_not_reg hzo hr

end Name

/-! ### The two ends of the file, at an arbitrary index

What a discharge asks of the `regFirst` and `regLast` slots is that they be set
at one named cell and nowhere else, and that is a fact about the layout order
alone: antisymmetry says the extreme index is unique, and the file is injective
in nothing – the slot is read off the *index*, not off the address. So both are
stated at the general index, and the elementwise forms are their diagonal. -/

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The file-top mark is the greatest index's cell.** -/
theorem ixBack_regLast {I : Type} {lay : Layout dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hlin : IsLinOrd lay.le) {gtop : I}
    (htop : ∀ y : I, lay.le y gtop) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.ixBack lay zero one hdd st r .regLast =
        bitVal zero one (r = lay.cell gtop) := by
  intro r
  refine bitVal_congr ⟨?_, ?_⟩
  · rintro ⟨u, rfl, hu⟩
    rw [hlin.2.2.1 u gtop (htop u) (hu gtop)]
  · rintro rfl
    exact ⟨gtop, rfl, fun y => htop y⟩

omit [LinearOrder A] [LinearOrder R'] [LinearOrder P']
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **The file-bottom mark is the least index's cell.** -/
theorem ixBack_regFirst {I : Type} {lay : Layout dt A R' P' I}
    {st : TapeSt dt A R' P' I} (hlin : IsLinOrd lay.le) {gbot : I}
    (hbot : ∀ y : I, lay.le gbot y) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.ixBack lay zero one hdd st r .regFirst =
        bitVal zero one (r = lay.cell gbot) := by
  intro r
  refine bitVal_congr ⟨?_, ?_⟩
  · rintro ⟨u, rfl, hu⟩
    rw [hlin.2.2.1 u gbot (hu gbot) (hbot u)]
  · rintro rfl
    exact ⟨gbot, rfl, fun y => hbot y⟩

/-- **The file-top mark is the greatest element's cell**: given that the
universe order is linear, the `regLast` slot is set exactly at the cell of
the top element – the equation every discharge's `hrl` is. -/
theorem back_regLast
    (hlin : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {gtop : Univ A R' P' dt.KIx dt.dd} (htop : ∀ y, WMLe y gtop)
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    ∀ r : Univ A R' P' dt.KIx dt.dd → Prop,
      dt.back cell zero one hdd st r .regLast = bitVal zero one (r = cell gtop) := by
  have heq : (WMLe (A := Univ A R' P' dt.KIx dt.dd)) = tagTupleLe :=
    funext fun x => funext fun y => propext (hord x y)
  exact dt.ixBack_regLast (lay := dt.diagLayout cell)
    (show IsLinOrd tagTupleLe from heq ▸ hlin) fun y => (hord y gtop).mp (htop y)

end Data

end Draw

end DescriptiveComplexity
