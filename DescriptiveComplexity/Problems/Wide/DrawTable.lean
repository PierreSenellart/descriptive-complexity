/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawGeom
import DescriptiveComplexity.Problems.Wide.Key
import DescriptiveComplexity.Problems.Wide.Tape

/-!
# The transition table, and the two promises it has to keep

The instance a hardness reduction into `DescriptiveComplexity.DWideAcceptSpace`
emits is a wide machine, and a wide machine is eleven relations on a finite type
(`DescriptiveComplexity.Problems.Wide.Instance` reads the smallest one). This
file says what those eleven relations are, once and for all, in terms of a
**table**: the program's rules, each with its guard, its two phases, the symbol
it reads and the one it writes, and the direction it moves in.

## What a rule is, and why it lives in the tag

`DescriptiveComplexity.Draw.Table` is indexed by two arbitrary types – `R`, the
rules, and `P`, the phases – which are the two halves of
`DescriptiveComplexity.Draw.Tag`. A transition is therefore an element
`(ctrl r, pad w)`: its rule is its **tag** and its tuple carries only the rule's
*data*, the elements the rule acts at. That is the library's "index rules by
attribute values, not by the transition" read at the level of the layout, and it
is what will make every defining formula of the interpretation a decision taken
when the formula is *built* – the source phase, the destination phase and the
direction of a rule are functions of its tag alone.

## Semantics first

Nothing here is a formula. The eleven relations are plain predicates on the
tagged-tuple universe, and the instance is only *assumed* to read them
(`DescriptiveComplexity.Draw.Table.Reads`); the interpretation that makes the
assumption true is written later, and the equivalence is definitional, the
interpreted universe being the tagged tuples themselves. Everything a program
proves is therefore proved once, about any structure reading the table.

## What the file delivers

| for | theorem |
|---|---|
| a rule fires, moving right | `DescriptiveComplexity.Draw.Table.fire_right` |
| a rule fires, moving left | `DescriptiveComplexity.Draw.Table.fire_left` |
| the promise of `WideAcceptSpace` | `DescriptiveComplexity.Draw.Table.wellFormed` |
| the promise `DWideAcceptSpace` adds | `DescriptiveComplexity.Draw.Table.deterministic` |

The two promises cost exactly what the layout was designed to make them cost.
Well-formedness is the order being linear – it is
`DescriptiveComplexity.tagTupleLe`, so `DescriptiveComplexity.Wide.isLinOrd_tagTupleLe`
settles it – plus the input and the blank being functional, which they are
because both are written as *equations*. Determinism is one condition on the
table, `DescriptiveComplexity.Draw.Table.Sep`: two guarded rules agreeing on the
state they apply in and the symbol they read are the same rule with the same
data. The padding of `DescriptiveComplexity.Draw.pad` is what makes that a
condition about payloads rather than about tuples, which is the whole reason it
is there.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-- **The universe the reduction emits**: tagged tuples, one block per tag. An
`abbrev`, so that it is the interpreted universe on the nose and a pair may be
destructured without ceremony. -/
abbrev Univ (A R P K : Type) (dd : ℕ) : Type := Tag R P K × (Fin dd → A)

/-- **The transition table of the emitted machine.** The reduction chooses the
two designated elements of the alphabet, the payload width, and – rule by rule –
a guard, the two phases, the two payloads of the state, the two payloads of the
symbol, and the direction.

The three remaining fields are the machine's constants: its start state, its
accepting states, its blank, and the symbol the input channel writes in the cell
of each element (the register file of
`DescriptiveComplexity.Problems.Wide.Marks`). -/
structure Table (A R P K : Type) (c dd : ℕ) where
  /-- The designated element a track holds when its bit is clear. -/
  zero : A
  /-- The designated element a track holds when its bit is set. -/
  one : A
  /-- The two designated elements differ: what a track is read back by. -/
  zero_ne_one : zero ≠ one
  /-- The payload fits in the tuples of the universe. -/
  payload_le : c ≤ dd
  /-- Which data make the rule a transition. -/
  guard : R → (Fin c → A) → Prop
  /-- The phase a rule applies in. -/
  srcPh : R → P
  /-- The phase a rule moves to. -/
  dstPh : R → P
  /-- The pointer of the state a rule applies in. -/
  srcPl : R → (Fin c → A) → (Fin c → A)
  /-- The pointer of the state a rule moves to. -/
  dstPl : R → (Fin c → A) → (Fin c → A)
  /-- The tracks of the symbol a rule reads. -/
  readPl : R → (Fin c → A) → (Fin c → A)
  /-- The tracks of the symbol a rule writes. -/
  writePl : R → (Fin c → A) → (Fin c → A)
  /-- Whether a rule moves the head right. -/
  moveRight : R → Prop
  /-- The phase of the start state. -/
  startPh : P
  /-- The pointer of the start state. -/
  startPl : Fin c → A
  /-- Which states accept. -/
  accept : P → (Fin c → A) → Prop
  /-- The tracks of the blank. -/
  blankPl : Fin c → A
  /-- The tracks of the symbol the input channel writes in the cell of an
  element. -/
  markPl : Univ A R P K dd → (Fin c → A)
  /-- **Which elements the channel writes for.** Every one of them by default,
  which is what `DescriptiveComplexity.WideAccept`'s channel does; a program
  emitted into the *register* channel of
  `DescriptiveComplexity.WideRegAccept` restricts it, and the elements it leaves
  out have no register in the file the channel hands over. -/
  Marked : Univ A R P K dd → Prop := fun _ => True

namespace Table

variable {A R P K : Type} {c dd : ℕ} (T : Table A R P K c dd)

/-! ### The eleven relations, as predicates -/

/-- **Being a transition**: a `ctrl`-tagged element, canonically padded, whose
data the rule of its tag admits. The padding is what gives a transition one
spelling, and so the machine its determinism. -/
def IsTr : Univ A R P K dd → Prop := fun τ =>
  match τ.1 with
  | .ctrl r => IsPad c T.zero τ.2 ∧ T.guard r (unpad T.payload_le τ.2)
  | _ => False

/-- **The state a transition applies in**, read off its rule and its data. -/
def Src : Univ A R P K dd → Univ A R P K dd → Prop := fun τ q =>
  match τ.1 with
  | .ctrl r => q = stateElt T.zero (T.srcPh r) (T.srcPl r (unpad T.payload_le τ.2))
  | _ => False

/-- **The symbol a transition reads.** -/
def Read : Univ A R P K dd → Univ A R P K dd → Prop := fun τ a =>
  match τ.1 with
  | .ctrl r => a = symElt T.zero (T.readPl r (unpad T.payload_le τ.2))
  | _ => False

/-- **The state a transition moves to.** -/
def Dst : Univ A R P K dd → Univ A R P K dd → Prop := fun τ q =>
  match τ.1 with
  | .ctrl r => q = stateElt T.zero (T.dstPh r) (T.dstPl r (unpad T.payload_le τ.2))
  | _ => False

/-- **The symbol a transition writes.** -/
def Write : Univ A R P K dd → Univ A R P K dd → Prop := fun τ a =>
  match τ.1 with
  | .ctrl r => a = symElt T.zero (T.writePl r (unpad T.payload_le τ.2))
  | _ => False

/-- **Moving right**: a function of the rule alone, hence of the tag. -/
def IsRight : Univ A R P K dd → Prop := fun τ =>
  match τ.1 with
  | .ctrl r => T.moveRight r
  | _ => False

/-- **The start state.** -/
def IsStart : Univ A R P K dd → Prop := fun q => q = stateElt T.zero T.startPh T.startPl

/-- **The accepting states**: a `phase`-tagged, canonically padded element whose
phase and pointer the table accepts. -/
def IsAcc : Univ A R P K dd → Prop := fun q =>
  match q.1 with
  | .phase p => IsPad c T.zero q.2 ∧ T.accept p (unpad T.payload_le q.2)
  | _ => False

/-- **The blank.** -/
def IsBlank : Univ A R P K dd → Prop := fun a => a = symElt T.zero T.blankPl

/-- **The input channel**: the cell of an element the table writes for holds the
mark the table gives it. Functional on the nose, and total exactly on the
elements the table marks. -/
def Inp : Univ A R P K dd → Univ A R P K dd → Prop :=
  fun x a => T.Marked x ∧ a = symElt T.zero (T.markPl x)

/-! ### What a rule does

The five attributes of a transition, read at the element the rule and its data
name. Each is the definitional unfolding of the predicate above with
`DescriptiveComplexity.Draw.unpad_pad` applied to the payload, and together they
are the only thing a program ever needs about the table. -/

theorem isTr_trElt {r : R} {w : Fin c → A} (hg : T.guard r w) :
    T.IsTr (trElt (dd := dd) (K := K) (P := P) T.zero r w) := by
  refine ⟨isPad_pad, ?_⟩
  change T.guard r (unpad T.payload_le (pad T.zero w))
  rw [unpad_pad T.payload_le]
  exact hg

theorem isAcc_stateElt {p : P} {w : Fin c → A} (ha : T.accept p w) :
    T.IsAcc (stateElt (dd := dd) (K := K) (R := R) T.zero p w) := by
  refine ⟨isPad_pad, ?_⟩
  change T.accept p (unpad T.payload_le (pad T.zero w))
  rw [unpad_pad T.payload_le]
  exact ha

theorem src_trElt (r : R) (w : Fin c → A) :
    T.Src (trElt (dd := dd) (K := K) (P := P) T.zero r w)
      (stateElt T.zero (T.srcPh r) (T.srcPl r w)) := by
  change stateElt T.zero (T.srcPh r) (T.srcPl r w) =
    stateElt T.zero (T.srcPh r) (T.srcPl r (unpad T.payload_le (pad T.zero w)))
  rw [unpad_pad T.payload_le]

theorem read_trElt (r : R) (w : Fin c → A) :
    T.Read (trElt (dd := dd) (K := K) (P := P) T.zero r w)
      (symElt T.zero (T.readPl r w)) := by
  change symElt T.zero (T.readPl r w) =
    symElt T.zero (T.readPl r (unpad T.payload_le (pad T.zero w)))
  rw [unpad_pad T.payload_le]

theorem dst_trElt (r : R) (w : Fin c → A) :
    T.Dst (trElt (dd := dd) (K := K) (P := P) T.zero r w)
      (stateElt T.zero (T.dstPh r) (T.dstPl r w)) := by
  change stateElt T.zero (T.dstPh r) (T.dstPl r w) =
    stateElt T.zero (T.dstPh r) (T.dstPl r (unpad T.payload_le (pad T.zero w)))
  rw [unpad_pad T.payload_le]

theorem write_trElt (r : R) (w : Fin c → A) :
    T.Write (trElt (dd := dd) (K := K) (P := P) T.zero r w)
      (symElt T.zero (T.writePl r w)) := by
  change symElt T.zero (T.writePl r w) =
    symElt T.zero (T.writePl r (unpad T.payload_le (pad T.zero w)))
  rw [unpad_pad T.payload_le]

theorem isRight_trElt {r : R} (w : Fin c → A) (hd : T.moveRight r) :
    T.IsRight (trElt (dd := dd) (K := K) (P := P) T.zero r w) := hd

theorem not_isRight_trElt {r : R} (w : Fin c → A) (hd : ¬T.moveRight r) :
    ¬T.IsRight (trElt (dd := dd) (K := K) (P := P) T.zero r w) := hd

/-! ### An instance that reads the table -/

variable [LinearOrder R] [LinearOrder P] [LinearOrder K] [LinearOrder A]

/-- **An instance reads the table**: its eleven relations are the predicates
above and its order is the definable one. Everything a program proves is proved
under this hypothesis, so the interpretation that emits the instance has exactly
eleven obligations and no more. -/
structure Reads [Language.wide.Structure (Univ A R P K dd)] : Prop where
  /-- The order is the block-major one on tagged tuples. -/
  le : ∀ x y : Univ A R P K dd, WMLe x y ↔ tagTupleLe x y
  /-- The transitions. -/
  tr : ∀ τ : Univ A R P K dd, WMTr τ ↔ T.IsTr τ
  /-- The start state. -/
  start : ∀ q : Univ A R P K dd, WMStart q ↔ T.IsStart q
  /-- The accepting states. -/
  acc : ∀ q : Univ A R P K dd, WMAcc q ↔ T.IsAcc q
  /-- The blank. -/
  blank : ∀ a : Univ A R P K dd, WMBlank a ↔ T.IsBlank a
  /-- The direction. -/
  right : ∀ τ : Univ A R P K dd, WMRight τ ↔ T.IsRight τ
  /-- The state a transition applies in. -/
  src : ∀ τ q : Univ A R P K dd, WMSrc τ q ↔ T.Src τ q
  /-- The symbol a transition reads. -/
  read : ∀ τ a : Univ A R P K dd, WMRead τ a ↔ T.Read τ a
  /-- The state a transition moves to. -/
  dst : ∀ τ q : Univ A R P K dd, WMDst τ q ↔ T.Dst τ q
  /-- The symbol a transition writes. -/
  write : ∀ τ a : Univ A R P K dd, WMWrite τ a ↔ T.Write τ a
  /-- The input channel. -/
  inp : ∀ x a : Univ A R P K dd, WMInp x a ↔ T.Inp x a

/-! ### Firing a rule

The shape every subroutine of the address layer asks for – a transition with its
six attributes, the direction being the one the caller wants. A program's whole
interaction with the table is these two theorems. -/

variable [Language.wide.Structure (Univ A R P K dd)]

/-- **A rule fires, moving right.** -/
theorem fire_right (hR : T.Reads) {r : R} {w : Fin c → A} (hg : T.guard r w)
    (hd : T.moveRight r) {q a q' a' : Univ A R P K dd}
    (hq : q = stateElt T.zero (T.srcPh r) (T.srcPl r w))
    (ha : a = symElt T.zero (T.readPl r w))
    (hq' : q' = stateElt T.zero (T.dstPh r) (T.dstPl r w))
    (ha' : a' = symElt T.zero (T.writePl r w)) :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q' ∧ WMWrite τ a' ∧
      WMRight τ := by
  subst hq; subst ha; subst hq'; subst ha'
  exact ⟨trElt T.zero r w, (hR.tr _).mpr (T.isTr_trElt hg), (hR.src _ _).mpr (T.src_trElt r w),
    (hR.read _ _).mpr (T.read_trElt r w), (hR.dst _ _).mpr (T.dst_trElt r w),
    (hR.write _ _).mpr (T.write_trElt r w), (hR.right _).mpr (T.isRight_trElt w hd)⟩

/-- **A rule fires, moving left.** -/
theorem fire_left (hR : T.Reads) {r : R} {w : Fin c → A} (hg : T.guard r w)
    (hd : ¬T.moveRight r) {q a q' a' : Univ A R P K dd}
    (hq : q = stateElt T.zero (T.srcPh r) (T.srcPl r w))
    (ha : a = symElt T.zero (T.readPl r w))
    (hq' : q' = stateElt T.zero (T.dstPh r) (T.dstPl r w))
    (ha' : a' = symElt T.zero (T.writePl r w)) :
    ∃ τ : Univ A R P K dd, WMTr τ ∧ WMSrc τ q ∧ WMRead τ a ∧ WMDst τ q' ∧ WMWrite τ a' ∧
      ¬WMRight τ := by
  subst hq; subst ha; subst hq'; subst ha'
  exact ⟨trElt T.zero r w, (hR.tr _).mpr (T.isTr_trElt hg), (hR.src _ _).mpr (T.src_trElt r w),
    (hR.read _ _).mpr (T.read_trElt r w), (hR.dst _ _).mpr (T.dst_trElt r w),
    (hR.write _ _).mpr (T.write_trElt r w),
    fun hc => T.not_isRight_trElt w hd ((hR.right _).mp hc)⟩

/-! ### The two promises -/

/-- **The order of the emitted instance is linear**, being the definable order on
tagged tuples. -/
theorem isLinOrd_wmLe (hR : T.Reads) : IsLinOrd (WMLe (A := Univ A R P K dd)) := by
  have h := Wide.isLinOrd_tagTupleLe (Tag := Tag R P K) (d := dd) (A := A)
  exact ⟨fun x => (hR.le x x).mpr (h.1 x),
    fun x y z h1 h2 => (hR.le x z).mpr (h.2.1 x y z ((hR.le x y).mp h1) ((hR.le y z).mp h2)),
    fun x y h1 h2 => h.2.2.1 x y ((hR.le x y).mp h1) ((hR.le y x).mp h2),
    fun x y => (h.2.2.2 x y).imp (hR.le x y).mpr (hR.le y x).mpr⟩

variable [Finite A] [Finite R] [Finite P] [Finite K]

/-- **The emitted instance is well formed.** Three conditions
(`DescriptiveComplexity.wideData_wellFormed_iff`), and all three are settled by
the layout: the order is `DescriptiveComplexity.tagTupleLe`, and the input and
the blank are equations. -/
theorem wellFormed (hR : T.Reads) : (wideData (Univ A R P K dd)).WellFormed :=
  wideData_wellFormed_iff.mpr
    ⟨T.isLinOrd_wmLe hR,
      fun _x _a _b ha hb => (((hR.inp _ _).mp ha).2).trans (((hR.inp _ _).mp hb).2).symm,
      ⟨symElt T.zero T.blankPl, (hR.blank _).mpr rfl⟩,
      fun _a _b ha hb => ((hR.blank _).mp ha).trans ((hR.blank _).mp hb).symm⟩

/-- **The separation condition**: two guarded rules that apply in the same state
and read the same symbol are the same rule with the same data. This is the whole
content of determinism, and the only obligation a concrete table has to discharge
by hand. -/
def Sep : Prop :=
  ∀ (r r' : R) (w w' : Fin c → A), T.guard r w → T.guard r' w' →
    T.srcPh r = T.srcPh r' → T.srcPl r w = T.srcPl r' w' →
    T.readPl r w = T.readPl r' w' → r = r' ∧ w = w'

/-- **The separation condition, asked at some phases only**: two guarded rules
that apply in the same state and read the same symbol are the same rule with the
same data, provided the phase they apply in is one `Ph` names.

A program that guesses does not separate everywhere – that is what guessing is –
but it separates at every phase it can be in once the guess is over, and
`DescriptiveComplexity.TMData.uniqueFrom_of_invariant` asks for no more. -/
def SepOn (Ph : P → Prop) : Prop :=
  ∀ (r r' : R) (w w' : Fin c → A), Ph (T.srcPh r) → T.guard r w → T.guard r' w' →
    T.srcPh r = T.srcPh r' → T.srcPl r w = T.srcPl r' w' →
    T.readPl r w = T.readPl r' w' → r = r' ∧ w = w'

omit [LinearOrder R] [LinearOrder P] [LinearOrder K] [LinearOrder A]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- Separating everywhere is separating at every phase. -/
theorem sepOn_of_sep (hsep : T.Sep) (Ph : P → Prop) : T.SepOn Ph :=
  fun r r' w w' _ hg hg' => hsep r r' w w' hg hg'

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The transition is pinned wherever the phases separate**: at a state whose
phase satisfies `Ph`, the state and the symbol read name the transition. This is
the hypothesis of `DescriptiveComplexity.TMData.step_functional_at`, and with it
a guessing program is functional off its guess. -/
theorem tr_unique_of_sepOn (hR : T.Reads) {Ph : P → Prop} (hsep : T.SepOn Ph)
    {q a : Univ A R P K dd}
    (hq : ∀ (p : P) (f : Fin c → A), q = stateElt T.zero p f → Ph p) :
    ∀ τ σ : Univ A R P K dd, WMTr τ → WMTr σ → WMSrc τ q → WMSrc σ q →
      WMRead τ a → WMRead σ a → τ = σ := by
  rintro ⟨t, v⟩ ⟨t', v'⟩ htr htr' hsrc hsrc' hread hread'
  rw [hR.tr] at htr htr'
  rw [hR.src] at hsrc hsrc'
  rw [hR.read] at hread hread'
  match t, t' with
  | .ctrl r, .ctrl r' =>
    obtain ⟨hpad, hg⟩ := htr
    obtain ⟨hpad', hg'⟩ := htr'
    have hst := stateElt_inj T.payload_le (hsrc.symm.trans hsrc')
    have hsy := symElt_inj T.payload_le (hread.symm.trans hread')
    obtain ⟨rfl, hw⟩ := hsep r r' _ _ (hq _ _ hsrc) hg hg' hst.1 hst.2 hsy
    have hpv : IsPad c T.zero v := hpad
    have hpv' : IsPad c T.zero v' := hpad'
    have hu : unpad T.payload_le v = unpad T.payload_le v' := hw
    have hvv : v = v' := by
      rw [← pad_unpad T.payload_le hpv, ← pad_unpad T.payload_le hpv', hu]
    exact congrArg (fun u => ((Tag.ctrl r : Tag R P K), u)) hvv

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **A transition has one destination**: it is an equation in the rule. -/
theorem dst_functional (hR : T.Reads) :
    ∀ τ q q' : Univ A R P K dd, WMDst τ q → WMDst τ q' → q = q' := by
  rintro ⟨t, v⟩ q q' hq hq'
  rw [hR.dst] at hq hq'
  match t with
  | .ctrl _ => exact hq.trans hq'.symm

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **A transition writes one symbol**: it is an equation in the rule. -/
theorem write_functional (hR : T.Reads) :
    ∀ τ a a' : Univ A R P K dd, WMWrite τ a → WMWrite τ a' → a = a' := by
  rintro ⟨t, v⟩ a a' ha ha'
  rw [hR.write] at ha ha'
  match t with
  | .ctrl _ => exact ha.trans ha'.symm

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The emitted instance is deterministic**, given the separation condition.
The three other clauses of `DescriptiveComplexity.WideDet` are free: the start
state, the destination and the written symbol are all written as equations. -/
theorem deterministic (hR : T.Reads) (hsep : T.Sep) :
    (wideData (Univ A R P K dd)).Deterministic := by
  refine wideData_deterministic_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact fun _q _q' hq hq' => ((hR.start _).mp hq).trans ((hR.start _).mp hq').symm
  · rintro ⟨t, v⟩ ⟨t', v'⟩ q a htr htr' hsrc hsrc' hread hread'
    rw [hR.tr] at htr htr'
    rw [hR.src] at hsrc hsrc'
    rw [hR.read] at hread hread'
    match t, t' with
    | .ctrl r, .ctrl r' =>
      obtain ⟨hpad, hg⟩ := htr
      obtain ⟨hpad', hg'⟩ := htr'
      have hst := stateElt_inj T.payload_le (hsrc.symm.trans hsrc')
      have hsy := symElt_inj T.payload_le (hread.symm.trans hread')
      obtain ⟨rfl, hw⟩ := hsep r r' _ _ hg hg' hst.1 hst.2 hsy
      have hpv : IsPad c T.zero v := hpad
      have hpv' : IsPad c T.zero v' := hpad'
      have hu : unpad T.payload_le v = unpad T.payload_le v' := hw
      have hvv : v = v' := by
        rw [← pad_unpad T.payload_le hpv, ← pad_unpad T.payload_le hpv', hu]
      exact congrArg (fun u => ((Tag.ctrl r : Tag R P K), u)) hvv
  · rintro ⟨t, v⟩ q q' hq hq'
    rw [hR.dst] at hq hq'
    match t with
    | .ctrl _ => exact hq.trans hq'.symm
  · rintro ⟨t, v⟩ a a' ha ha'
    rw [hR.write] at ha ha'
    match t with
    | .ctrl _ => exact ha.trans ha'.symm

/-! ### The bounds of the outer loop

`DescriptiveComplexity.Draw.wmSetLe_logicalTop` is about the block-major order on
tagged tuples; a program's loop is about the order its *instance* carries. They are
the same order, which is what the layout was chosen for, and this is where the two
are joined. -/

omit [LinearOrder R] [LinearOrder P] [LinearOrder K] [LinearOrder A]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- The order on addresses depends on the order of the elements only through its
extension. -/
theorem wmSetLe_congr_rel {α : Type} {Le Le' : α → α → Prop} (h : ∀ x y, Le x y ↔ Le' x y)
    (s u : α → Prop) : WMSetLe Le s u ↔ WMSetLe Le' s u := by
  refine or_congr Iff.rfl (exists_congr fun x => and_congr_left fun _ => ?_)
  exact forall_congr' fun y => imp_congr (and_congr (h y x) (not_congr (h x y))) Iff.rfl

/-- **A logical address is at or below the last one**, in the machine's own order:
the addresses whose non-argument blocks are empty – the ones that hold the stage of
the fixed point – are an initial interval of the tape, and this is the upper bound
`DescriptiveComplexity.reaches_of_wideRounds` is given. -/
theorem wmSetLe_logicalTop_reads (hR : T.Reads) {s : Univ A R P K dd → Prop}
    (hjunk : ∀ τ : Tag R P K, (∀ i : K, τ ≠ Tag.arg i) → ∀ v : Fin dd → A, ¬s (τ, v)) :
    WMSetLe WMLe s logicalTop := by
  refine (wmSetLe_congr_rel ?_ s logicalTop).mpr
    (wmSetLe_logicalTop Wide.isLinOrd_tupLeLex hjunk)
  intro x y
  rw [hR.le, Wide.tagTupleLe_iff_lexRel]

/-- **The empty address is the bottom of the tape**, which is the lower bound of the
same loop and where the head starts. -/
theorem wmSetLe_bot (hR : T.Reads) (s : Univ A R P K dd → Prop) :
    WMSetLe WMLe (fun _ => False) s :=
  wmSetLe_of_empty (T.isLinOrd_wmLe hR) (fun _ hc => hc) s

/-! ### The two ends of a run

What a program starts from and what it has to reach, in the table's own terms.
Between them and `DescriptiveComplexity.Draw.Table.fire_right` /
`DescriptiveComplexity.Draw.Table.fire_left`, a program never mentions
`FirstOrder.Language.wide` again. -/

/-- **The initial configuration of the emitted machine**: the start state, the
head on the empty address, the mark of each element in that element's cell and the
blank everywhere else. -/
theorem isInit (hR : T.Reads) (hmk : ∀ x : Univ A R P K dd, T.Marked x)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, f (wmSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop, (∀ x : Univ A R P K dd, s ≠ wmSeg x) →
      f s = symElt T.zero T.blankPl) :
    (wideData (Univ A R P K dd)).IsInit
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ :=
  isInit_wideTape (T.isLinOrd_wmLe hR) ((hR.blank _).mpr rfl)
    (fun x => (hR.inp x _).mpr ⟨hmk x, rfl⟩) hmark hrest ((hR.start _).mpr rfl)

/-- **The emitted machine accepts in bounded space**: it starts as
`DescriptiveComplexity.Draw.Table.isInit` says, roams, and ends in a state the
table accepts. -/
theorem acceptsSpace (hR : T.Reads) (hmk : ∀ x : Univ A R P K dd, T.Marked x)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, f (wmSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop, (∀ x : Univ A R P K dd, s ≠ wmSeg x) →
      f s = symElt T.zero T.blankPl)
    {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ cfg)
    {p : P} {w : Fin c → A} (hstate : cfg.state = Sum.inr (stateElt T.zero p w))
    (ha : T.accept p w) :
    (wideData (Univ A R P K dd)).AcceptsSpace :=
  acceptsSpace_of_wideTape (T.isLinOrd_wmLe hR) ((hR.blank _).mpr rfl)
    (fun x => (hR.inp x _).mpr ⟨hmk x, rfl⟩) hmark hrest ((hR.start _).mpr rfl) hreach hstate
    ((hR.acc _).mpr (T.isAcc_stateElt ha))

/-- **The emitted machine accepts on the clock**: it starts as
`DescriptiveComplexity.Draw.Table.isInit` says, runs for fewer steps than there
are addresses – `2 ^ n` of them, `n` the size of the drawn universe – and ends in
a state the table accepts. This is the reading a *time*-bounded reduction needs,
where `DescriptiveComplexity.Draw.Table.acceptsSpace` is the space-bounded one. -/
theorem accepts (hR : T.Reads) (hmk : ∀ x : Univ A R P K dd, T.Marked x)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, f (wmSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop, (∀ x : Univ A R P K dd, s ≠ wmSeg x) →
      f s = symElt T.zero T.blankPl)
    {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {w : Fin c → A} (hstate : cfg.state = Sum.inr (stateElt T.zero p w))
    (ha : T.accept p w) :
    (wideData (Univ A R P K dd)).Accepts :=
  accepts_of_wideTape_lt_two_pow (T.isLinOrd_wmLe hR) ((hR.blank _).mpr rfl)
    (fun x => (hR.inp x _).mpr ⟨hmk x, rfl⟩) hmark hrest ((hR.start _).mpr rfl) hreach hlt hstate
    ((hR.acc _).mpr (T.isAcc_stateElt ha))

/-- **The emitted instance is a yes-instance of
`DescriptiveComplexity.WideAccept`**, which is what a *nondeterministic*
time-bounded reduction has to produce: well-formedness and an accepting run
within the clock. Determinism is not asked for, so a program that guesses is
served by this and not by
`DescriptiveComplexity.Draw.Table.dwideAcceptSpace`. -/
theorem wideAccept (hR : T.Reads) (hmk : ∀ x : Univ A R P K dd, T.Marked x)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, f (wmSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop, (∀ x : Univ A R P K dd, s ≠ wmSeg x) →
      f s = symElt T.zero T.blankPl)
    {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {w : Fin c → A} (hstate : cfg.state = Sum.inr (stateElt T.zero p w))
    (ha : T.accept p w) :
    WideAccept (Univ A R P K dd) :=
  ⟨T.wellFormed hR, T.accepts hR hmk hmark hrest hreach hlt hstate ha⟩

/-- **The emitted instance is a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`**, which is what a reduction has to
produce: the two promises and an accepting run. -/
theorem dwideAcceptSpace (hR : T.Reads) (hsep : T.Sep)
    (hmk : ∀ x : Univ A R P K dd, T.Marked x)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, f (wmSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop, (∀ x : Univ A R P K dd, s ≠ wmSeg x) →
      f s = symElt T.zero T.blankPl)
    {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ cfg)
    {p : P} {w : Fin c → A} (hstate : cfg.state = Sum.inr (stateElt T.zero p w))
    (ha : T.accept p w) :
    DWideAcceptSpace (Univ A R P K dd) :=
  ⟨T.wellFormed hR, T.deterministic hR hsep,
    T.acceptsSpace hR hmk hmark hrest hreach hstate ha⟩

end Table

end Draw

end DescriptiveComplexity
