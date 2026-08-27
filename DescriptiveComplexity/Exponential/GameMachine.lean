/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameCtrl
import DescriptiveComplexity.MachinesAltSpace
import DescriptiveComplexity.Problems.Machine.Walk

/-!
# The machine of a second-order game

The alternating machine emitted by `SO-GAME ≤ʳᶠᵒ[≤] ATMAcceptSpace`, assembled
on the tape of `DescriptiveComplexity.Exponential.GameTape` with the phases of
`DescriptiveComplexity.Exponential.GameCtrl`.

## The shape of a transition

A transition is an *element* of the emitted universe, so it carries a tag and a
tuple. The tag is `DescriptiveComplexity.TrTag`: the phase it applies in, the
phase it moves to, the symbol it reads, the symbol it writes, and its
direction. The tuple carries, in one piece,

```
  coordinates 0 … V-1        the valuation of the question's variables
  coordinates V … V+a-1      the address of the cell the symbol sits in
```

which is what makes every relation of
`DescriptiveComplexity.TMData` first-order and uniform:

* `Src` and `Dst` read the valuation, each **up to the arity its own phase
  declares** – so a step of the prefix, whose destination declares one more
  variable than its source, writes exactly one coordinate, and the existential
  quantification over transitions *is* the quantification over the value
  written;
* `Read` and `Write` read the address, and a symbol shape together with an
  address is a point (`DescriptiveComplexity.symPt`).

Everything specific to the machine is therefore confined to one predicate, the
**rule** `DescriptiveComplexity.TrTag → (Fin dim → A) → Prop` saying which
tagged transitions are real. This file takes it as a parameter and proves what
does not depend on it: the two promises `ATMAcceptSpace` folds into its
yes-instances.

## The two promises are rule-independent

`DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksSplit` are proved here once and for all
(`DescriptiveComplexity.gameMachine_wellFormed`,
`DescriptiveComplexity.gameMachine_blocksSplit`), because neither mentions the
transitions: the first is about the order, the positions, the input and the
blank – all fixed by the layout – and the second is about the marks, which are
`DescriptiveComplexity.MachPh.IsUniv` read off the phase.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

/-! ### Symbols, as a shape and an address -/

/-- **The shape of a symbol**: a sentinel's mark, or a cell's bit together with
the region and relation variable of the cell it sits in. The address itself is
carried by the transition's tuple, not by the shape. -/
inductive SymTag (B : SOBlock) : Type
  /-- A sentinel's mark. -/
  | mark (b : Bool)
  /-- The bit `b` in a cell of region `r` holding the relation variable `i`. -/
  | val (b r : Bool) (i : B.ι)

namespace SymTag

variable {B : SOBlock}

/-- The symbol shapes as a sum, for the `Finite` instance. -/
def equivSum : SymTag B ≃ Bool ⊕ (Bool × Bool × B.ι) where
  toFun
    | .mark b => .inl b
    | .val b r i => .inr (b, r, i)
  invFun
    | .inl b => .mark b
    | .inr (b, r, i) => .val b r i
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _, _⟩ <;> rfl

instance : Finite (SymTag B) := Finite.of_equiv _ equivSum.symm

end SymTag

/-! ### The dimension, and the two halves of a tuple -/

variable (B : SOBlock) in
/-- The dimension of the emitted universe: room for the valuation of a
question's variables, and for the address of a cell. -/
noncomputable def gameDim (V : ℕ) : ℕ := V + blockArityBound B

theorem blockArityBound_le_gameDim (B : SOBlock) (V : ℕ) :
    blockArityBound B ≤ gameDim B V := by
  simp [gameDim]

theorem le_gameDim (B : SOBlock) (V : ℕ) : V ≤ gameDim B V := by
  simp [gameDim]

section Address

variable {B : SOBlock} {V : ℕ} {A : Type}

/-- The address half of a transition's tuple. -/
noncomputable def addrOf (w : Fin (gameDim B V) → A) : Fin (blockArityBound B) → A :=
  fun l => w ⟨V + (l : ℕ), by have := l.isLt; simp only [gameDim]; omega⟩

/-- The address a symbol shape reads, truncated to the arity of its relation
variable. -/
noncomputable def argsOf (i : B.ι) (ā : Fin (blockArityBound B) → A) : Fin (B.arity i) → A :=
  fun l => ā (Fin.castLE (arity_le_blockArityBound B i) l)

variable [LinearOrder A] (a₀ : A)

/-- **The tuple of a transition**, from the valuation it carries and the
address it reads: the two halves, side by side. -/
noncomputable def joinTuple (v : Fin V → A) (ā : Fin (blockArityBound B) → A) :
    Fin (gameDim B V) → A := fun k =>
  if h : (k : ℕ) < V then v ⟨k, h⟩
  else ā ⟨(k : ℕ) - V, by have := k.isLt; simp only [gameDim] at this; omega⟩

omit [LinearOrder A] in
theorem joinTuple_of_lt (v : Fin V → A) (ā : Fin (blockArityBound B) → A)
    {k : Fin (gameDim B V)} (h : (k : ℕ) < V) : joinTuple v ā k = v ⟨k, h⟩ := by
  rw [joinTuple, dif_pos h]

omit [LinearOrder A] in
/-- **The address of a cell, read as a symbol's address.** -/
theorem argsOf_pad (a₀ : A) (i : B.ι) (ā : Fin (B.arity i) → A) :
    argsOf (B := B) i (pad a₀ ā) = ā := by
  funext l
  simp only [argsOf, pad]
  rw [dif_pos (show ((Fin.castLE (arity_le_blockArityBound B i) l : Fin _) : ℕ) < B.arity i from
    l.isLt)]
  exact congrArg ā (Fin.ext rfl)

omit [LinearOrder A] in
@[simp] theorem addrOf_joinTuple (v : Fin V → A) (ā : Fin (blockArityBound B) → A) :
    addrOf (joinTuple v ā) = ā := by
  funext l
  rw [addrOf, joinTuple, dif_neg (by simp)]
  exact congrArg ā (Fin.ext (by simp))

/-- **The tuple a walk step carries**: the valuation its phase already holds,
and the address of the cell it is reading. The first half is what `Src` and
`Dst` compare against the state, the second what `Read` and `Write` turn into a
symbol. -/
noncomputable def walkTuple (v : Fin (gameDim B V) → A) (ā : Fin (blockArityBound B) → A) :
    Fin (gameDim B V) → A := joinTuple (pref (le_gameDim B V) v) ā

omit [LinearOrder A] in
@[simp] theorem addrOf_walkTuple (v : Fin (gameDim B V) → A)
    (ā : Fin (blockArityBound B) → A) : addrOf (walkTuple v ā) = ā :=
  addrOf_joinTuple _ _

omit [LinearOrder A] in
/-- **A walk step agrees with its own state**: it carries the valuation the
phase declares, whatever the address it is reading. -/
theorem agree_walkTuple {m : ℕ} (hm : m ≤ V) (v : Fin (gameDim B V) → A)
    (ā : Fin (blockArityBound B) → A) : Agree m (walkTuple v ā) v := by
  intro j hj
  rw [walkTuple, joinTuple_of_lt _ _ (by omega)]
  exact congrArg v (Fin.ext rfl)

/-- **The valuation a phase keeps**: the tuple of the transition entering it,
truncated to the coordinates the phase declares and pinned to the minimum
elsewhere. This is the destination state a control step builds – any tuple with
the same two properties would do, and this is the canonical one. -/
noncomputable def truncTuple (a₀ : A) (m : ℕ) {D : ℕ} (w : Fin D → A) : Fin D → A :=
  fun j => if (j : ℕ) < m then w j else a₀

omit [LinearOrder A] in
theorem agree_truncTuple (a₀ : A) (m : ℕ) {D : ℕ} (w : Fin D → A) :
    Agree m w (truncTuple a₀ m w) := fun _j hj => if_pos hj

theorem canon_truncTuple {a₀ : A} (h₀ : IsBot a₀) (m : ℕ) {D : ℕ} (w : Fin D → A) :
    Canon m (truncTuple a₀ m w) := by
  intro j hj
  rw [truncTuple, if_neg (by omega)]
  exact h₀

omit [LinearOrder A] in
/-- A phase that declares nothing keeps the constant tuple. -/
@[simp] theorem truncTuple_zero (a₀ : A) {D : ℕ} (w : Fin D → A) :
    truncTuple a₀ 0 w = fun _ => a₀ := by
  funext j
  rw [truncTuple, if_neg (by omega)]

/-- **And it is the only such tuple**: a state's tuple is determined by the
transition that entered it, because the domain pins everything the phase does
not declare. -/
theorem eq_truncTuple {a₀ : A} (h₀ : IsBot a₀) {m D : ℕ} {w x : Fin D → A}
    (hc : Canon m x) (ha : Agree m w x) : x = truncTuple a₀ m w := by
  funext j
  by_cases hj : (j : ℕ) < m
  · rw [truncTuple, if_pos hj]
    exact ha j hj
  · rw [truncTuple, if_neg hj]
    exact le_antisymm (hc j (by omega) a₀) (h₀ _)

/-- **One step of a prefix writes exactly one coordinate**: the tuple the next
phase keeps is the one it came from, updated at the coordinate just declared.
This is the whole of the arithmetic the prefix costs. -/
theorem truncTuple_succ {a₀ : A} (h₀ : IsBot a₀) {m D : ℕ} {vv w : Fin D → A} (hm : m < D)
    (hc : Canon m vv) (ha : Agree m w vv) :
    truncTuple a₀ (m + 1) w = Function.update vv ⟨m, hm⟩ (w ⟨m, hm⟩) := by
  funext k
  by_cases hk : (k : ℕ) < m + 1
  · rw [truncTuple, if_pos hk]
    by_cases hkm : (k : ℕ) = m
    · rw [show k = (⟨m, hm⟩ : Fin D) from Fin.ext hkm, Function.update_self]
    · rw [Function.update_of_ne (fun hc => hkm (congrArg Fin.val hc)), ha k (by omega)]
  · rw [truncTuple, if_neg hk,
      Function.update_of_ne (fun hc => absurd (congrArg Fin.val hc : (k : ℕ) = m) (by omega))]
    exact le_antisymm (h₀ (vv k)) (hc k (by omega) a₀)

omit [LinearOrder A] in
/-- **Updating a coordinate commutes with taking a prefix**, when the
coordinate is in the prefix. -/
theorem pref_update {D m : ℕ} (h : m ≤ D) {vv : Fin D → A} {j : ℕ} (hjD : j < D)
    (hjm : j < m) (a : A) :
    pref h (Function.update vv ⟨j, hjD⟩ a) = Function.update (pref h vv) ⟨j, hjm⟩ a := by
  funext l
  by_cases hl : (l : ℕ) = j
  · have h1 : l = (⟨j, hjm⟩ : Fin m) := Fin.ext hl
    have h2 : (Fin.castLE h (⟨j, hjm⟩ : Fin m) : Fin D) = ⟨j, hjD⟩ := Fin.ext rfl
    simp only [pref, h1, h2, Function.update_self]
  · have h1 : l ≠ (⟨j, hjm⟩ : Fin m) := fun hc => hl (congrArg Fin.val hc)
    have h2 : (Fin.castLE h l : Fin D) ≠ ⟨j, hjD⟩ := fun hc => hl (congrArg Fin.val hc)
    simp only [pref, Function.update_of_ne h1, Function.update_of_ne h2]

/-- **A symbol shape at an address is a point.** -/
noncomputable def gameSymPt {C : Type} (s : SymTag B) (ā : Fin (blockArityBound B) → A) :
    Pt B C (gameDim B V) A :=
  match s with
  | .mark b => markPt a₀ b
  | .val b r i => valPt a₀ b r i (argsOf i ā)

omit [LinearOrder A] in
theorem gameSymPt_val {C : Type} (b r : Bool) (i : B.ι) (ā : Fin (blockArityBound B) → A) :
    gameSymPt (C := C) (V := V) a₀ (.val b r i) ā = valPt a₀ b r i (argsOf i ā) := rfl

omit [LinearOrder A] in
theorem gameSymPt_mark {C : Type} (b : Bool) (ā : Fin (blockArityBound B) → A) :
    gameSymPt (C := C) (V := V) a₀ (.mark b) ā = markPt a₀ b := rfl

end Address

/-! ### The tags of the machine -/

/-- **The tag of a transition**: where it applies, where it goes, what it reads
and writes, and which way it moves. -/
structure TrTag (B : SOBlock) (V M : ℕ) : Type where
  /-- The phase the transition applies in. -/
  src : MachPh V M
  /-- The phase it moves to. -/
  dst : MachPh V M
  /-- The symbol it reads. -/
  rd : SymTag B
  /-- The symbol it writes. -/
  wr : SymTag B
  /-- Whether it moves the head right. -/
  right : Bool

namespace TrTag

variable {B : SOBlock} {V M : ℕ}

/-- A transition tag as a tuple, for the `Finite` instance. -/
def toProd (t : TrTag B V M) : MachPh V M × MachPh V M × SymTag B × SymTag B × Bool :=
  (t.src, t.dst, t.rd, t.wr, t.right)

theorem toProd_injective : Function.Injective (toProd (B := B) (V := V) (M := M)) := by
  intro a b h
  simp only [toProd, Prod.mk.injEq] at h
  cases a; cases b
  simp_all

instance : Finite (TrTag B V M) := Finite.of_injective _ toProd_injective

end TrTag

/-- **The control's tags**: the phases, which are the states, and the rules,
which are the transitions. -/
abbrev GameCtrlTag (B : SOBlock) (V M : ℕ) : Type := MachPh V M ⊕ TrTag B V M

/-- **The tags of the emitted machine**: the tape's, and the control's. -/
abbrev GameTag (B : SOBlock) (V M : ℕ) : Type := MachTag B (GameCtrlTag B V M)

/-- The coordinates a control tag uses: a phase declares its own, a transition
uses the whole tuple. -/
noncomputable def ctrlArity (vars : GameQuestion → ℕ) {B : SOBlock} {V M : ℕ} :
    GameCtrlTag B V M → ℕ :=
  Sum.elim (MachPh.arity vars) fun _ => gameDim B V

/-! ### The machine -/

section Machine

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  (vars : GameQuestion → ℕ) (pol : GameQuestion → ℕ → Bool) (a₀ : A)

/-- A point of the emitted universe. -/
abbrev GamePt (B : SOBlock) (V M : ℕ) (A : Type) : Type :=
  Pt B (GameCtrlTag B V M) (gameDim B V) A

/-- The point of a phase, at a given valuation. -/
noncomputable def phasePt (p : MachPh V M) (w : Fin (gameDim B V) → A) : GamePt B V M A :=
  (Sum.inr (Sum.inl p), w)

/-- A state belongs to the universal player exactly when its phase does. -/
noncomputable def isUnivPt (p : GamePt B V M A) : Prop :=
  match p.1 with
  | Sum.inr (Sum.inl ph) => MachPh.IsUniv pol ph = true
  | _ => False

variable (V M) in
/-- The state the machine starts in: the initial sweep, writing region `0`. -/
def startPh : MachPh V M := MachPh.sweepPh false false .start false

/-- **The machine of a second-order game**, with its rules as a parameter. -/
noncomputable def gameMachine (hdim : blockArityBound B ≤ gameDim B V)
    (rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop) :
    ATMData (GamePt B V M A) :=
  letI := machTagOrder (B := B) (C := GameCtrlTag B V M)
  { Posn p := machPosn p ∧ machDom (ctrlArity vars) p
    Le := tagTupleLe
    Tr p := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ rule t p.2
    Start p := p = phasePt (startPh V M) fun _ => a₀
    Acc p := ∃ ph : MachPh V M, p.1 = Sum.inr (Sum.inl ph) ∧ ph.kind = .acc
    Blank p := p = markPt a₀ false
    Right p := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ t.right = true
    Src p q := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧
      q.1 = Sum.inr (Sum.inl t.src) ∧ Canon (MachPh.arity vars t.src) q.2 ∧
        Agree (MachPh.arity vars t.src) p.2 q.2
    Read p x := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ x = gameSymPt a₀ t.rd (addrOf p.2)
    Dst p q := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧
      q.1 = Sum.inr (Sum.inl t.dst) ∧ Canon (MachPh.arity vars t.dst) q.2 ∧
        Agree (MachPh.arity vars t.dst) p.2 q.2
    Write p x := ∃ t : TrTag B V M, p.1 = Sum.inr (Sum.inr t) ∧ x = gameSymPt a₀ t.wr (addrOf p.2)
    Inp := machInp a₀ hdim
    Blk j p := (j = 1 ∧ isUnivPt pol p) ∨ (j = 0 ∧ ¬ isUnivPt pol p) }

/-! ### The two promises -/

variable {vars pol a₀}

/-- The tape order is linear on the whole universe, which is what
`DescriptiveComplexity.TMData.WellFormed` asks of it. -/
theorem isLinOrd_gameLe :
    letI := machTagOrder (B := B) (C := GameCtrlTag B V M)
    IsLinOrd (tagTupleLe (Tag := GameTag B V M) (d := gameDim B V) (A := A)) := by
  let := machTagOrder (B := B) (C := GameCtrlTag B V M)
  let := tagTupleOrder (Tag := GameTag B V M) (d := gameDim B V) (A := A)
  have heq : (tagTupleLe (Tag := GameTag B V M) (d := gameDim B V) (A := A)) =
      (tagTupleOrder : LinearOrder (GameTag B V M × (Fin (gameDim B V) → A))).le := by
    funext p q
    exact propext (tagTupleLe_iff_le p q)
  rw [heq]
  exact isLinOrd_le

/-- **The machine is well formed**, whatever its rules: the order is linear,
there is a position, the input is functional and total, and there is exactly
one blank. -/
theorem gameMachine_wellFormed (hdim : blockArityBound B ≤ gameDim B V)
    (rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop) (h₀ : IsBot a₀) :
    (gameMachine vars pol a₀ hdim rule).toTMData.WellFormed := by
  refine ⟨isLinOrd_gameLe, ⟨leftPt a₀ false, trivial, fun _ _ => h₀⟩, ?_,
    ⟨markPt a₀ false, rfl⟩, ?_⟩
  · exact fun _ _ _ ha hb => machInp_functional ha hb
  · exact fun _ _ ha hb => ha.trans hb.symm

/-- **The two marks split the states**, whatever the rules: a point is
universal exactly when it is a state whose phase is. -/
theorem gameMachine_blocksSplit (hdim : blockArityBound B ≤ gameDim B V)
    (rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop) :
    (gameMachine vars pol a₀ hdim rule).BlocksSplit := by
  intro q
  by_cases h : isUnivPt pol q
  · refine ⟨1, by omega, Or.inl ⟨rfl, h⟩, ?_⟩
    rintro j' (⟨rfl, -⟩ | ⟨rfl, hc⟩)
    · rfl
    · exact absurd h hc
  · refine ⟨0, by omega, Or.inr ⟨rfl, h⟩, ?_⟩
    rintro j' (⟨rfl, hc⟩ | ⟨rfl, -⟩)
    · exact absurd hc h
    · rfl

/-- **A state is universal exactly when its phase is.** -/
theorem gameMachine_isUniv (hdim : blockArityBound B ≤ gameDim B V)
    (rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop) (p : MachPh V M)
    (w : Fin (gameDim B V) → A) :
    (gameMachine vars pol a₀ hdim rule).IsUniv true (phasePt p w) ↔ MachPh.IsUniv pol p = true := by
  rw [ATMData.isUniv_true_iff_blk_one (gameMachine_blocksSplit hdim rule)]
  constructor
  · rintro (⟨-, h⟩ | ⟨hc, -⟩)
    · exact h
    · exact absurd hc (by decide)
  · exact fun h => Or.inl ⟨rfl, h⟩

/-! ### The two ends, and what a position is -/

/-- **What a position is**: a left sentinel, a cell, or the right sentinel.
This is what a walk's step analysis begins with – the head is one of the three,
and the symbol it reads follows. -/
theorem posn_cases (h₀ : IsBot a₀) {p : GamePt B V M A}
    (hp : machPosn p) (hd : machDom (ctrlArity vars) p) :
    (∃ b, p = leftPt a₀ b) ∨ (∃ (r : Bool) (i : B.ι) (ā : Fin (B.arity i) → A),
      p = cellPt a₀ r i ā) ∨ p = rightPt a₀ := by
  obtain ⟨s, hs, hsp⟩ := MachTag.exists_tapeTag_of_isPos hp
  have harity : MachTag.arity (ctrlArity vars) p.1 = TapeTag.arity s := by rw [hs]; rfl
  cases s with
  | left b =>
    exact Or.inl ⟨b, Prod.ext hs (eq_const_of_dom h₀ hd (by rw [harity]; rfl))⟩
  | right =>
    exact Or.inr (Or.inr (Prod.ext hs (eq_const_of_dom h₀ hd (by rw [harity]; rfl))))
  | cell r i =>
    have hle : B.arity i ≤ gameDim B V :=
      (arity_le_blockArityBound B i).trans (blockArityBound_le_gameDim B V)
    refine Or.inr (Or.inl ⟨r, i, pref hle p.2, Prod.ext hs ?_⟩)
    have hc : Canon (B.arity i) p.2 := by
      have : Canon (TapeTag.arity (TapeTag.cell r i)) p.2 := harity ▸ hd
      exact this
    exact (pad_pref_of_canon h₀ hle hc).symm
  | val b r i => exact hsp.elim
  | mark b => exact hsp.elim

/-! ### The rules -/

variable (vars natoms : GameQuestion → ℕ)

/-- **The rules of the machine**, all nine families.

Two of them are still parameters, and for the same reason the rules themselves
were one: they are the only places where the machine consults the *source
structure* rather than its own tape.

* `concOk` is the guard of a concluding transition – the residual formula of
  `DescriptiveComplexity.QuestionData`, which mentions no block atom and is
  therefore a first-order condition on the valuation;
* `isTarget` is the test a seek makes at a cell: is the symbol I am reading the
  one the challenged atom addresses, carrying the bit that was claimed? Both
  the address and the claim come from the phase and the tuple.

The control's own steps (family A) are `DescriptiveComplexity.MachPh.CtrlStep`,
which is `False` at every walk phase, so no family overlaps another except
where the design means it to: family C at a cell of the swept region, where the
two choices of the written bit are the guess. -/
def gameRule (concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop)
    (isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop)
    (t : TrTag B V M) (w : Fin (gameDim B V) → A) : Prop :=
  -- (A) a tape-free step of the control, bouncing on the left sentinels
  (t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = !t.src.par ∧
      MachPh.CtrlStep vars natoms t.src t.dst ∧ (t.src.kind = .conc → concOk t.src w)) ∨
  -- (B) a sweep crossing the left sentinels
  (t.src.kind = .sweep ∧ t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧
      t.right = true) ∨
  -- (C) a sweep at a cell: guess in the swept region, copy back elsewhere
  (t.src.kind = .sweep ∧ t.dst = t.src ∧ t.right = true ∧
      ∃ (b b' rr : Bool) (i : B.ι), t.rd = .val b rr i ∧ t.wr = .val b' rr i ∧
        (rr = t.src.tgt ∨ b' = b)) ∨
  -- (D) a sweep at the right sentinel, handing over to its rewind
  (t.src.kind = .sweep ∧ t.dst = MachPh.rewindPh t.src.r t.src.tgt t.src.cont false ∧
      t.rd = .mark true ∧ t.wr = .mark true ∧ t.right = false) ∨
  -- (E) a rewind at a cell, which changes nothing
  (t.src.kind = .rewind ∧ t.dst = t.src ∧ t.rd = t.wr ∧ t.right = false ∧
      ∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∨
  -- (F) a rewind at the left sentinel, handing over to its continuation
  (t.src.kind = .rewind ∧ t.dst = MachPh.rewindTarget t.src ∧
      t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = false) ∨
  -- (G) a seek crossing the left sentinels
  (t.src.kind = .seek ∧ t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧
      t.right = true) ∨
  -- (H) a seek at a cell that is not the one it is looking for
  (t.src.kind = .seek ∧ t.dst = t.src ∧ t.rd = t.wr ∧ t.right = true ∧
      (∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∧ ¬ isTarget t.src t.rd w) ∨
  -- (I) a seek at the cell it is looking for, carrying the bit that was claimed
  (t.src.kind = .seek ∧ t.dst = MachPh.accPh false ∧ t.rd = t.wr ∧ t.right = true ∧
      isTarget t.src t.rd w)

variable {vars natoms}
variable {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}

/-- **A rule out of a walk phase is never a control step**: the control graph
is empty there, so the nine families do not overlap at a walk. -/
theorem not_ctrlStep_of_walk {t : TrTag B V M}
    (h : t.src.kind = .sweep ∨ t.src.kind = .rewind ∨ t.src.kind = .seek) :
    ¬ MachPh.CtrlStep vars natoms t.src t.dst := by
  rcases h with h | h | h <;> simp [MachPh.CtrlStep, h]

end Machine

/-! ### The machine of a specification -/

/-- **What a machine needs to know about a specification**: one
`DescriptiveComplexity.QuestionData` per question, and the two bounds that let
the phases carry a *common* prefix index and a *common* claim vector. Nothing
is padded – each question keeps its own `vars` and `natoms`, and the tuples are
restricted with `Fin.castLE`. -/
structure GameProg (K : Language.{0, 0}) (B : SOBlock) (V M : ℕ) where
  /-- The machine-ready form of each of the six questions. -/
  data : GameQuestion → QuestionData K B
  /-- Every question's prefix fits in the phase's index. -/
  vars_le : ∀ q, (data q).vars ≤ V
  /-- Every question's atoms fit in the phase's claim vector. -/
  natoms_le : ∀ q, (data q).natoms ≤ M

namespace GameProg

variable {K : Language.{0, 0}} {B : SOBlock} {V M : ℕ} (prog : GameProg K B V M)

/-- The length of each question's prefix. -/
def vars : GameQuestion → ℕ := fun q => (prog.data q).vars

/-- The number of block atoms in each question's matrix. -/
def natoms : GameQuestion → ℕ := fun q => (prog.data q).natoms

/-- Whose turn each prefix variable is. -/
def pol : GameQuestion → ℕ → Bool := fun q => (prog.data q).pol

theorem vars_le_gameDim (q : GameQuestion) : (prog.data q).vars ≤ gameDim B V :=
  (prog.vars_le q).trans (by simp [gameDim])

variable {A : Type} [K.Structure A]

/-- The valuation a tuple gives the variables of a question. -/
noncomputable def valOf (q : GameQuestion) (w : Fin (gameDim B V) → A) :
    Fin (prog.data q).vars → A :=
  fun l => w (Fin.castLE (prog.vars_le_gameDim q) l)

/-- **The guard of a concluding transition**: the residual formula of the
question, under the claims the phase carries, read at the valuation the tuple
carries. It mentions no block atom, so it is a condition on the source
structure – written by the interpretation, never computed by the machine. -/
def concOk (p : MachPh V M) (w : Fin (gameDim B V) → A) : Prop :=
  ((prog.data p.q).sub fun j => p.claims (Fin.castLE (prog.natoms_le p.q) j)).Realize default
    (prog.valOf p.q w)

/-- **The test a seek makes at a cell**: is the symbol I am reading the one the
challenged atom addresses, carrying the bit that was claimed? The region and
the relation variable are named by the atom – the copy being read against the
region the game sits in – and the address is the atom's arguments
applied to the valuation. -/
def isTarget (p : MachPh V M) (s : SymTag B) (w : Fin (gameDim B V) → A) : Prop :=
  ∃ h : (p.k : ℕ) < (prog.data p.q).natoms,
    s = SymTag.val (p.claims (Fin.castLE (prog.natoms_le p.q) ⟨p.k, h⟩))
          (if ((prog.data p.q).atoms ⟨p.k, h⟩).copy then !p.r else p.r)
          ((prog.data p.q).atoms ⟨p.k, h⟩).var ∧
      argsOf ((prog.data p.q).atoms ⟨p.k, h⟩).var (addrOf w) =
        fun l => w (Fin.castLE (prog.vars_le_gameDim p.q)
          (((prog.data p.q).atoms ⟨p.k, h⟩).args l))

variable [LinearOrder A]

/-- **The machine of a specification**, complete: the layout, the control, the
nine rule families, and the two guards that read the source structure. -/
noncomputable def machine (a₀ : A) (hdim : blockArityBound B ≤ gameDim B V) :
    ATMData (GamePt B V M A) :=
  gameMachine prog.vars prog.pol a₀ hdim
    (gameRule prog.vars prog.natoms prog.concOk prog.isTarget)

/-- **The machine is well formed.** -/
theorem machine_wellFormed (a₀ : A) (hdim : blockArityBound B ≤ gameDim B V)
    (h₀ : IsBot a₀) : (prog.machine a₀ hdim).toTMData.WellFormed :=
  gameMachine_wellFormed hdim _ h₀

/-- **The two marks split its states.** -/
theorem machine_blocksSplit (a₀ : A) (hdim : blockArityBound B ≤ gameDim B V) :
    (prog.machine a₀ hdim).BlocksSplit :=
  gameMachine_blocksSplit hdim _

end GameProg

/-- **Every specification has such a program.** The six questions are read in
one language and normalized independently; the phases' index types are the
maxima, and nothing is padded. -/
theorem exists_gameProg {L : Language.{0, 0}} [L.IsRelational] (spec : SOGameSpec L) :
    ∃ (V M : ℕ) (prog : GameProg (L.sum Language.order) spec.B V M),
      ∀ q, (prog.data q).Plays (spec.question q) := by
  classical
  have h : ∀ q : GameQuestion, ∃ dq : QuestionData (L.sum Language.order) spec.B,
      dq.Plays (spec.question q) := fun q => exists_questionData _
  choose data hdata using h
  exact ⟨Finset.univ.sup fun q => (data q).vars, Finset.univ.sup fun q => (data q).natoms,
    ⟨data, fun q => Finset.le_sup (f := fun q => (data q).vars) (Finset.mem_univ q),
      fun q => Finset.le_sup (f := fun q => (data q).natoms) (Finset.mem_univ q)⟩, hdata⟩

/-! ### Reading a step off its transition -/

section Step

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool} {a₀ : A}
  {hdim : blockArityBound B ≤ gameDim B V}
  {rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop}

/-- The point of a transition: its tag, and its tuple. -/
def trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A) : GamePt B V M A :=
  (Sum.inr (Sum.inr t), w)

/-- **Every transition is a tagged tuple**, and its rule holds of it. This is
the one place the tag of a transition is destructured; everything downstream
reads the five lemmas below. -/
theorem exists_trPt_of_tr {τ : GamePt B V M A}
    (h : (gameMachine vars pol a₀ hdim rule).Tr τ) :
    ∃ (t : TrTag B V M) (w : Fin (gameDim B V) → A), τ = trPt t w ∧ rule t w := by
  obtain ⟨t, ht, hr⟩ := h
  exact ⟨t, τ.2, Prod.ext ht rfl, hr⟩

omit [LinearOrder A] in
private theorem tag_inj {t t' : TrTag B V M} {w : Fin (gameDim B V) → A}
    (h : (trPt t w : GamePt B V M A).1 = Sum.inr (Sum.inr t')) : t' = t :=
  (Sum.inr.inj (Sum.inr.inj h)).symm

@[simp] theorem tr_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A) :
    (gameMachine vars pol a₀ hdim rule).Tr (trPt t w) ↔ rule t w :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

@[simp] theorem right_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A) :
    (gameMachine vars pol a₀ hdim rule).Right (trPt t w) ↔ t.right = true :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

@[simp] theorem read_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A)
    (x : GamePt B V M A) :
    (gameMachine vars pol a₀ hdim rule).Read (trPt t w) x ↔ x = gameSymPt a₀ t.rd (addrOf w) :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

@[simp] theorem write_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A)
    (x : GamePt B V M A) :
    (gameMachine vars pol a₀ hdim rule).Write (trPt t w) x ↔ x = gameSymPt a₀ t.wr (addrOf w) :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

@[simp] theorem src_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A)
    (q : GamePt B V M A) :
    (gameMachine vars pol a₀ hdim rule).Src (trPt t w) q ↔
      (q.1 = Sum.inr (Sum.inl t.src) ∧ Canon (MachPh.arity vars t.src) q.2 ∧
        Agree (MachPh.arity vars t.src) w q.2) :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

@[simp] theorem dst_trPt (t : TrTag B V M) (w : Fin (gameDim B V) → A)
    (q : GamePt B V M A) :
    (gameMachine vars pol a₀ hdim rule).Dst (trPt t w) q ↔
      (q.1 = Sum.inr (Sum.inl t.dst) ∧ Canon (MachPh.arity vars t.dst) q.2 ∧
        Agree (MachPh.arity vars t.dst) w q.2) :=
  ⟨fun ⟨_, ht, hr⟩ => tag_inj ht ▸ hr, fun h => ⟨t, rfl, h⟩⟩

/-- **A step, read off its transition.** The tuple `w` of the transition is what
carries the value a prefix step writes and the address a walk step reads; the
five clauses about it are exactly the five attributes of
`DescriptiveComplexity.TMData.Step`. -/
theorem game_step_iff (c c' : Config (GamePt B V M A)) :
    (gameMachine vars pol a₀ hdim rule).toTMData.Step c c' ↔
      ∃ (t : TrTag B V M) (w : Fin (gameDim B V) → A), rule t w ∧
        (c.state.1 = Sum.inr (Sum.inl t.src) ∧ Canon (MachPh.arity vars t.src) c.state.2 ∧
          Agree (MachPh.arity vars t.src) w c.state.2) ∧
        c.tape c.head = gameSymPt a₀ t.rd (addrOf w) ∧
        (c'.state.1 = Sum.inr (Sum.inl t.dst) ∧ Canon (MachPh.arity vars t.dst) c'.state.2 ∧
          Agree (MachPh.arity vars t.dst) w c'.state.2) ∧
        c'.tape c.head = gameSymPt a₀ t.wr (addrOf w) ∧
        (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
        ((t.right = true ∧ SuccPos (gameMachine vars pol a₀ hdim rule).Le
            (gameMachine vars pol a₀ hdim rule).Posn c.head c'.head) ∨
          (t.right = false ∧ SuccPos (gameMachine vars pol a₀ hdim rule).Le
            (gameMachine vars pol a₀ hdim rule).Posn c'.head c.head)) := by
  constructor
  · rintro ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    obtain ⟨t, w, rfl, hr⟩ := exists_trPt_of_tr hτ
    refine ⟨t, w, hr, (src_trPt t w _).mp hsrc, (read_trPt t w _).mp hread,
      (dst_trPt t w _).mp hdst, (write_trPt t w _).mp hwrite, hframe, ?_⟩
    rcases hmove with ⟨hr', hs⟩ | ⟨hr', hs⟩
    · exact Or.inl ⟨(right_trPt t w).mp hr', hs⟩
    · exact Or.inr ⟨by simpa using fun h => hr' ((right_trPt t w).mpr h), hs⟩
  · rintro ⟨t, w, hr, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    refine ⟨trPt t w, (tr_trPt t w).mpr hr, (src_trPt t w _).mpr hsrc,
      (read_trPt t w _).mpr hread, (dst_trPt t w _).mpr hdst,
      (write_trPt t w _).mpr hwrite, hframe, ?_⟩
    rcases hmove with ⟨hr', hs⟩ | ⟨hr', hs⟩
    · exact Or.inl ⟨(right_trPt t w).mpr hr', hs⟩
    · exact Or.inr ⟨fun hc => by simp [(right_trPt t w).mp hc] at hr', hs⟩

end Step

/-! ### Building one step -/

section Build

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool} {a₀ : A}
  {hdim : blockArityBound B ≤ gameDim B V}
  {rule : TrTag B V M → (Fin (gameDim B V) → A) → Prop}

open Classical in
/-- **One step, built from a rule.** The destination configuration is forced:
the state is whatever `Dst` allows, the head is the neighbor, and the tape is
the old one with the written symbol at the head. Every case of every walk goes
through this, so the frame condition is discharged once. -/
theorem step_of_rule {t : TrTag B V M} {w : Fin (gameDim B V) → A} (hrule : rule t w)
    (c : Config (GamePt B V M A)) (q' h' : GamePt B V M A)
    (hsrc : c.state.1 = Sum.inr (Sum.inl t.src))
    (hcs : Canon (MachPh.arity vars t.src) c.state.2)
    (has : Agree (MachPh.arity vars t.src) w c.state.2)
    (hdst : q'.1 = Sum.inr (Sum.inl t.dst))
    (hcd : Canon (MachPh.arity vars t.dst) q'.2)
    (had : Agree (MachPh.arity vars t.dst) w q'.2)
    (hread : c.tape c.head = gameSymPt a₀ t.rd (addrOf w))
    (hmove : (t.right = true ∧ SuccPos (gameMachine vars pol a₀ hdim rule).Le
        (gameMachine vars pol a₀ hdim rule).Posn c.head h') ∨
      (t.right = false ∧ SuccPos (gameMachine vars pol a₀ hdim rule).Le
        (gameMachine vars pol a₀ hdim rule).Posn h' c.head)) :
    (gameMachine vars pol a₀ hdim rule).toTMData.Step c
      ⟨q', h', Function.update c.tape c.head (gameSymPt a₀ t.wr (addrOf w))⟩ :=
  (game_step_iff c _).mpr ⟨t, w, hrule, ⟨hsrc, hcs, has⟩, hread, ⟨hdst, hcd, had⟩,
    Function.update_self _ _ _, fun _ hp => Function.update_of_ne hp _ _, hmove⟩

end Build

/-! ### What a walk may do -/

section Cases

variable {B : SOBlock} {V M : ℕ} {A : Type}
  {vars natoms : GameQuestion → ℕ}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {t : TrTag B V M} {w : Fin (gameDim B V) → A}

/-- **The three things a sweep may do**, and nothing else: cross a left
sentinel, act at a cell – guessing the bit in the swept region, copying it back
elsewhere – or reach the right mark and hand over to its rewind. The other six
families die on the phase's kind, and the control's own family dies because
`DescriptiveComplexity.MachPh.CtrlStep` is empty at a walk. -/
theorem sweep_cases (hk : t.src.kind = .sweep)
    (h : gameRule vars natoms concOk isTarget t w) :
    (t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = true) ∨
    (t.dst = t.src ∧ t.right = true ∧
      ∃ (b b' rr : Bool) (i : B.ι), t.rd = .val b rr i ∧ t.wr = .val b' rr i ∧
        (rr = t.src.tgt ∨ b' = b)) ∨
    (t.dst = MachPh.rewindPh t.src.r t.src.tgt t.src.cont false ∧
      t.rd = .mark true ∧ t.wr = .mark true ∧ t.right = false) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2.2.1 (not_ctrlStep_of_walk (Or.inl hk))
  · exact Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · exact Or.inr (Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
  · exact Or.inr (Or.inr ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)

/-- **The two things a rewind may do**: cross a cell without changing it, or
reach the left mark and hand over to its continuation. Both move left, so it
really does walk back. -/
theorem rewind_cases (hk : t.src.kind = .rewind)
    (h : gameRule vars natoms concOk isTarget t w) :
    (t.dst = t.src ∧ t.rd = t.wr ∧ t.right = false ∧
      ∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∨
    (t.dst = MachPh.rewindTarget t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧
      t.right = false) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2.2.1 (not_ctrlStep_of_walk (Or.inr (Or.inl hk)))
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · exact Or.inr ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)

/-- **The three things a seek may do**: cross a left sentinel, cross a cell
that is not its target, or stop at the one that is. Every one of them writes
back what it read, so a seek never changes the tape; and the last is the only
way out of the phase, so a seek that never meets its target simply runs off the
tape and loses. -/
theorem seek_cases (hk : t.src.kind = .seek)
    (h : gameRule vars natoms concOk isTarget t w) :
    (t.dst = t.src ∧ t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = true) ∨
    (t.dst = t.src ∧ t.rd = t.wr ∧ t.right = true ∧
      (∃ (b rr : Bool) (i : B.ι), t.rd = .val b rr i) ∧ ¬ isTarget t.src t.rd w) ∨
    (t.dst = MachPh.accPh false ∧ t.rd = t.wr ∧ t.right = true ∧
      isTarget t.src t.rd w) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2.2.1 (not_ctrlStep_of_walk (Or.inr (Or.inr hk)))
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact absurd (hk.symm.trans h.1) (by simp)
  · exact Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · exact Or.inr (Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
  · exact Or.inr (Or.inr ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)

/-- **The only thing a control phase may do is a step of the control graph.**
The eight tape families all name a walk kind, so at any other phase they are
empty and family (A) is what is left – with the guard of a concluding
transition, which is the one thing the control graph does not carry. -/
theorem ctrl_cases (hs : t.src.kind ≠ .sweep) (hr : t.src.kind ≠ .rewind)
    (hk : t.src.kind ≠ .seek) (h : gameRule vars natoms concOk isTarget t w) :
    t.rd = .mark false ∧ t.wr = .mark false ∧ t.right = !t.src.par ∧
      MachPh.CtrlStep vars natoms t.src t.dst ∧ (t.src.kind = .conc → concOk t.src w) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact h
  · exact absurd h.1 hs
  · exact absurd h.1 hs
  · exact absurd h.1 hs
  · exact absurd h.1 hr
  · exact absurd h.1 hr
  · exact absurd h.1 hk
  · exact absurd h.1 hk
  · exact absurd h.1 hk

/-- **A rewind never changes the tape.** -/
theorem rewind_writes_back (hk : t.src.kind = .rewind)
    (h : gameRule vars natoms concOk isTarget t w) : t.rd = t.wr := by
  rcases rewind_cases hk h with ⟨_, hrd, _⟩ | ⟨_, hrd, hwr, _⟩
  · exact hrd
  · rw [hrd, hwr]

end Cases

/-! ### The two steps of a sweep -/

section Sweep

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars : GameQuestion → ℕ} {natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

open Classical in
/-- **A sweep crosses a sentinel**, changing nothing. -/
theorem sweep_step_left (h₀ : IsBot a₀) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.sweepPh r tgt cont par) fun _ => a₀)
    (hread : c.tape c.head = markPt a₀ false) {h' : GamePt B V M A}
    (hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head h') :
    (𝕄).toTMData.Step c ⟨c.state, h', Function.update c.tape c.head (markPt a₀ false)⟩ := by
  refine step_of_rule (t := ⟨MachPh.sweepPh r tgt cont par, MachPh.sweepPh r tgt cont par,
      .mark false, .mark false, true⟩) (w := fun _ => a₀)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) c c.state h' ?_ ?_ ?_ ?_ ?_ ?_ hread
    (Or.inl ⟨rfl, hsucc⟩)
  · rw [hstate]; rfl
  · rw [hstate]; exact fun j _ => h₀
  · exact fun j hj => absurd hj (by simp [MachPh.arity, MachPh.sweepPh])
  · rw [hstate]; rfl
  · rw [hstate]; exact fun j _ => h₀
  · exact fun j hj => absurd hj (by simp [MachPh.arity, MachPh.sweepPh])

open Classical in
/-- **A sweep acts at a cell**: in the region it is writing it may put either
bit there, and elsewhere it writes back what it read. -/
theorem sweep_step_cell (h₀ : IsBot a₀) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.sweepPh r tgt cont par) fun _ => a₀)
    {b rr b' : Bool} {i : B.ι} {ā : Fin (B.arity i) → A}
    (hread : c.tape c.head = valPt a₀ b rr i ā) (hb : rr = tgt ∨ b' = b)
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head h') :
    (𝕄).toTMData.Step c ⟨c.state, h', Function.update c.tape c.head (valPt a₀ b' rr i ā)⟩ := by
  have haddr : addrOf (joinTuple (B := B) (V := V) (fun _ => a₀) (pad a₀ ā)) = pad a₀ ā :=
    addrOf_joinTuple (V := V) _ _
  have hwr : (gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ (SymTag.val b' rr i)
      (addrOf (joinTuple (V := V) (fun _ => a₀) (pad a₀ ā))) : GamePt B V M A) =
      valPt a₀ b' rr i ā := by
    rw [gameSymPt_val, haddr, argsOf_pad]
  rw [← hwr]
  refine step_of_rule (t := ⟨MachPh.sweepPh r tgt cont par, MachPh.sweepPh r tgt cont par,
      .val b rr i, .val b' rr i, true⟩) (w := joinTuple (fun _ => a₀) (pad a₀ ā))
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, b, b', rr, i, rfl, rfl, hb⟩)))
    c c.state h' ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inl ⟨rfl, hsucc⟩)
  · rw [hstate]; rfl
  · rw [hstate]; exact fun j _ => h₀
  · exact fun j hj => absurd hj (by simp [MachPh.arity, MachPh.sweepPh])
  · rw [hstate]; rfl
  · rw [hstate]; exact fun j _ => h₀
  · exact fun j hj => absurd hj (by simp [MachPh.arity, MachPh.sweepPh])
  · rw [hread, gameSymPt_val, haddr, argsOf_pad]

open Classical in
/-- **A sweep reaches the right mark and hands over to its rewind**, moving
left in the same step – so the rewind starts strictly below the right
sentinel. -/
theorem sweep_step_right (h₀ : IsBot a₀) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.sweepPh r tgt cont par) fun _ => a₀)
    (hread : c.tape c.head = markPt a₀ true)
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn h' c.head) :
    (𝕄).toTMData.Step c
      ⟨phasePt (MachPh.rewindPh r tgt cont false) (fun _ => a₀), h', c.tape⟩ := by
  have h := step_of_rule (t := ⟨MachPh.sweepPh r tgt cont par,
      MachPh.rewindPh r tgt cont false, .mark true, .mark true, false⟩) (w := fun _ => a₀)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))))
    c (phasePt (MachPh.rewindPh r tgt cont false) fun _ => a₀) h'
    (by rw [hstate]; rfl) (by rw [hstate]; exact fun j _ => h₀)
    (fun j hj => absurd hj (by simp)) rfl (fun j _ => h₀) (fun j _ => rfl)
    hread (Or.inr ⟨rfl, hsucc⟩)
  rwa [gameSymPt_mark, ← hread, Function.update_eq_self] at h

end Sweep

/-! ### A walk along the positions

The induction the three walks run on, stated for an arbitrary machine: each
step moves the head to the neighboring position and preserves an invariant, so
the walk reaches the end of the tape. The measure is
`DescriptiveComplexity.bitRank`, which increases by one along
`DescriptiveComplexity.SuccPos`
(`DescriptiveComplexity.bitRank_succPos`) and is bounded by the number of
positions (`DescriptiveComplexity.bitRank_lt_card`), so nothing here depends on
*which* position follows which – the successor is whatever the step produces.
That is the payoff of §2.1a: a walk needs no address of its own. -/

section Walk

variable {U : Type} [Finite U] {M : TMData U}

/-- **A rightward walk runs until something stops it, or to the end of the
tape.** A sweep is stopped by nothing and so reaches the right sentinel; a seek
is stopped by the cell it is looking for, and reaching the sentinel instead is
how it learns there was none. -/
theorem exists_reach_stop (hlin : IsLinOrd M.Le) {Inv Stop Guard : Config U → Prop}
    (hguard : ∀ c, Inv c → ¬ MaxPos M.Le M.Posn c.head → ¬ Stop c → Guard c)
    (hstep : ∀ c, Inv c → M.Posn c.head → ¬ MaxPos M.Le M.Posn c.head → ¬ Stop c →
      ∃ c', M.Step c c' ∧ SuccPos M.Le M.Posn c.head c'.head ∧ Inv c') :
    ∀ c, Inv c → M.Posn c.head →
      ∃ c', Relation.ReflTransGen (fun x y => M.Step x y ∧ Guard x) c c' ∧
        (Stop c' ∨ MaxPos M.Le M.Posn c'.head) ∧ Inv c' := by
  classical
  have key : ∀ n c, Nat.card {x : U // M.Posn x} - bitRank M.Le M.Posn c.head ≤ n →
      Inv c → M.Posn c.head →
      ∃ c', Relation.ReflTransGen (fun x y => M.Step x y ∧ Guard x) c c' ∧
        (Stop c' ∨ MaxPos M.Le M.Posn c'.head) ∧ Inv c' := by
    intro n
    induction n with
    | zero =>
      intro c hle _ hpos
      have hlt := bitRank_lt_card (Le := M.Le) (Posn := M.Posn) hpos
      omega
    | succ n ih =>
      intro c hle hInv hpos
      by_cases hstop : Stop c
      · exact ⟨c, Relation.ReflTransGen.refl, Or.inl hstop, hInv⟩
      by_cases hmax : MaxPos M.Le M.Posn c.head
      · exact ⟨c, Relation.ReflTransGen.refl, Or.inr hmax, hInv⟩
      · obtain ⟨c', hst, hsucc, hInv'⟩ := hstep c hInv hpos hmax hstop
        have hrk := bitRank_succPos hlin hsucc
        obtain ⟨c'', hreach, hstop'', hInv''⟩ := ih c' (by omega) hInv' hsucc.2.1
        exact ⟨c'', Relation.ReflTransGen.head ⟨hst, hguard c hInv hmax hstop⟩ hreach,
          hstop'', hInv''⟩
  exact fun c => key _ c le_rfl

/-- **A rightward walk reaches the highest position**, when nothing stops it. -/
theorem exists_reach_maxPos (hlin : IsLinOrd M.Le) {Inv Guard : Config U → Prop}
    (hguard : ∀ c, Inv c → ¬ MaxPos M.Le M.Posn c.head → Guard c)
    (hstep : ∀ c, Inv c → M.Posn c.head → ¬ MaxPos M.Le M.Posn c.head →
      ∃ c', M.Step c c' ∧ SuccPos M.Le M.Posn c.head c'.head ∧ Inv c') :
    ∀ c, Inv c → M.Posn c.head →
      ∃ c', Relation.ReflTransGen (fun x y => M.Step x y ∧ Guard x) c c' ∧
        MaxPos M.Le M.Posn c'.head ∧ Inv c' := by
  intro c hInv hpos
  obtain ⟨c', hreach, hstop, hInv'⟩ :=
    exists_reach_stop (Stop := fun _ => False) hlin (fun d hd hm _ => hguard d hd hm)
      (fun d hd hp hm _ => hstep d hd hp hm) c hInv hpos
  exact ⟨c', hreach, hstop.resolve_left id, hInv'⟩

/-- **A leftward walk reaches the lowest position.** -/
theorem exists_reach_minPos (hlin : IsLinOrd M.Le) {Inv Guard : Config U → Prop}
    (hguard : ∀ c, Inv c → ¬ MinPos M.Le M.Posn c.head → Guard c)
    (hstep : ∀ c, Inv c → M.Posn c.head → ¬ MinPos M.Le M.Posn c.head →
      ∃ c', M.Step c c' ∧ SuccPos M.Le M.Posn c'.head c.head ∧ Inv c') :
    ∀ c, Inv c → M.Posn c.head →
      ∃ c', Relation.ReflTransGen (fun x y => M.Step x y ∧ Guard x) c c' ∧
        MinPos M.Le M.Posn c'.head ∧ Inv c' := by
  have key : ∀ n c, bitRank M.Le M.Posn c.head ≤ n → Inv c → M.Posn c.head →
      ∃ c', Relation.ReflTransGen (fun x y => M.Step x y ∧ Guard x) c c' ∧
        MinPos M.Le M.Posn c'.head ∧ Inv c' := by
    intro n
    induction n with
    | zero =>
      intro c hle hInv hpos
      by_cases hmin : MinPos M.Le M.Posn c.head
      · exact ⟨c, Relation.ReflTransGen.refl, hmin, hInv⟩
      · obtain ⟨c', _, hsucc, _⟩ := hstep c hInv hpos hmin
        have hrk := bitRank_succPos hlin hsucc
        omega
    | succ n ih =>
      intro c hle hInv hpos
      by_cases hmin : MinPos M.Le M.Posn c.head
      · exact ⟨c, Relation.ReflTransGen.refl, hmin, hInv⟩
      · obtain ⟨c', hst, hsucc, hInv'⟩ := hstep c hInv hpos hmin
        have hrk := bitRank_succPos hlin hsucc
        obtain ⟨c'', hreach, hmin'', hInv''⟩ := ih c' (by omega) hInv' hsucc.1
        exact ⟨c'', Relation.ReflTransGen.head ⟨hst, hguard c hInv hmin⟩ hreach, hmin'', hInv''⟩
  exact fun c => key _ c le_rfl

/-! ### What a walk has already passed

A walk's invariant has to say *what it has already rewritten*, and the only
handle on that is the order: the cells strictly below the head. The two facts
below are all it needs, and neither mentions the tape's layout – so the sweep's
invariant never has to compare two cells, and the order on cells
(`cellPt r i ā` against `cellPt r' i' ā'`) does not have to be characterized at
all. -/

section Below

variable {U : Type} {Le : U → U → Prop} {Posn : U → Prop}

/-- **A step of the walk moves exactly one position from ahead to behind**: the
positions strictly below the successor are those strictly below the head,
together with the head itself. -/
theorem below_succPos (hlin : IsLinOrd Le) {h h' : U} (hs : SuccPos Le Posn h h')
    {p : U} (hp : Posn p) :
    (Le p h' ∧ p ≠ h') ↔ ((Le p h ∧ p ≠ h) ∨ p = h) := by
  obtain ⟨hph, hph', hhh', hne, hbetween⟩ := hs
  constructor
  · rintro ⟨hle, hpne⟩
    rcases hlin.2.2.2 p h with hph2 | hhp
    · rcases eq_or_ne p h with rfl | hpne2
      · exact Or.inr rfl
      · exact Or.inl ⟨hph2, hpne2⟩
    · rcases hbetween p hp hhp hle with rfl | rfl
      · exact Or.inr rfl
      · exact absurd rfl hpne
  · rintro (⟨hle, hpne⟩ | rfl)
    · refine ⟨hlin.2.1 p h h' hle hhh', fun hcon => ?_⟩
      exact hne (hlin.2.2.1 h h' hhh' (hcon ▸ hle))
    · exact ⟨hhh', hne⟩

/-- **The element immediately above a given one is unique** – the mirror of
`DescriptiveComplexity.succPos_left_unique`, and what pins the head a control
step lands on. -/
theorem succPos_right_unique (hlin : IsLinOrd Le) {p q q' : U}
    (h : SuccPos Le Posn p q) (h' : SuccPos Le Posn p q') : q = q' := by
  rcases hlin.2.2.2 q q' with hle | hle
  · rcases h'.2.2.2.2 q h.2.1 h.2.2.1 hle with h1 | h1
    · exact absurd h1.symm h.2.2.2.1
    · exact h1
  · rcases h.2.2.2.2 q' h'.2.1 h'.2.2.1 hle with h1 | h1
    · exact absurd h1.symm h'.2.2.2.1
    · exact h1.symm

end Below

end Walk

/-! ### The control's own step -/

section Ctrl

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

open Classical in
/-- **A step of the control graph, built.** The head bounces between the two
left sentinels – which is what `DescriptiveComplexity.MachPh.par` records, and
why every such step flips it – and the tape is untouched. The destination keeps
the transition's tuple up to the arity it declares, so a prefix step *writes*
exactly one coordinate and the choice of the transition is the choice of the
value written. -/
theorem ctrl_step (h₀ : IsBot a₀) {p p' : MachPh V M} {w vv : Fin (gameDim B V) → A}
    (hcs : MachPh.CtrlStep vars natoms p p') (hconc : p.kind = .conc → concOk p w)
    (c : Config (GamePt B V M A)) (hstate : c.state = phasePt p vv)
    (hcv : Canon (MachPh.arity vars p) vv) (hag : Agree (MachPh.arity vars p) w vv)
    (hhead : c.head = leftPt a₀ p.par) (hread : c.tape c.head = markPt a₀ false) :
    (𝕄).toTMData.Step c
      ⟨phasePt p' (truncTuple a₀ (MachPh.arity vars p') w), leftPt a₀ (!p.par), c.tape⟩ := by
  have hsucc : SuccPos (𝕄).Le (𝕄).Posn (leftPt a₀ false) (leftPt a₀ true) :=
    succPos_leftPt h₀ (carity := ctrlArity vars)
  have hmove : ((!p.par) = true ∧ SuccPos (𝕄).Le (𝕄).Posn c.head (leftPt a₀ (!p.par))) ∨
      ((!p.par) = false ∧ SuccPos (𝕄).Le (𝕄).Posn (leftPt a₀ (!p.par)) c.head) := by
    cases hp : p.par with
    | false => exact Or.inl ⟨by simp, by rw [hhead, hp]; exact hsucc⟩
    | true => exact Or.inr ⟨by simp, by rw [hhead, hp]; exact hsucc⟩
  have h := step_of_rule (t := ⟨p, p', .mark false, .mark false, !p.par⟩) (w := w)
    (Or.inl ⟨rfl, rfl, rfl, hcs, hconc⟩) c
    (phasePt p' (truncTuple a₀ (MachPh.arity vars p') w)) (leftPt a₀ (!p.par))
    (by rw [hstate]; rfl) (by rw [hstate]; exact hcv) (by rw [hstate]; exact hag) rfl
    (canon_truncTuple h₀ _ w) (agree_truncTuple a₀ _ w) hread hmove
  rwa [gameSymPt_mark, ← hread, Function.update_eq_self] at h

end Ctrl

/-! ### The run of a sweep -/

section SweepRun

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

open Classical in
/-- **A sweep writes an arbitrary assignment into its region.** Starting at the
lowest position with the tape holding `ρ` and `σ`, it reaches the right
sentinel with the tape holding any `ρ'`, `σ'` that agree with them outside the
swept region – and, since the phase owns the choice, *every* play of the sweep
is such a run, which is what a universal sweep needs.

The tape is controlled only **at the positions**: a cell tag with a
non-canonical tuple is not one, and is never read. -/
theorem sweep_run (h₀ : IsBot a₀) {ρ σ ρ' σ' : B.Assignment A}
    (hkeep : ∀ rr : Bool, rr ≠ tgt → cond rr σ' ρ' = cond rr σ ρ)
    (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.sweepPh r tgt cont par) fun _ => a₀)
    {bhd : Bool} (hhead : c.head = leftPt a₀ bhd)
    (htape : ∀ p, (𝕄).Posn p → c.tape p = tapeOfAssign a₀ hdim ρ σ p) :
    ∃ c', Relation.ReflTransGen (fun x y => (𝕄).toTMData.Step x y ∧ x.state = c.state) c c' ∧
      c'.state = c.state ∧ c'.head = rightPt a₀ ∧
      ∀ p, (𝕄).Posn p → c'.tape p = tapeOfAssign a₀ hdim ρ' σ' p := by
  set old := tapeOfAssign (C := GameCtrlTag B V M) a₀ hdim ρ σ with hold
  set new := tapeOfAssign (C := GameCtrlTag B V M) a₀ hdim ρ' σ' with hnew
  set Inv : Config (GamePt B V M A) → Prop := fun d =>
    d.state = c.state ∧
      (∀ p, (𝕄).Posn p → (𝕄).Le p d.head → p ≠ d.head → d.tape p = new p) ∧
      (∀ p, (𝕄).Posn p → ¬((𝕄).Le p d.head ∧ p ≠ d.head) → d.tape p = old p) with hInvDef
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  -- the step
  have hstep : ∀ d, Inv d → (𝕄).Posn d.head → ¬ MaxPos (𝕄).Le (𝕄).Posn d.head →
      ∃ d', (𝕄).toTMData.Step d d' ∧ SuccPos (𝕄).Le (𝕄).Posn d.head d'.head ∧ Inv d' := by
    intro d hInv hpos hnmax
    obtain ⟨h', hsucc⟩ := TMData.exists_succPos' (M := (𝕄).toTMData) hlin hpos hnmax
    have hdst : d.state = phasePt (MachPh.sweepPh r tgt cont par) fun _ => a₀ :=
      hInv.1.trans hstate
    have hreadold : d.tape d.head = old d.head :=
      hInv.2.2 d.head hpos (fun hc => hc.2 rfl)
    -- the invariant of the successor, from the one at the head
    have hnext : ∀ (x : GamePt B V M A), (x = new d.head) →
        Inv ⟨d.state, h', Function.update d.tape d.head x⟩ := by
      intro x hx
      refine ⟨hInv.1, ?_, ?_⟩
      · intro p hp hle hne
        dsimp only
        rcases (below_succPos hlin hsucc hp).mp ⟨hle, hne⟩ with ⟨hle', hne'⟩ | rfl
        · rw [Function.update_of_ne hne' _ _]
          exact hInv.2.1 p hp hle' hne'
        · rw [Function.update_self, hx]
      · intro p hp hnb
        dsimp only
        have hpne : p ≠ d.head := by
          intro hc
          exact hnb ((below_succPos hlin hsucc hp).mpr (Or.inr hc))
        rw [Function.update_of_ne hpne _ _]
        refine hInv.2.2 p hp fun hc => hnb ?_
        exact (below_succPos hlin hsucc hp).mpr (Or.inl hc)
    rcases posn_cases h₀ hpos.1 hpos.2 with ⟨b, hb⟩ | ⟨r₀, i, ā, hcell⟩ | hr
    · refine ⟨_, sweep_step_left h₀ d hdst ?_ hsucc, hsucc, hnext _ ?_⟩
      · rw [hreadold, hb, hold, tapeOfAssign_leftPt]
      · rw [hb, hnew, tapeOfAssign_leftPt]
    · refine ⟨_, sweep_step_cell (b := decide (cond r₀ σ ρ i ā)) (rr := r₀) (i := i) (ā := ā)
        (b' := decide (cond r₀ σ' ρ' i ā)) h₀ d hdst ?_ ?_ hsucc, hsucc, hnext _ ?_⟩
      · rw [hreadold, hcell, hold, tapeOfAssign_cellPt]
      · by_cases hrt : r₀ = tgt
        · exact Or.inl hrt
        · exact Or.inr (by rw [hkeep r₀ hrt])
      · rw [hcell, hnew, tapeOfAssign_cellPt]
    · exact absurd (hr ▸ maxPos_rightPt h₀ (carity := ctrlArity vars)) hnmax
  -- run the walk
  -- below a sentinel there are only sentinels, where the two tapes agree anyway
  have hstart : ∀ p, (𝕄).Posn p → (𝕄).Le p c.head → p ≠ c.head → c.tape p = new p := by
    intro p hp hle _
    have hle' : (𝕄).Le p (leftPt a₀ true) :=
      hlin.2.1 _ _ _ hle (by rw [hhead]; exact leftPt_le_leftPt_true bhd)
    rcases eq_leftPt_of_le h₀ hp hle' with hp1 | hp1 <;>
      rw [htape p hp, hold, hnew, hp1, tapeOfAssign_leftPt, tapeOfAssign_leftPt]
  obtain ⟨d, hreach, hmax, hInv⟩ := exists_reach_maxPos (M := (𝕄).toTMData) hlin
    (fun d hd _ => hd.1) hstep c ⟨rfl, hstart, fun p hp _ => htape p hp⟩
    (hhead ▸ ⟨trivial, fun j _ => h₀⟩)
  have hhr : d.head = rightPt a₀ :=
    hlin.2.2.1 _ _ ((maxPos_rightPt h₀ (carity := ctrlArity vars)).2 _ hmax.1)
      (hmax.2 _ (maxPos_rightPt h₀ (carity := ctrlArity vars)).1)
  refine ⟨d, hreach, hInv.1, hhr, fun p hp => ?_⟩
  by_cases hpe : p = d.head
  · rw [hpe, hInv.2.2 _ hmax.1 (fun hc => hc.2 rfl), hhr, hold, hnew,
      tapeOfAssign_rightPt, tapeOfAssign_rightPt]
  · exact hInv.2.1 p hp (hmax.2 p hp) hpe

end SweepRun

/-! ### The run of a rewind

A rewind changes nothing – both its rules write back what they read – so its
invariant is about the *state*, not the tape. Unlike a sweep it does not end in
the phase it began: its last step, at the second left sentinel, both moves to
the lowest position and hands over to
`DescriptiveComplexity.MachPh.rewindTarget`. So the invariant it runs on is

```
(the tape is unchanged) ∧ (the head is not the right sentinel) ∧
  (the state is the rewind, or it is the target and the head is lowest)
```

and closing it needs the two order facts of the layout: the two left sentinels
are adjacent (`DescriptiveComplexity.succPos_leftPt`), so the handover really
does land on the lowest position; and a cell is never next to the first
sentinel (`DescriptiveComplexity.succPos_ne_leftPt`), so the walk cannot
reach the lowest position without reading the mark first. -/

section Rewind

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {r tgt : Bool} {cont : SweepCont} {par : Bool}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

omit [Finite A] in
open Classical in
/-- **A rewind crosses a cell**, changing nothing. -/
theorem rewind_step_cell (h₀ : IsBot a₀) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.rewindPh r tgt cont par) fun _ => a₀)
    {b rr : Bool} {i : B.ι} {ā : Fin (B.arity i) → A}
    (hread : c.tape c.head = valPt a₀ b rr i ā)
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn h' c.head) :
    (𝕄).toTMData.Step c ⟨c.state, h', c.tape⟩ := by
  have hsym : (gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ (SymTag.val b rr i)
      (addrOf (walkTuple (V := V) (fun _ => a₀) (pad a₀ ā))) : GamePt B V M A) =
      valPt a₀ b rr i ā := by
    rw [gameSymPt_val, addrOf_walkTuple, argsOf_pad]
  have h := step_of_rule (t := ⟨MachPh.rewindPh r tgt cont par, MachPh.rewindPh r tgt cont par,
      .val b rr i, .val b rr i, false⟩) (w := walkTuple (fun _ => a₀) (pad a₀ ā))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, b, rr, i, rfl⟩)))))
    c c.state h' (by rw [hstate]; rfl) (by rw [hstate]; exact fun j _ => h₀)
    (fun j hj => absurd hj (by simp)) (by rw [hstate]; rfl)
    (by rw [hstate]; exact fun j _ => h₀) (fun j hj => absurd hj (by simp))
    (by rw [hsym]; exact hread) (Or.inr ⟨rfl, hsucc⟩)
  rwa [hsym, ← hread, Function.update_eq_self] at h

omit [Finite A] in
open Classical in
/-- **A rewind reads the left mark and hands over**, moving left in the same
step – which is why it has to be the second sentinel it reads it on. -/
theorem rewind_step_left (h₀ : IsBot a₀) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.rewindPh r tgt cont par) fun _ => a₀)
    (hread : c.tape c.head = markPt a₀ false)
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn h' c.head) :
    (𝕄).toTMData.Step c
      ⟨phasePt (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par)) (fun _ => a₀), h',
        c.tape⟩ := by
  have h := step_of_rule (t := ⟨MachPh.rewindPh r tgt cont par,
      MachPh.rewindTarget (MachPh.rewindPh r tgt cont par), .mark false, .mark false, false⟩)
      (w := fun _ => a₀)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))))))
    c (phasePt (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par)) fun _ => a₀) h'
    (by rw [hstate]; rfl) (by rw [hstate]; exact fun j _ => h₀)
    (fun j hj => absurd hj (by simp)) rfl (fun j _ => h₀) (fun j _ => rfl)
    hread (Or.inr ⟨rfl, hsucc⟩)
  rwa [gameSymPt_mark, ← hread, Function.update_eq_self] at h

open Classical in
/-- **A rewind walks back to the lowest position and hands over.** It starts
anywhere strictly below the right sentinel – which is where the sweep's last
step leaves it – changes nothing, and ends on the lowest position in the phase
`DescriptiveComplexity.MachPh.rewindTarget` names. -/
theorem rewind_run (h₀ : IsBot a₀) {ρ σ : B.Assignment A} (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt (MachPh.rewindPh r tgt cont par) fun _ => a₀)
    (hpos : (𝕄).Posn c.head) (hne : c.head ≠ rightPt a₀) (hlow : c.head ≠ leftPt a₀ false)
    (htape : ∀ p, (𝕄).Posn p → c.tape p = tapeOfAssign a₀ hdim ρ σ p) :
    ∃ c', Relation.ReflTransGen (fun x y => (𝕄).toTMData.Step x y ∧ x.state = c.state) c c' ∧
      c'.state = phasePt (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par))
        (fun _ => a₀) ∧
      c'.head = leftPt a₀ false ∧
      ∀ p, (𝕄).Posn p → c'.tape p = tapeOfAssign a₀ hdim ρ σ p := by
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  have hminl : MinPos (𝕄).Le (𝕄).Posn (leftPt a₀ false) :=
    minPos_leftPt h₀ (carity := ctrlArity vars)
  -- at the lowest position and nowhere else
  have hminiff : ∀ p : GamePt B V M A, MinPos (𝕄).Le (𝕄).Posn p ↔ p = leftPt a₀ false :=
    fun p => ⟨fun h => hlin.2.2.1 _ _ (h.2 _ hminl.1) (hminl.2 _ h.1), fun h => h ▸ hminl⟩
  set target : GamePt B V M A :=
    phasePt (MachPh.rewindTarget (MachPh.rewindPh r tgt cont par)) (fun _ => a₀) with htarget
  set Inv : Config (GamePt B V M A) → Prop := fun d =>
    (∀ p, (𝕄).Posn p → d.tape p = tapeOfAssign a₀ hdim ρ σ p) ∧ d.head ≠ rightPt a₀ ∧
      ((d.state = c.state ∧ d.head ≠ leftPt a₀ false) ∨
        (d.state = target ∧ d.head = leftPt a₀ false)) with hInvDef
  -- a step to a lower position stays clear of the right sentinel
  have hlower : ∀ {x y : GamePt B V M A}, SuccPos (𝕄).Le (𝕄).Posn x y → y ≠ rightPt a₀ →
      x ≠ rightPt a₀ := by
    rintro x y hs hy rfl
    exact hy (hlin.2.2.1 _ _ ((maxPos_rightPt h₀ (carity := ctrlArity vars)).2 _ hs.2.1)
      hs.2.2.1)
  have hstep : ∀ d, Inv d → (𝕄).Posn d.head → ¬ MinPos (𝕄).Le (𝕄).Posn d.head →
      ∃ d', (𝕄).toTMData.Step d d' ∧ SuccPos (𝕄).Le (𝕄).Posn d'.head d.head ∧ Inv d' := by
    intro d hInv hposd hnmin
    have hdc : d.state = c.state := by
      rcases hInv.2.2 with ⟨h, -⟩ | ⟨-, hh⟩
      · exact h
      · exact absurd ((hminiff _).mpr hh) hnmin
    have hd : d.state = phasePt (MachPh.rewindPh r tgt cont par) (fun _ => a₀) := hdc.trans hstate
    have hread : d.tape d.head = tapeOfAssign a₀ hdim ρ σ d.head := hInv.1 _ hposd
    rcases posn_cases h₀ hposd.1 hposd.2 with ⟨b, hb⟩ | ⟨r₀, i, ā, hcell⟩ | hr
    · cases b with
      | false => exact absurd ((hminiff _).mpr hb) hnmin
      | true =>
        have hsucc : SuccPos (𝕄).Le (𝕄).Posn (leftPt a₀ false) d.head := by
          rw [hb]; exact succPos_leftPt h₀ (carity := ctrlArity vars)
        exact ⟨_, rewind_step_left h₀ d hd (by rw [hread, hb, tapeOfAssign_leftPt]) hsucc,
          hsucc, hInv.1, leftPt_ne_rightPt a₀ false, Or.inr ⟨rfl, rfl⟩⟩
    · obtain ⟨h', hsucc⟩ := exists_predPos hlin hposd hnmin
      have hs' : SuccPos (𝕄).Le (𝕄).Posn h' (cellPt a₀ r₀ i ā) := hcell ▸ hsucc
      have hnl : h' ≠ leftPt a₀ false :=
        succPos_ne_leftPt (carity := ctrlArity vars) h₀ (one_lt_fam_cellPt (a₀ := a₀) r₀ i ā) hs'
      exact ⟨_, rewind_step_cell h₀ d hd (by rw [hread, hcell, tapeOfAssign_cellPt]) hsucc,
        hsucc, hInv.1, hlower hsucc hInv.2.1, Or.inl ⟨hdc, hnl⟩⟩
    · exact absurd hr hInv.2.1
  obtain ⟨d, hreach, hmin, hInv⟩ := exists_reach_minPos (M := (𝕄).toTMData) hlin
    (fun d hd hnmin => by
      rcases hd.2.2 with ⟨h, -⟩ | ⟨-, hh⟩
      · exact h
      · exact absurd ((hminiff _).mpr hh) hnmin) hstep c
    ⟨htape, hne, Or.inl ⟨rfl, hlow⟩⟩ hpos
  have hhd : d.head = leftPt a₀ false := (hminiff _).mp hmin
  refine ⟨d, hreach, ?_, hhd, hInv.1⟩
  rcases hInv.2.2 with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd hhd h
  · exact h

end Rewind

/-! ### The run of a seek

A seek walks right, writing back everything it reads, and stops at the cell
whose symbol answers its test – the address *and* the claimed bit, which is why
a wrong claim is not a stop. It therefore either meets its cell and accepts, or
runs off the tape and, having no rule at the right sentinel, is stuck. Since a
seek is an existential phase, that is a loss: **asking an unprovable question
costs the player who asked.** -/

section Seek

variable {B : SOBlock} {V M : ℕ} {A : Type} [LinearOrder A] [Finite A]
  {vars natoms : GameQuestion → ℕ} {pol : GameQuestion → ℕ → Bool}
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V}
  {concOk : MachPh V M → (Fin (gameDim B V) → A) → Prop}
  {isTarget : MachPh V M → SymTag B → (Fin (gameDim B V) → A) → Prop}
  {ph : MachPh V M} {v : Fin (gameDim B V) → A}

local notation "𝕄" => gameMachine vars pol a₀ hdim (gameRule vars natoms concOk isTarget)

variable (a₀ isTarget ph v) in
/-- **The cell a seek is looking for**: a cell whose symbol – the bit included –
answers the phase's test at the address the valuation gives. The bit is read off
the tape, so this is where a claim being right or wrong is decided. -/
def SeekHit (tape : GamePt B V M A → GamePt B V M A) (p : GamePt B V M A) : Prop :=
  ∃ (b rr : Bool) (i : B.ι) (ā : Fin (B.arity i) → A), p = cellPt a₀ rr i ā ∧
    tape p = valPt a₀ b rr i ā ∧ isTarget ph (SymTag.val b rr i) (walkTuple v (pad a₀ ā))

omit [LinearOrder A] [Finite A] in
/-- A sentinel is never the cell a seek is looking for. -/
theorem not_seekHit_leftPt {tape : GamePt B V M A → GamePt B V M A} (b : Bool) :
    ¬ SeekHit a₀ isTarget ph v tape (leftPt a₀ b) := by
  rintro ⟨-, rr, i, ā, hc, -, -⟩
  exact leftPt_ne_cellPt a₀ b rr i ā hc

omit [LinearOrder A] [Finite A] in
theorem not_seekHit_rightPt {tape : GamePt B V M A → GamePt B V M A} :
    ¬ SeekHit a₀ isTarget ph v tape (rightPt a₀) := by
  rintro ⟨-, rr, i, ā, hc, -, -⟩
  exact rightPt_ne_cellPt a₀ rr i ā hc

omit [Finite A] in
open Classical in
/-- **A seek crosses a sentinel**, changing nothing. -/
theorem seek_step_left (hk : ph.kind = .seek)
    (harity : MachPh.arity vars ph ≤ V) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt ph v) (hcv : Canon (MachPh.arity vars ph) v)
    (hread : c.tape c.head = markPt a₀ false)
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head h') :
    (𝕄).toTMData.Step c ⟨c.state, h', c.tape⟩ := by
  have h := step_of_rule (t := ⟨ph, ph, .mark false, .mark false, true⟩)
      (w := walkTuple v fun _ => a₀)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, rfl, rfl, rfl, rfl⟩)))))))
    c c.state h' (by rw [hstate]; rfl) (by rw [hstate]; exact hcv)
    (by rw [hstate]; exact agree_walkTuple harity v _) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hcv) (by rw [hstate]; exact agree_walkTuple harity v _)
    hread (Or.inl ⟨rfl, hsucc⟩)
  rwa [gameSymPt_mark, ← hread, Function.update_eq_self] at h

omit [Finite A] in
open Classical in
/-- **A seek crosses a cell that is not the one it is looking for**, changing
nothing. -/
theorem seek_step_miss (hk : ph.kind = .seek)
    (harity : MachPh.arity vars ph ≤ V) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt ph v) (hcv : Canon (MachPh.arity vars ph) v)
    {b rr : Bool} {i : B.ι} {ā : Fin (B.arity i) → A}
    (hread : c.tape c.head = valPt a₀ b rr i ā)
    (hmiss : ¬ isTarget ph (SymTag.val b rr i) (walkTuple v (pad a₀ ā)))
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head h') :
    (𝕄).toTMData.Step c ⟨c.state, h', c.tape⟩ := by
  have hsym : (gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ (SymTag.val b rr i)
      (addrOf (walkTuple (V := V) v (pad a₀ ā))) : GamePt B V M A) = valPt a₀ b rr i ā := by
    rw [gameSymPt_val, addrOf_walkTuple, argsOf_pad]
  have h := step_of_rule (t := ⟨ph, ph, .val b rr i, .val b rr i, true⟩)
      (w := walkTuple v (pad a₀ ā))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hk, rfl, rfl, rfl, ⟨b, rr, i, rfl⟩, hmiss⟩))))))))
    c c.state h' (by rw [hstate]; rfl) (by rw [hstate]; exact hcv)
    (by rw [hstate]; exact agree_walkTuple harity v _) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hcv) (by rw [hstate]; exact agree_walkTuple harity v _)
    (by rw [hsym]; exact hread) (Or.inl ⟨rfl, hsucc⟩)
  rwa [hsym, ← hread, Function.update_eq_self] at h

omit [Finite A] in
open Classical in
/-- **A seek stops at the cell it is looking for, and accepts.** -/
theorem seek_step_hit (h₀ : IsBot a₀) (hk : ph.kind = .seek)
    (harity : MachPh.arity vars ph ≤ V) (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt ph v) (hcv : Canon (MachPh.arity vars ph) v)
    {b rr : Bool} {i : B.ι} {ā : Fin (B.arity i) → A}
    (hread : c.tape c.head = valPt a₀ b rr i ā)
    (hhit : isTarget ph (SymTag.val b rr i) (walkTuple v (pad a₀ ā)))
    {h' : GamePt B V M A} (hsucc : SuccPos (𝕄).Le (𝕄).Posn c.head h') :
    (𝕄).toTMData.Step c ⟨phasePt (MachPh.accPh false) (fun _ => a₀), h', c.tape⟩ := by
  have hsym : (gameSymPt (C := GameCtrlTag B V M) (V := V) a₀ (SymTag.val b rr i)
      (addrOf (walkTuple (V := V) v (pad a₀ ā))) : GamePt B V M A) = valPt a₀ b rr i ā := by
    rw [gameSymPt_val, addrOf_walkTuple, argsOf_pad]
  have h := step_of_rule (t := ⟨ph, MachPh.accPh false, .val b rr i, .val b rr i, true⟩)
      (w := walkTuple v (pad a₀ ā))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hk, rfl, rfl, rfl, hhit⟩))))))))
    c (phasePt (MachPh.accPh false) fun _ => a₀) h'
    (by rw [hstate]; rfl) (by rw [hstate]; exact hcv)
    (by rw [hstate]; exact agree_walkTuple harity v _) rfl (fun j _ => h₀)
    (fun j hj => absurd hj (by simp)) (by rw [hsym]; exact hread) (Or.inl ⟨rfl, hsucc⟩)
  rwa [hsym, ← hread, Function.update_eq_self] at h

open Classical in
/-- **A seek either meets its cell and accepts, or runs off the tape** – and
then no cell at all answered its test, which is how a false claim is punished.
It starts on a sentinel, where nothing below it can have been passed. -/
theorem seek_run (h₀ : IsBot a₀) (hk : ph.kind = .seek)
    (harity : MachPh.arity vars ph ≤ V) (hcv : Canon (MachPh.arity vars ph) v)
    {ρ σ : B.Assignment A} (c : Config (GamePt B V M A))
    (hstate : c.state = phasePt ph v) {bhd : Bool} (hhead : c.head = leftPt a₀ bhd)
    (htape : ∀ p, (𝕄).Posn p → c.tape p = tapeOfAssign a₀ hdim ρ σ p) :
    ∃ c', Relation.ReflTransGen (fun x y => (𝕄).toTMData.Step x y ∧ x.state = c.state) c c' ∧
      c'.tape = c.tape ∧
      (c'.state = phasePt (MachPh.accPh false) (fun _ => a₀) ∨
        (c'.state = c.state ∧ c'.head = rightPt a₀ ∧
          ∀ p, (𝕄).Posn p → ¬ SeekHit a₀ isTarget ph v (tapeOfAssign a₀ hdim ρ σ) p)) := by
  have hlin : IsLinOrd (𝕄).Le := isLinOrd_gameLe
  have hmaxr : MaxPos (𝕄).Le (𝕄).Posn (rightPt a₀) :=
    maxPos_rightPt h₀ (carity := ctrlArity vars)
  -- the tape never changes, so the symbol under the head is known throughout
  set Hit : GamePt B V M A → Prop := SeekHit a₀ isTarget ph v (tapeOfAssign a₀ hdim ρ σ)
    with hHit
  set Inv : Config (GamePt B V M A) → Prop := fun d =>
    d.tape = c.tape ∧ d.state = c.state ∧
      ∀ p, (𝕄).Posn p → (𝕄).Le p d.head → p ≠ d.head → ¬ Hit p with hInvDef
  have hstep : ∀ d, Inv d → (𝕄).Posn d.head → ¬ MaxPos (𝕄).Le (𝕄).Posn d.head →
      ¬ Hit d.head →
      ∃ d', (𝕄).toTMData.Step d d' ∧ SuccPos (𝕄).Le (𝕄).Posn d.head d'.head ∧ Inv d' := by
    intro d hInv hposd hnmax hnhit
    obtain ⟨h', hsucc⟩ := TMData.exists_succPos' (M := (𝕄).toTMData) hlin hposd hnmax
    have hd : d.state = phasePt ph v := hInv.2.1.trans hstate
    have hread : d.tape d.head = tapeOfAssign a₀ hdim ρ σ d.head := by
      rw [hInv.1]; exact htape _ hposd
    -- the invariant of the successor, from the one at the head
    have hnext : Inv ⟨d.state, h', d.tape⟩ := by
      refine ⟨hInv.1, hInv.2.1, fun p hp hle hne => ?_⟩
      rcases (below_succPos hlin hsucc hp).mp ⟨hle, hne⟩ with ⟨hle', hne'⟩ | rfl
      · exact hInv.2.2 p hp hle' hne'
      · exact hnhit
    rcases posn_cases h₀ hposd.1 hposd.2 with ⟨b, hb⟩ | ⟨r₀, i, ā, hcell⟩ | hr
    · exact ⟨_, seek_step_left hk harity d hd hcv
        (by rw [hread, hb, tapeOfAssign_leftPt]) hsucc, hsucc, hnext⟩
    · refine ⟨_, seek_step_miss hk harity d hd hcv (b := decide (cond r₀ σ ρ i ā))
        (by rw [hread, hcell, tapeOfAssign_cellPt]) (fun hc => hnhit ?_) hsucc, hsucc, hnext⟩
      exact ⟨_, r₀, i, ā, hcell, by rw [hcell, tapeOfAssign_cellPt], hc⟩
    · exact absurd (hr ▸ hmaxr) hnmax
  -- nothing below a sentinel is a cell, so the walk starts clear
  have hstart : Inv c := by
    refine ⟨rfl, rfl, fun p hp hle hne => ?_⟩
    have hle' : (𝕄).Le p (leftPt a₀ true) := by
      cases bhd with
      | false =>
        exact hlin.2.1 _ _ _ (hhead ▸ hle) (succPos_leftPt h₀ (carity := ctrlArity vars)).2.2.1
      | true => exact hhead ▸ hle
    rcases eq_leftPt_of_le h₀ hp hle' with rfl | rfl
    · exact not_seekHit_leftPt false
    · exact not_seekHit_leftPt true
  obtain ⟨d, hreach, hstop, hInv⟩ :=
    exists_reach_stop (M := (𝕄).toTMData) (Stop := fun e => Hit e.head) hlin
      (fun d hd _ _ => hd.2.1) hstep c hstart
      (hhead ▸ ⟨trivial, fun j _ => h₀⟩)
  rcases hstop with hhit | hmax
  · -- the cell was met: one more step accepts
    obtain ⟨b, rr, i, ā, hcell, hsym, htgt⟩ := hhit
    have hposd : (𝕄).Posn d.head := by
      rw [hcell]; exact ⟨trivial, machDom_cellPt a₀ h₀ rr i ā⟩
    have hnmax : ¬ MaxPos (𝕄).Le (𝕄).Posn d.head := by
      intro hm
      exact rightPt_ne_cellPt a₀ rr i ā
        ((hlin.2.2.1 _ _ (hm.2 _ hmaxr.1) (hmaxr.2 _ hm.1)).trans hcell)
    obtain ⟨h', hsucc⟩ := TMData.exists_succPos' (M := (𝕄).toTMData) hlin hposd hnmax
    refine ⟨_, hreach.tail ⟨seek_step_hit h₀ hk harity d (hInv.2.1.trans hstate) hcv
      (b := b) (rr := rr) (i := i) (ā := ā) ?_ htgt hsucc, hInv.2.1⟩, hInv.1, Or.inl rfl⟩
    rw [hInv.1, htape _ hposd, hsym]
  · -- the tape ran out: no cell answered
    have hhr : d.head = rightPt a₀ := hlin.2.2.1 _ _ (hmaxr.2 _ hmax.1) (hmax.2 _ hmaxr.1)
    refine ⟨d, hreach, hInv.1, Or.inr ⟨hInv.2.1, hhr, fun p hp => ?_⟩⟩
    by_cases hpe : p = d.head
    · rw [hpe, hhr]; exact not_seekHit_rightPt
    · exact hInv.2.2 p hp (hmax.2 p hp) hpe

end Seek

end DescriptiveComplexity
