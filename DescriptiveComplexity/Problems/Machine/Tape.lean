/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.OrderedComposition
import Mathlib.Data.Fintype.Lattice

/-!
# The tape of the SAT machine

The layout half of `SAT ≤ᶠᵒ[≤] NTMAccept`: which tagged tuples are positions, in
what order they sit, and why there are enough of them. The program that runs on
this tape – states, symbols, transitions – is separate.

## The layout

The machine's tape is one cell per element of the instance, bracketed by two
markers, followed by filler cells that exist only to supply time:

```
  ⊢   x₁ x₂ … xₙ   ⊣   fillers…
```

`Satisfiable` assigns a truth value to *every* element (elements that are not
variables of any clause are harmless), so there is no need to single out the
variables: one cell per element is both simpler and correct.

Tags are ordered so that this is exactly the order of the interpreted universe.
That order comes for free: `DescriptiveComplexity.lexLeF` is the defining formula of
`le` – tags first, then the tuple lexicographically – and
`DescriptiveComplexity.tagTupleOrder` is already a `LinearOrder`, so the well-formedness
obligation `IsLinOrd` of `DescriptiveComplexity.TMData.WellFormed` is discharged without
a single tag-pair case.

Only the *position* tags are fixed here. The symbol, state and transition tags
of the program get higher indices, which leaves the order of the positions
undisturbed – `DescriptiveComplexity.satTagIdx` is what has to stay monotone, not the
constructor list.

## The budget

The machine needs one sweep to guess an assignment and one sweep per clause to
check it, so `(m + 1) · (n + 2)` steps for `n` elements and `m ≤ n` clauses.
Eight filler tags at dimension two give `8n²` positions on their own – no need
to count the markers and cells – and `DescriptiveComplexity.sat_budget` says that is
always more than the machine needs. Following the plan's advice
on risk #3, the filler is over-provisioned rather than the bound tightened:
nothing downstream depends on the constant, and an off-by-one here would only
surface at the very end of the correctness proof.
-/

namespace DescriptiveComplexity

open FirstOrder

/-! ### The tags of the positions -/

/-- The tags carrying the tape of the SAT machine. The order of the
constructors is the order of the tape; `DescriptiveComplexity.satTagIdx` is what makes
that official.

The program's tags (symbols, states, transitions) will be added after these
with higher indices, which does not disturb the order of the positions. -/
inductive SatTag : Type
  /-- The left marker cell. -/
  | pStart
  /-- The cell of an element: one per element of the instance. -/
  | pCell
  /-- The right marker cell. -/
  | pEnd
  /-- Filler cells, eight tags' worth, supplying the time budget. -/
  | pFill (i : Fin 8)
  /-- The left-marker symbol `⊢`. -/
  | sStart
  /-- The right-marker symbol `⊣`. -/
  | sEnd
  /-- The blank symbol. -/
  | sBlank
  /-- The symbol `(x, U)`: the cell of `x`, not yet assigned. -/
  | sU
  /-- The symbol `(x, T)`: the cell of `x`, assigned true. -/
  | sT
  /-- The symbol `(x, F)`: the cell of `x`, assigned false. -/
  | sF
  /-- The guessing state. -/
  | qGuess
  /-- Checking clause `c` with the accumulated flag `f`, sweeping in direction
  `d` (`true` = rightwards). -/
  | qChk (f d : Bool)
  /-- The accepting state. -/
  | qAcc
  /-- Guess phase: step over the left marker. -/
  | tGuessStart
  /-- Guess phase: write the truth value `b` in an unassigned cell. -/
  | tGuessVal (b : Bool)
  /-- Guess phase over, and there is no clause: accept. -/
  | tGuessEndAcc
  /-- Guess phase over: start checking the lowest clause. -/
  | tGuessEndChk
  /-- Check phase: read `(x, b)` with flag `f`, sweeping in direction `d`. -/
  | tChk (b f d : Bool)
  /-- Check phase: the clause is satisfied and another one follows. -/
  | tTurnNext (d : Bool)
  /-- Check phase: the clause is satisfied and it was the last one. -/
  | tTurnAcc (d : Bool)
  deriving DecidableEq, Fintype

instance : Nonempty SatTag := ⟨SatTag.pStart⟩

/-- The position of a tag in the tape order. -/
def satTagIdx : SatTag → ℕ
  | .pStart => 0
  | .pCell => 1
  | .pEnd => 2
  | .pFill i => 3 + (i : ℕ)
  | .sStart => 11
  | .sEnd => 12
  | .sBlank => 13
  | .sU => 14
  | .sT => 15
  | .sF => 16
  | .qGuess => 17
  | .qChk f d => 18 + (if f then 1 else 0) + (if d then 2 else 0)
  | .qAcc => 22
  | .tGuessStart => 23
  | .tGuessVal b => 24 + (if b then 1 else 0)
  | .tGuessEndAcc => 26
  | .tGuessEndChk => 27
  | .tChk b f d => 28 + (if b then 1 else 0) + (if f then 2 else 0) + (if d then 4 else 0)
  | .tTurnNext d => 36 + (if d then 1 else 0)
  | .tTurnAcc d => 38 + (if d then 1 else 0)

theorem satTagIdx_injective : Function.Injective satTagIdx := by
  have hb : ∀ b : Bool, (if b then 1 else 0) < 2 := by decide
  intro s t h
  cases s <;> cases t <;>
    simp only [satTagIdx] at h ⊢ <;>
      first
        | rfl
        | omega
        | (rename_i i j; exact congrArg _ (Fin.ext (by omega)))
        | (rename_i i; omega)
        | (repeat' first | rfl | (rename_i b; cases b) | omega | simp_all)

/-- The tape order on tags. -/
instance : LinearOrder SatTag := LinearOrder.lift' satTagIdx satTagIdx_injective

theorem satTag_lt_iff {s t : SatTag} : s < t ↔ satTagIdx s < satTagIdx t := Iff.rfl

theorem satTag_le_iff {s t : SatTag} : s ≤ t ↔ satTagIdx s ≤ satTagIdx t := Iff.rfl

/-! ### The intended positions

Stated as a plain predicate on tagged tuples, in the style of
`DescriptiveComplexity.IAdjRaw`: the interpretation's `posn` formula will be shown to
realize exactly this, and every fact proved here transfers. -/

section Positions

variable {A : Type} [LinearOrder A]

/-- The tagged tuples that are positions: the two markers are the single tuple
of minima, an element's cell is that element in the first coordinate, and the
fillers are unrestricted. -/
def SatPosn (p : SatTag × (Fin 2 → A)) : Prop :=
  match p.1 with
  | .pStart => ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pCell => ∀ a : A, p.2 1 ≤ a
  | .pEnd => ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pFill _ => True
  | _ => False

/-- There is exactly one start marker. -/
theorem satPosn_pStart_iff {w : Fin 2 → A} :
    SatPosn (SatTag.pStart, w) ↔ (∀ a : A, w 0 ≤ a) ∧ ∀ a : A, w 1 ≤ a :=
  ⟨fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩, fun h a => ⟨h.1 a, h.2 a⟩⟩

/-- A cell is a position exactly when its second coordinate is the minimum: one
cell per element, indexed by the first coordinate. -/
theorem satPosn_pCell_iff {w : Fin 2 → A} :
    SatPosn (SatTag.pCell, w) ↔ ∀ a : A, w 1 ≤ a := Iff.rfl

/-- Every filler tuple is a position. -/
theorem satPosn_pFill {i : Fin 8} {w : Fin 2 → A} : SatPosn (SatTag.pFill i, w) := trivial

/-! ### The instance data of the machine

The order, the blank symbol and the initial tape – everything
`DescriptiveComplexity.TMData.WellFormed` asks about, which is therefore discharged here
once, before any transition exists. -/

/-- The tuple of minima: the coordinates a marker or a constant symbol is
pinned to, so that exactly one tuple carries such a tag. -/
def IsMinTup (w : Fin 2 → A) : Prop := (∀ a : A, w 0 ≤ a) ∧ ∀ a : A, w 1 ≤ a

theorem isMinTup_unique {w w' : Fin 2 → A} (h : IsMinTup w) (h' : IsMinTup w') : w = w' := by
  funext i
  fin_cases i
  · exact le_antisymm (h.1 _) (h'.1 _)
  · exact le_antisymm (h.2 _) (h'.2 _)

variable [Finite A] [Nonempty A]

theorem exists_isMinTup : ∃ w : Fin 2 → A, IsMinTup w := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  exact ⟨fun _ => m, hm, hm⟩

/-- The blank symbol: one element, pinned to the tuple of minima. -/
def SatBlank (p : SatTag × (Fin 2 → A)) : Prop := p.1 = SatTag.sBlank ∧ IsMinTup p.2

theorem exists_satBlank : ∃ p : SatTag × (Fin 2 → A), SatBlank p := by
  obtain ⟨w, hw⟩ := exists_isMinTup (A := A)
  exact ⟨(SatTag.sBlank, w), rfl, hw⟩

omit [Finite A] [Nonempty A] in
theorem satBlank_unique {p q : SatTag × (Fin 2 → A)} (hp : SatBlank p) (hq : SatBlank q) :
    p = q :=
  Prod.ext (hp.1.trans hq.1.symm) (isMinTup_unique hp.2 hq.2)

/-- **The initial tape**: the markers hold their own symbols, the cell of an
element holds that element still unassigned, and the fillers hold nothing – so
the blank, by `DescriptiveComplexity.TMData.InitTape`. -/
def SatInp (p a : SatTag × (Fin 2 → A)) : Prop :=
  (p.1 = SatTag.pStart ∧ a.1 = SatTag.sStart ∧ IsMinTup a.2) ∨
    (p.1 = SatTag.pCell ∧ a.1 = SatTag.sU ∧ a.2 0 = p.2 0 ∧ ∀ b : A, a.2 1 ≤ b) ∨
      (p.1 = SatTag.pEnd ∧ a.1 = SatTag.sEnd ∧ IsMinTup a.2)

omit [Finite A] [Nonempty A] in
/-- **The initial tape is functional**: a cell holds at most one symbol. The
three cases are separated by the tag of the cell, and within each case the
symbol's tuple is pinned. -/
theorem satInp_functional {p a b : SatTag × (Fin 2 → A)} (ha : SatInp p a) (hb : SatInp p b) :
    a = b := by
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

/-- There is a position: the start marker. -/
theorem exists_satPosn : ∃ p : SatTag × (Fin 2 → A), SatPosn p := by
  obtain ⟨w, hw⟩ := exists_isMinTup (A := A)
  exact ⟨(SatTag.pStart, w), fun a => ⟨hw.1 a, hw.2 a⟩⟩

omit [Finite A] [Nonempty A] in
/-- The `≤` of a `LinearOrder`, as an `DescriptiveComplexity.IsLinOrd`. -/
private theorem isLinOrd_of_linearOrder {X : Type} (o : LinearOrder X) : IsLinOrd o.le :=
  ⟨fun a => @le_refl X o.toPreorder a, fun a b c => @le_trans X o.toPreorder a b c,
    fun a b => @le_antisymm X o.toPartialOrder a b, fun a b => @le_total X o a b⟩

omit [Finite A] [Nonempty A] in
/-- **The interpreted order is linear**, from `DescriptiveComplexity.tagTupleOrder` –
no tag-pair case analysis. -/
theorem isLinOrd_tagTupleLe :
    IsLinOrd (tagTupleLe (Tag := SatTag) (d := 2) (A := A)) := by
  have heq : (tagTupleLe (Tag := SatTag) (d := 2) (A := A)) =
      (tagTupleOrder : LinearOrder (SatTag × (Fin 2 → A))).le := by
    funext p q
    exact propext (tagTupleLe_iff_le p q)
  rw [heq]
  exact isLinOrd_of_linearOrder _

end Positions

/-! ### The budget -/

/-- **The filler cells alone are enough.** The machine takes one sweep to guess
an assignment and one per clause to check it, `(m + 1) · (n + 2)` steps in all
for `n` elements and `m ≤ n` clauses; the eight filler tags contribute `8n²`
positions by themselves, so no count of the markers and cells is needed.

The inequality is strict, as `DescriptiveComplexity.TMData.Accepts` requires: `N`
positions are `N` time points and so `N - 1` steps. -/
theorem sat_budget {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m + 1) * (n + 2) < 8 * n * n := by
  have hstep : (m + 1) * (n + 2) ≤ (n + 1) * (n + 2) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hm)
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  nlinarith [hstep, hnn]

/-- **The tape really has that many positions**: the filler tuples alone inject
into the positions, which is all the budget argument needs. -/
theorem card_le_card_posn (A : Type) [LinearOrder A] [Finite A] :
    8 * Nat.card A * Nat.card A ≤ Nat.card {p : SatTag × (Fin 2 → A) // SatPosn p} := by
  have hinj : Function.Injective
      (fun q : Fin 8 × A × A => (⟨(SatTag.pFill q.1, ![q.2.1, q.2.2]), trivial⟩ :
        {p : SatTag × (Fin 2 → A) // SatPosn p})) := by
    rintro ⟨i, a, b⟩ ⟨i', a', b'⟩ h
    have h' := congrArg Subtype.val h
    obtain ⟨ht, hw⟩ := Prod.mk.injEq .. ▸ h'
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    cases ht
    simp [h0, h1]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 8),
    Fintype.card_fin, ← mul_assoc] at this

end DescriptiveComplexity
