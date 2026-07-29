/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Program
import DescriptiveComplexity.OrderedComposition
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Interval.Finset.Fin

/-!
# The tape of the alternating QBF machine

The layout half of `QBF k ≤ᶠᵒ[≤] ATMAccept k`: which tagged tuples are
positions, in what order they sit, and why there are enough of them. It is the
tape of `DescriptiveComplexity.Problems.Machine.Tape` with the guessing phase
split into `k` sweeps.

## The layout

```
  ⊢   x₁ x₂ … xₙ   ⊣   fillers…
```

one cell per element, bracketed by two markers, then filler cells that exist
only to supply time – exactly as for the SAT machine. What changes is the
*symbol* in a cell and the number of tags.

**A cell holds a truth value, not an “unassigned” mark.** The value of a
variable under a tuple of block assignments is
`DescriptiveComplexity.qbfVal`, which is a *disjunction*: `x` is true when
*some* block marking it assigns it true. A variable may carry several block
marks, or none. So the cell of `x` starts at `false` and sweep `i` may turn it
to `true`; after all `k` sweeps it holds the disjunction, and a variable no
block marks stays false – which is what `qbfVal` says about it. Monotone
accumulation is what makes one bit per cell enough.

## The tags, and why the order is by key

The SAT machine numbers its tags by hand. Here the families are indexed by `k`,
so the numbering is a *pair* – a family index and an offset inside the family –
ordered lexicographically (`DescriptiveComplexity.altTagKey`). The position
families come first, so the order of the positions is undisturbed by the
program's tags, exactly as `DescriptiveComplexity.satTagIdx` arranges.

## The budget

Each of the `k` sweeps goes right and comes back, so `2k(n + 2)` steps, and the
check costs `(m + 1)(n + 2)` for `m ≤ n` clauses: at most `(2k + n + 1)(n + 2)`.
The `8(k + 1)` filler tags at dimension two supply `8(k + 1)n²` positions on
their own, and `DescriptiveComplexity.alt_budget` says that is always more –
the filler is over-provisioned rather than the bound tightened, as in
`DescriptiveComplexity.sat_budget`.
-/

namespace DescriptiveComplexity

namespace AltQbf

open FirstOrder

/-! ### The tags of the positions -/

/-- The base tags of the alternating QBF machine: everything but the sweep
index, which a tag carries alongside. Keeping this type independent of `k` is
what makes its numbering – and hence the tape order – a `decide`. -/
inductive AltBase : Type
  /-- The left marker cell. -/
  | pStart
  /-- The cell of an element: one per element of the instance. -/
  | pCell
  /-- The right marker cell. -/
  | pEnd
  /-- Filler cells, eight base tags' worth, each with `k + 1` sweep indices. -/
  | pFill (i : Fin 8)
  /-- The left-marker symbol `⊢`. -/
  | sStart
  /-- The right-marker symbol `⊣`. -/
  | sEnd
  /-- The blank symbol. -/
  | sBlank
  /-- The symbol `(x, b)`: the cell of `x`, currently holding the truth value
  `b`. -/
  | sVal (b : Bool)
  /-- A guessing sweep, sweeping in direction `d` (`true` = rightwards); which
  sweep is the tag's index. -/
  | qG (d : Bool)
  /-- Checking a clause with the accumulated flag `f`, sweeping in direction
  `d`. -/
  | qChk (f d : Bool)
  /-- The accepting state. -/
  | qAcc
  /-- A sweep: step over the left marker, rightwards. -/
  | tGStart
  /-- A sweep, rightwards: leave a cell holding `b` alone. -/
  | tGKeep (b : Bool)
  /-- A sweep, rightwards: turn a cell of a variable this block marks from
  `false` to `true`. -/
  | tGSet
  /-- A sweep: turn round at the right marker. -/
  | tGTurn
  /-- A sweep, leftwards: step back over a cell holding `b`. -/
  | tGBack (b : Bool)
  /-- A sweep: at the left marker, hand over to the next sweep. -/
  | tGNext
  /-- The last sweep is over and there is no clause: accept. -/
  | tGEndAcc
  /-- The last sweep is over: start checking the lowest clause. -/
  | tGEndChk
  /-- Check phase: read `(x, b)` with flag `f`, sweeping in direction `d`. -/
  | tChk (b f d : Bool)
  /-- Check phase: the clause is settled and another one follows. -/
  | tTurnNext (d : Bool)
  /-- Check phase: the clause is settled and it was the last one. -/
  | tTurnAcc (d : Bool)
  deriving DecidableEq, Fintype

instance : Nonempty AltBase := ⟨AltBase.pStart⟩

/-- The position of a base tag in the tape order. -/
def altBaseIdx : AltBase → ℕ
  | .pStart => 0
  | .pCell => 1
  | .pEnd => 2
  | .pFill i => 3 + (i : ℕ)
  | .sStart => 11
  | .sEnd => 12
  | .sBlank => 13
  | .sVal b => 14 + (if b then 1 else 0)
  | .qG d => 16 + (if d then 1 else 0)
  | .qChk f d => 18 + (if f then 1 else 0) + (if d then 2 else 0)
  | .qAcc => 22
  | .tGStart => 23
  | .tGKeep b => 24 + (if b then 1 else 0)
  | .tGSet => 26
  | .tGTurn => 27
  | .tGBack b => 28 + (if b then 1 else 0)
  | .tGNext => 30
  | .tGEndAcc => 31
  | .tGEndChk => 32
  | .tChk b f d => 33 + (if b then 1 else 0) + (if f then 2 else 0) + (if d then 4 else 0)
  | .tTurnNext d => 41 + (if d then 1 else 0)
  | .tTurnAcc d => 43 + (if d then 1 else 0)

theorem altBaseIdx_injective : Function.Injective altBaseIdx := by decide

/-- The tags of the tape: a base tag together with a sweep index. The index is
the sweep a guessing state or transition belongs to, and the second coordinate
of a filler cell; everywhere else it is pinned to `0` by
`DescriptiveComplexity.AltPosn` and the machine's own definitions. -/
abbrev AltTag (k : ℕ) : Type := AltBase × Fin (k + 1)

/-- The sort key of a tag: the base tag, then the sweep index. -/
def altTagKey {k : ℕ} (t : AltTag k) : Lex (ℕ × ℕ) := toLex (altBaseIdx t.1, (t.2 : ℕ))

theorem altTagKey_injective {k : ℕ} : Function.Injective (altTagKey (k := k)) := by
  intro s t h
  have h' : (altBaseIdx s.1, (s.2 : ℕ)) = (altBaseIdx t.1, (t.2 : ℕ)) := congrArg ofLex h
  exact Prod.ext (altBaseIdx_injective (congrArg Prod.fst h')) (Fin.ext (congrArg Prod.snd h'))

/-- **The tape order on tags**: the base tag first, then the sweep index. The
position families come first, so the program's tags never disturb the order of
the positions. -/
instance (k : ℕ) : LinearOrder (AltTag k) :=
  LinearOrder.lift' altTagKey altTagKey_injective

/-! ### The intended positions -/

section Positions

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- The tagged tuples that are positions: the two markers are the single tuple
of minima, an element's cell is that element in the first coordinate, and the
fillers are unrestricted. -/
def AltPosn (p : AltTag k × (Fin 2 → A)) : Prop :=
  match p.1.1 with
  | .pStart => (p.1.2 : ℕ) = 0 ∧ ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pCell => (p.1.2 : ℕ) = 0 ∧ ∀ a : A, p.2 1 ≤ a
  | .pEnd => (p.1.2 : ℕ) = 0 ∧ ∀ a : A, p.2 0 ≤ a ∧ p.2 1 ≤ a
  | .pFill _ => True
  | _ => False

/-- The tuple of minima: the coordinates a marker or a constant symbol is
pinned to, so that exactly one tuple carries such a tag. -/
def IsMinTup2 (w : Fin 2 → A) : Prop := (∀ a : A, w 0 ≤ a) ∧ ∀ a : A, w 1 ≤ a

theorem isMinTup2_unique {w w' : Fin 2 → A} (h : IsMinTup2 w) (h' : IsMinTup2 w') : w = w' := by
  funext i
  fin_cases i
  · exact le_antisymm (h.1 _) (h'.1 _)
  · exact le_antisymm (h.2 _) (h'.2 _)

variable [Finite A] [Nonempty A]

theorem exists_isMinTup2 : ∃ w : Fin 2 → A, IsMinTup2 w := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  exact ⟨fun _ => m, hm, hm⟩

/-- The blank symbol: one element, pinned to the tuple of minima. -/
def AltBlank (p : AltTag k × (Fin 2 → A)) : Prop :=
  p.1 = (AltBase.sBlank, 0) ∧ IsMinTup2 p.2

theorem exists_altBlank : ∃ p : AltTag k × (Fin 2 → A), AltBlank p := by
  obtain ⟨w, hw⟩ := exists_isMinTup2 (A := A)
  exact ⟨((AltBase.sBlank, 0), w), rfl, hw⟩

omit [Finite A] [Nonempty A] in
theorem altBlank_unique {p q : AltTag k × (Fin 2 → A)} (hp : AltBlank p) (hq : AltBlank q) :
    p = q :=
  Prod.ext (hp.1.trans hq.1.symm) (isMinTup2_unique hp.2 hq.2)

/-- **The initial tape**: the markers hold their own symbols and the cell of an
element holds that element with the truth value `false` – no block has assigned
anything yet. The fillers hold the blank. -/
def AltInp (p a : AltTag k × (Fin 2 → A)) : Prop :=
  (p.1.1 = AltBase.pStart ∧ a.1 = (AltBase.sStart, 0) ∧ IsMinTup2 a.2) ∨
    (p.1.1 = AltBase.pCell ∧ a.1 = (AltBase.sVal false, 0) ∧ a.2 0 = p.2 0 ∧
        ∀ b : A, a.2 1 ≤ b) ∨
      (p.1.1 = AltBase.pEnd ∧ a.1 = (AltBase.sEnd, 0) ∧ IsMinTup2 a.2)

omit [Finite A] [Nonempty A] in
/-- **The initial tape is functional**: a cell holds at most one symbol. -/
theorem altInp_functional {p a b : AltTag k × (Fin 2 → A)} (ha : AltInp p a) (hb : AltInp p b) :
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
        | exact Prod.ext (hat.trans hbt.symm) (isMinTup2_unique haw hbw)
        | exact Prod.ext (hat.trans hbt.symm) (htup _ _ ha0 ha1 hb0 hb1)
        | (rw [hp] at hq; exact absurd hq (by simp))

/-- There is a position: the start marker. -/
theorem exists_altPosn : ∃ p : AltTag k × (Fin 2 → A), AltPosn p := by
  obtain ⟨w, hw⟩ := exists_isMinTup2 (A := A)
  exact ⟨((AltBase.pStart, 0), w), rfl, fun a => ⟨hw.1 a, hw.2 a⟩⟩

omit [Finite A] [Nonempty A] in
private theorem isLinOrd_of_linearOrder {X : Type} (o : LinearOrder X) : IsLinOrd o.le :=
  ⟨fun a => @le_refl X o.toPreorder a, fun a b c => @le_trans X o.toPreorder a b c,
    fun a b => @le_antisymm X o.toPartialOrder a b, fun a b => @le_total X o a b⟩

omit [Finite A] [Nonempty A] in
/-- **The interpreted order is linear**, from `DescriptiveComplexity.tagTupleOrder`. -/
theorem isLinOrd_altTagTupleLe :
    IsLinOrd (tagTupleLe (Tag := AltTag k) (d := 2) (A := A)) := by
  have heq : (tagTupleLe (Tag := AltTag k) (d := 2) (A := A)) =
      (tagTupleOrder : LinearOrder (AltTag k × (Fin 2 → A))).le := by
    funext p q
    exact propext (tagTupleLe_iff_le p q)
  rw [heq]
  exact isLinOrd_of_linearOrder _

end Positions

/-! ### The budget -/

/-- **The filler cells alone are enough.** The `k` sweeps cost `2k(n + 2)`
steps, the check `(m + 1)(n + 2)` for `m ≤ n` clauses, and the `8(k + 1)`
filler tags contribute `8(k + 1)n²` positions by themselves.

The inequality is strict, as `DescriptiveComplexity.TMData.Accepts` requires. -/
theorem alt_budget {k n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    (2 * k + m + 1) * (n + 2) < 8 * (k + 1) * n * n := by
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have h1 : (2 * k + m + 1) * (n + 2) ≤ (2 * k + n + 1) * (n + 2) := by
    exact Nat.mul_le_mul_right _ (by omega)
  nlinarith [h1, hnn]

/-- **The tape really has that many positions**: the filler tuples alone inject
into the positions. -/
theorem alt_card_le_card_posn (k : ℕ) (A : Type) [LinearOrder A] [Finite A] :
    8 * (k + 1) * Nat.card A * Nat.card A ≤
      Nat.card {p : AltTag k × (Fin 2 → A) // AltPosn p} := by
  have hinj : Function.Injective
      (fun q : (Fin 8 × Fin (k + 1)) × A × A =>
        (⟨((AltBase.pFill q.1.1, q.1.2), ![q.2.1, q.2.2]), trivial⟩ :
          {p : AltTag k × (Fin 2 → A) // AltPosn p})) := by
    rintro ⟨⟨i, j⟩, a, b⟩ ⟨⟨i', j'⟩, a', b'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Prod.mk.injEq, AltBase.pFill.injEq] at h'
    obtain ⟨⟨hi, hj⟩, hw⟩ := h'
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    simp [hi, hj, h0, h1]
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, mul_assoc] using this

end AltQbf

end DescriptiveComplexity
