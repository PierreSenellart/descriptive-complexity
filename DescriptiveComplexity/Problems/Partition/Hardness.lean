/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Partition.Defs
import DescriptiveComplexity.Problems.NaeSat
import DescriptiveComplexity.OccurrenceSlack
import DescriptiveComplexity.Numbers.Digits
import DescriptiveComplexity.Padding

/-!
# Partition is NP-hard

Partition asks for a set of items weighing exactly as much as the items it
leaves out. Karp derives it from Knapsack by padding an instance with the two
weights `2Σ − T` and `Σ + T`; both are arithmetic in the total, so that
padding is *not* first-order and the reduction has to start elsewhere. It
starts here from NAE-SAT, whose not-all-equal condition is the two-sided
constraint a balanced split imposes.

## The gadget

One *digit block* per variable and one per clause, in base `2 ^ (3 |A|)`, and
one item per literal, per slack position and per empty clause:

* the item of the literal `(x, s)` has the digit `1` in the block of `x` and
  in the block of every clause where `(x, s)` occurs;
* the block of a variable therefore totals `2`, so a balanced split takes
  exactly one of the two literals of each variable: it *is* an assignment;
* the item of a *slack occurrence* – an occurrence of a clause that is
  neither its first nor its last – has the digit `1` in the block of that
  clause, which brings the total of a clause of width `w` to `w + (w − 2)`;
  a balanced split takes `w − 1` of them, that is, between `1` and `w − 1`
  true literals: exactly not-all-equal satisfaction;
* a clause with no literal at all totals `1` with its own item, an odd digit,
  so no split exists – which is the right answer, an empty clause being
  not-all-equal unsatisfiable. A clause of width one needs no item of its
  own: it has no slack occurrence, so its block already totals `1`.

Nothing here bounds the width, so the reduction starts from NAE-SAT rather
than from its width-three restriction: `w + (w − 2)` is even and the interval
`[1, w − 1]` is the not-all-equal condition at every width.

## What the order is for

Positions are `(block, index)` pairs ordered lexicographically, one block
being `3 |A|` positions, so the lowest position of a block has rank
`3 |A| ·` the rank of the block (`DescriptiveComplexity.PartRed.bitRank_pLow`) – the
two-level analogue of the block structure of the Knapsack reduction. Only
lowest positions ever carry a bit, so weights are read digit by digit, and
`3 |A|` bits keep the base above every digit the gadget writes.

The order of the interpreted structure is described once, by a *key* into
`ℕ × A × ℕ × A` read lexicographically
(`DescriptiveComplexity.PartRed.bwLe_iff`), rather than tag pair by tag pair.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace PartRed

open Language Structure SatOcc

/-! ### The minimum of the order -/

section Mid

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- A minimum of the order, as a formula over the ordered expansion of the
vocabulary of CNF instances. -/
noncomputable def minF {α : Type} (x : α) : satOrd.Formula α := botF (L := Language.sat) x

@[simp]
theorem realize_minF {α : Type} {v : α → A} {x : α} : (minF x).Realize v ↔ IsBot (v x) :=
  realize_botF

end Mid

/-! ### The tags -/

/-- Tags of the reduction. The items are those of the literals, of the slack
occurrences and of the empty clauses; the positions carry a *block* – a
variable block (`false`) or a clause block (`true`) – and an index inside it,
of which `Fin 3` are enough to keep the base above every digit. -/
inductive PTag : Type
  /-- The item of the literal `(x, s)`; its tuple is `(x, ⊥)`. -/
  | lit (s : Bool)
  /-- The item of the slack occurrence `(x, s)` of `c`; its tuple is `(c, x)`. -/
  | slk (s : Bool)
  /-- The item of the empty clause `c`; its tuple is `(c, ⊥)`. -/
  | emp
  /-- The `f`-th position of the block `(k, e)`; its tuple is `(e, y)`. -/
  | pos (k : Bool) (f : Fin 3)
  deriving DecidableEq

instance : Fintype PTag where
  elems :=
    {.lit false, .lit true, .slk false, .slk true, .emp,
      .pos false 0, .pos false 1, .pos false 2, .pos true 0, .pos true 1, .pos true 2}
  complete := by
    intro t
    cases t with
    | lit s => cases s <;> decide
    | slk s => cases s <;> decide
    | emp => decide
    | pos k f => cases k <;> fin_cases f <;> decide

instance : Nonempty PTag := ⟨PTag.emp⟩

/-- The rank of a tag: the items first, then the positions of the variable
blocks, then those of the clause blocks. It is the leading component of the
key, so it separates items from positions and variable blocks from clause
blocks. -/
def tagRk : PTag → ℕ
  | .lit false => 0
  | .lit true => 1
  | .slk false => 2
  | .slk true => 3
  | .emp => 4
  | .pos false _ => 5
  | .pos true _ => 6

/-- The rank of a tag inside a block: the index of a position, and `0` for the
items, which no block holds. -/
def subRk : PTag → ℕ
  | .pos _ f => (f : ℕ)
  | _ => 0

/-- The two ranks together determine the tag. -/
theorem tag_ext {t t' : PTag} (h₁ : tagRk t = tagRk t') (h₂ : subRk t = subRk t') : t = t' := by
  revert h₁ h₂
  revert t t'
  decide

/-! ### The interpretation -/

section Formulas

open SatOcc

/-- Defining formula for the items: one per literal, one per slack occurrence
and one per empty clause. -/
noncomputable def itemF : PTag → satOrd.Formula (Fin 1 × Fin 2)
  | .lit _ => minF (0, 1)
  | .slk s => midF s (0, 0) (0, 1)
  | .emp => emptyClF (0, 0) ⊓ minF (0, 1)
  | .pos _ _ => ⊥

/-- Defining formula for the bit positions: every tagged pair is one. -/
def posnF : PTag → satOrd.Formula (Fin 1 × Fin 2)
  | .pos _ _ => ⊤
  | _ => ⊥

/-- Defining formula for the bits of the weights. Only the lowest position of
a block – index `0`, second coordinate a minimum – ever carries a bit. -/
noncomputable def bitF : PTag → PTag → satOrd.Formula (Fin 2 × Fin 2)
  | .lit s, .pos k f =>
    if f = 0 then
      minF (0, 1) ⊓ minF (1, 1) ⊓ (if k then occF s (1, 0) (0, 0) else eqF (1, 0) (0, 0))
    else ⊥
  | .slk s, .pos k f =>
    if f = 0 ∧ k = true then
      midF s (0, 0) (0, 1) ⊓ minF (1, 1) ⊓ eqF (1, 0) (0, 0)
    else ⊥
  | .emp, .pos k f =>
    if f = 0 ∧ k = true then
      emptyClF (0, 0) ⊓ minF (0, 1) ⊓ minF (1, 1) ⊓ eqF (1, 0) (0, 0)
    else ⊥
  | _, _ => ⊥

/-- Defining formula for the order: the key `(tag rank, first coordinate,
index in the block, second coordinate)`, read lexicographically. -/
def leKF (t t' : PTag) : satOrd.Formula (Fin 2 × Fin 2) :=
  if tagRk t < tagRk t' then ⊤
  else if tagRk t' < tagRk t then ⊥
  else
    SatOcc.ltF (0, 0) (1, 0) ⊔
      (SatOcc.eqF (0, 0) (1, 0) ⊓
        (if subRk t < subRk t' then ⊤
        else if subRk t' < subRk t then ⊥
        else SatOcc.leF (0, 1) (1, 1)))

/-- The interpretation of a binary-weighted instance in a CNF structure: one
item per literal, slack occurrence and empty clause, one block of `3 |A|`
positions per variable and per clause. The target symbol is unused, Partition
carrying no number to reach. -/
noncomputable def pInterp : FOInterpretation satOrd Language.binWeights PTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .item => fun t => itemF (t 0)
    | _, .posn => fun t => posnF (t 0)
    | _, .bit => fun t => bitF (t 0) (t 1)
    | _, .tgt => fun _ => ⊥
    | _, .le => fun t => leKF (t 0) (t 1)

end Formulas

/-! ### The points of the interpreted structure -/

section Points

variable {A : Type}

/-- The point of tag `t` over the pair `w`. -/
def pPt (t : PTag) (w : Fin 2 → A) : pInterp.Map A := (t, w)

theorem pPt_surj (q : pInterp.Map A) : ∃ t w, q = pPt t w := ⟨q.1, q.2, rfl⟩

theorem pPt_eq_iff {t t' : PTag} {w w' : Fin 2 → A} :
    pPt t w = pPt t' w' ↔ t = t' ∧ w = w' := by
  constructor
  · intro h
    exact ⟨congrArg (fun q : pInterp.Map A => q.1) h,
      congrArg (fun q : pInterp.Map A => q.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem pPt_snd (t : PTag) (w : Fin 2 → A) (j : Fin 2) : (pPt t w).2 j = w j := rfl

/-- Two `2`-tuples with the same coordinates are equal. -/
theorem tuple₂_ext {w w' : Fin 2 → A} (h0 : w 0 = w' 0) (h1 : w 1 = w' 1) : w = w' := by
  funext j
  fin_cases j
  · exact h0
  · exact h1

/-- The item of the literal `(x, s)`. -/
def pLit (a₀ : A) (s : Bool) (x : A) : pInterp.Map A := pPt (.lit s) ![x, a₀]

/-- The item of the slack occurrence `(x, s)` of the clause `c`. -/
def pSlk (s : Bool) (c x : A) : pInterp.Map A := pPt (.slk s) ![c, x]

/-- The item of the empty clause `c`. -/
def pEmp (a₀ c : A) : pInterp.Map A := pPt .emp ![c, a₀]

/-- The `f`-th position of the block `b`. -/
def pPos (f : Fin 3) (b : Bool × A) (y : A) : pInterp.Map A := pPt (.pos b.1 f) ![b.2, y]

/-- The lowest position of the block `b`. -/
def pLow (a₀ : A) (b : Bool × A) : pInterp.Map A := pPos 0 b a₀

theorem pLit_injective (a₀ : A) : Function.Injective fun p : A × Bool => pLit a₀ p.2 p.1 := by
  rintro ⟨x, s⟩ ⟨x', s'⟩ h
  obtain ⟨ht, hw⟩ := pPt_eq_iff.mp h
  refine Prod.ext ?_ ?_
  · simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  · cases s <;> cases s' <;> simp_all

theorem pSlk_injective (c : A) : Function.Injective fun p : A × Bool => pSlk p.2 c p.1 := by
  rintro ⟨x, s⟩ ⟨x', s'⟩ h
  obtain ⟨ht, hw⟩ := pPt_eq_iff.mp h
  refine Prod.ext ?_ ?_
  · simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  · cases s <;> cases s' <;> simp_all

theorem pPos_injective : Function.Injective fun u : (Bool × A) × Fin 3 × A =>
    pPos u.2.1 u.1 u.2.2 := by
  rintro ⟨⟨k, e⟩, f, y⟩ ⟨⟨k', e'⟩, f', y'⟩ h
  obtain ⟨ht, hw⟩ := pPt_eq_iff.mp h
  have h0 : e = e' := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  have h1 : y = y' := by simpa using congrArg (fun u : Fin 2 → A => u 1) hw
  have hk : k = k' ∧ f = f' := by
    refine ⟨?_, ?_⟩ <;> · injection ht
  obtain ⟨hk₁, hk₂⟩ := hk
  subst h0; subst h1; subst hk₁; subst hk₂
  rfl

theorem pLow_injective (a₀ : A) : Function.Injective (pLow a₀ (A := A)) := by
  rintro ⟨k, e⟩ ⟨k', e'⟩ h
  obtain ⟨ht, hw⟩ := pPt_eq_iff.mp h
  have h0 : e = e' := by simpa using congrArg (fun u : Fin 2 → A => u 0) hw
  have hk : k = k' := by injection ht
  exact Prod.ext hk h0

end Points

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

@[simp]
theorem bwItem_lit (s : Bool) (w : Fin 2 → A) :
    BWItem (pPt (.lit s) w) ↔ IsBot (w 1) := by
  rw [BWItem, pPt, FOInterpretation.relMap_map]
  simp [pInterp, itemF]

@[simp]
theorem bwItem_slk (s : Bool) (w : Fin 2 → A) :
    BWItem (pPt (.slk s) w) ↔ Mid (w 0) (w 1) s := by
  rw [BWItem, pPt, FOInterpretation.relMap_map]
  simp [pInterp, itemF]

@[simp]
theorem bwItem_emp (w : Fin 2 → A) :
    BWItem (pPt .emp w) ↔ EmptyCl (w 0) ∧ IsBot (w 1) := by
  rw [BWItem, pPt, FOInterpretation.relMap_map]
  simp [pInterp, itemF]

@[simp]
theorem bwItem_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) : ¬BWItem (pPt (.pos k f) w) := by
  rw [BWItem, pPt, FOInterpretation.relMap_map]
  simp [pInterp, itemF]

@[simp]
theorem bwPosn_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) : BWPosn (pPt (.pos k f) w) := by
  rw [BWPosn, pPt, FOInterpretation.relMap_map]
  simp [pInterp, posnF]

@[simp]
theorem bwPosn_lit (s : Bool) (w : Fin 2 → A) : ¬BWPosn (pPt (.lit s) w) := by
  rw [BWPosn, pPt, FOInterpretation.relMap_map]
  simp [pInterp, posnF]

@[simp]
theorem bwPosn_slk (s : Bool) (w : Fin 2 → A) : ¬BWPosn (pPt (.slk s) w) := by
  rw [BWPosn, pPt, FOInterpretation.relMap_map]
  simp [pInterp, posnF]

@[simp]
theorem bwPosn_emp (w : Fin 2 → A) : ¬BWPosn (pPt .emp w) := by
  rw [BWPosn, pPt, FOInterpretation.relMap_map]
  simp [pInterp, posnF]

@[simp]
theorem bwTgt_none (t : PTag) (w : Fin 2 → A) : ¬BWTgt (pPt t w) := by
  rw [BWTgt, pPt, FOInterpretation.relMap_map]
  simp [pInterp]

/-- The key of a point: tag rank, first coordinate, index in the block, second
coordinate. -/
def pKey (q : pInterp.Map A) : ℕ × A × ℕ × A :=
  (tagRk q.1, q.2 0, subRk q.1, q.2 1)

/-- The order of the interpreted structure, read lexicographically on the
keys. -/
def keyLe : ℕ × A × ℕ × A → ℕ × A × ℕ × A → Prop :=
  lexRel (· ≤ ·) (lexRel (· ≤ ·) (lexRel (· ≤ ·) (· ≤ ·)))

theorem bwLe_iff (t t' : PTag) (w w' : Fin 2 → A) :
    BWLe (pPt t w) (pPt t' w') ↔ keyLe (pKey (pPt t w)) (pKey (pPt t' w')) := by
  rw [BWLe, pPt, pPt, FOInterpretation.relMap_map]
  simp only [pInterp, leKF, keyLe, pKey, lexRel]
  split_ifs with h₁ h₂ h₃ h₄
  · simp only [Formula.realize_top, true_iff]
    exact Or.inl ⟨h₁.le, ne_of_lt h₁⟩
  · simp only [Formula.realize_bot, false_iff, not_or]
    exact ⟨fun h => absurd h.1 (Nat.not_le.mpr h₂), fun h => absurd h.1 (ne_of_gt h₂)⟩
  · have hrk : tagRk t = tagRk t' := Nat.le_antisymm (Nat.not_lt.mp h₂) (Nat.not_lt.mp h₁)
    simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_top, SatOcc.realize_ltF,
      realize_eqF]
    constructor
    · rintro (h | ⟨he, -⟩)
      · exact Or.inr ⟨hrk, Or.inl ⟨h.le, ne_of_lt h⟩⟩
      · exact Or.inr ⟨hrk, Or.inr ⟨he, Or.inl ⟨h₃.le, ne_of_lt h₃⟩⟩⟩
    · rintro (⟨-, hne⟩ | ⟨-, h | ⟨he, -⟩⟩)
      · exact absurd hrk hne
      · exact Or.inl (lt_of_le_of_ne h.1 h.2)
      · exact Or.inr ⟨he, trivial⟩
  · have hrk : tagRk t = tagRk t' := Nat.le_antisymm (Nat.not_lt.mp h₂) (Nat.not_lt.mp h₁)
    simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_bot, SatOcc.realize_ltF,
      realize_eqF, and_false, or_false]
    constructor
    · intro h
      exact Or.inr ⟨hrk, Or.inl ⟨h.le, ne_of_lt h⟩⟩
    · rintro (⟨-, hne⟩ | ⟨-, h | ⟨-, h | ⟨he, -⟩⟩⟩)
      · exact absurd hrk hne
      · exact lt_of_le_of_ne h.1 h.2
      · exact absurd h.1 (Nat.not_le.mpr h₄)
      · exact absurd he (ne_of_gt h₄)
  · have hrk : tagRk t = tagRk t' := Nat.le_antisymm (Nat.not_lt.mp h₂) (Nat.not_lt.mp h₁)
    have hsub : subRk t = subRk t' := Nat.le_antisymm (Nat.not_lt.mp h₄) (Nat.not_lt.mp h₃)
    simp only [Formula.realize_sup, Formula.realize_inf, SatOcc.realize_ltF, realize_eqF,
      SatOcc.realize_leF]
    constructor
    · rintro (h | ⟨he, hle⟩)
      · exact Or.inr ⟨hrk, Or.inl ⟨h.le, ne_of_lt h⟩⟩
      · exact Or.inr ⟨hrk, Or.inr ⟨he, Or.inr ⟨hsub, hle⟩⟩⟩
    · rintro (⟨-, hne⟩ | ⟨-, h | ⟨he, h | ⟨-, hle⟩⟩⟩)
      · exact absurd hrk hne
      · exact Or.inl (lt_of_le_of_ne h.1 h.2)
      · exact absurd hsub h.2
      · exact Or.inr ⟨he, hle⟩

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pKey_injective : Function.Injective (pKey (A := A)) := by
  intro q q' h
  obtain ⟨t, w, rfl⟩ := pPt_surj q
  obtain ⟨t', w', rfl⟩ := pPt_surj q'
  have h₁ : tagRk t = tagRk t' := congrArg (fun u : ℕ × A × ℕ × A => u.1) h
  have h₂ : subRk t = subRk t' := congrArg (fun u : ℕ × A × ℕ × A => u.2.2.1) h
  have h₃ : w 0 = w' 0 := congrArg (fun u : ℕ × A × ℕ × A => u.2.1) h
  have h₄ : w 1 = w' 1 := congrArg (fun u : ℕ × A × ℕ × A => u.2.2.2) h
  exact pPt_eq_iff.mpr ⟨tag_ext h₁ h₂, tuple₂_ext h₃ h₄⟩

/-- The interpreted order is a linear order: the lexicographic order of the
keys, which are pairwise distinct. -/
theorem isLinOrd_bwLe : IsLinOrd (BWLe (A := pInterp.Map A)) := by
  refine isLinOrd_of_key (isLinOrd_lexRel isLinOrd_le
    (isLinOrd_lexRel isLinOrd_le (isLinOrd_lexRel isLinOrd_le isLinOrd_le)))
    pKey pKey_injective fun q q' => ?_
  obtain ⟨t, w, rfl⟩ := pPt_surj q
  obtain ⟨t', w', rfl⟩ := pPt_surj q'
  exact bwLe_iff t t' w w'

end Characterizations

/-! ### The blocks -/

section Blocks

variable {A : Type} [LinearOrder A]

/-- The order of the blocks: the variable blocks first, then the clause
blocks, each group in the order of the input. -/
def blkLe : Bool × A → Bool × A → Prop := lexRel (· ≤ ·) (· ≤ ·)

theorem isLinOrd_blkLe : IsLinOrd (blkLe (A := A)) := isLinOrd_lexRel isLinOrd_le isLinOrd_le

/-- Being strictly below a block. -/
theorem blkLt_iff {k k' : Bool} {x e : A} :
    (blkLe (k, x) (k', e) ∧ (k, x) ≠ (k', e)) ↔
      (k = k' ∧ x < e) ∨ (k = false ∧ k' = true) := by
  cases k <;> cases k' <;> simp [blkLe, lexRel, lt_iff_le_and_ne]

/-- The rank of a block: how many blocks lie strictly below it. -/
noncomputable def blkRank (b : Bool × A) : ℕ := bitRank (blkLe (A := A)) (fun _ => True) b

end Blocks

/-! ### The bits, and the lowest position of a block -/

section Bits

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem bwBit_lit_pos (s : Bool) (w : Fin 2 → A) (k : Bool) (f : Fin 3) (w' : Fin 2 → A) :
    BWBit (pPt (.lit s) w) (pPt (.pos k f) w') ↔
      f = 0 ∧ IsBot (w 1) ∧ IsBot (w' 1) ∧ (if k then OccIn (w' 0) (w 0) s else w' 0 = w 0) := by
  rw [BWBit, pPt, pPt, FOInterpretation.relMap_map]
  by_cases hf : f = 0
  · subst hf
    cases k <;> simp [pInterp, bitF, and_assoc]
  · simp [pInterp, bitF, hf]

theorem bwBit_slk_pos (s : Bool) (w : Fin 2 → A) (k : Bool) (f : Fin 3) (w' : Fin 2 → A) :
    BWBit (pPt (.slk s) w) (pPt (.pos k f) w') ↔
      f = 0 ∧ k = true ∧ Mid (w 0) (w 1) s ∧ IsBot (w' 1) ∧ w' 0 = w 0 := by
  rw [BWBit, pPt, pPt, FOInterpretation.relMap_map]
  by_cases hf : f = 0 ∧ k = true
  · obtain ⟨rfl, rfl⟩ := hf
    simp [pInterp, bitF, and_assoc]
  · simp [pInterp, bitF, hf]
    tauto

theorem bwBit_emp_pos (w : Fin 2 → A) (k : Bool) (f : Fin 3) (w' : Fin 2 → A) :
    BWBit (pPt .emp w) (pPt (.pos k f) w') ↔
      f = 0 ∧ k = true ∧ EmptyCl (w 0) ∧ IsBot (w 1) ∧ IsBot (w' 1) ∧ w' 0 = w 0 := by
  rw [BWBit, pPt, pPt, FOInterpretation.relMap_map]
  by_cases hf : f = 0 ∧ k = true
  · obtain ⟨rfl, rfl⟩ := hf
    simp [pInterp, bitF, and_assoc]
  · simp [pInterp, bitF, hf]
    tauto

@[simp]
theorem bwBit_pos_left (k : Bool) (f : Fin 3) (w : Fin 2 → A) (q : pInterp.Map A) :
    ¬BWBit (pPt (.pos k f) w) q := by
  obtain ⟨t', w', rfl⟩ := pPt_surj q
  rw [BWBit, pPt, pPt, FOInterpretation.relMap_map]
  cases t' <;> simp [pInterp, bitF]

@[simp]
theorem bwBit_item_right (t : PTag) (w : Fin 2 → A) (s : Bool) (w' : Fin 2 → A) :
    ¬BWBit (pPt t w) (pPt (.lit s) w') ∧ ¬BWBit (pPt t w) (pPt (.slk s) w') ∧
      ¬BWBit (pPt t w) (pPt .emp w') := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [BWBit, pPt, pPt, FOInterpretation.relMap_map]
      cases t <;> simp [pInterp, bitF]

/-- Only the lowest position of a block ever carries a bit. -/
theorem eq_pLow_of_bit {a₀ : A} (ha₀ : IsBot a₀) {i q : pInterp.Map A} (h : BWBit i q)
    (hq : BWPosn q) : ∃ b, q = pLow a₀ b := by
  obtain ⟨t, w, rfl⟩ := pPt_surj i
  obtain ⟨t', w', rfl⟩ := pPt_surj q
  have hlow : ∀ (k : Bool) (f : Fin 3), f = 0 → IsBot (w' 1) →
      ∃ b : Bool × A, pPt (.pos k f) w' = pLow a₀ b := by
    rintro k f rfl hb
    refine ⟨(k, w' 0), ?_⟩
    rw [pLow, pPos]
    exact congrArg (pPt (PTag.pos k 0))
      (tuple₂_ext (by simp) (by simp [(ha₀ (w' 1)).antisymm (hb a₀)]))
  cases t' with
  | lit s => exact absurd hq (bwPosn_lit s w')
  | slk s => exact absurd hq (bwPosn_slk s w')
  | emp => exact absurd hq (bwPosn_emp w')
  | pos k f =>
    cases t with
    | lit s =>
      obtain ⟨hf, -, hb, -⟩ := (bwBit_lit_pos s w k f w').mp h
      exact hlow k f hf hb
    | slk s =>
      obtain ⟨hf, -, -, hb, -⟩ := (bwBit_slk_pos s w k f w').mp h
      exact hlow k f hf hb
    | emp =>
      obtain ⟨hf, -, -, -, hb, -⟩ := (bwBit_emp_pos w k f w').mp h
      exact hlow k f hf hb
    | pos k' f' => exact absurd h (bwBit_pos_left k' f' w _)

/-- The bit of a literal item in a block. -/
theorem bwBit_pLit_pLow {a₀ : A} (ha₀ : IsBot a₀) (s : Bool) (x : A) (b : Bool × A) :
    BWBit (pLit a₀ s x) (pLow a₀ b) ↔ (if b.1 then OccIn b.2 x s else b.2 = x) := by
  rw [pLit, pLow, pPos, bwBit_lit_pos]
  simp [ha₀]

/-- The bit of a slack item in a block. -/
theorem bwBit_pSlk_pLow {a₀ : A} (ha₀ : IsBot a₀) (s : Bool) (c x : A) (b : Bool × A) :
    BWBit (pSlk s c x) (pLow a₀ b) ↔ b.1 = true ∧ b.2 = c ∧ Mid c x s := by
  rw [pSlk, pLow, pPos, bwBit_slk_pos]
  simp [ha₀]
  tauto

/-- The bit of the item of an empty clause in a block. -/
theorem bwBit_pEmp_pLow {a₀ : A} (ha₀ : IsBot a₀) (c : A) (b : Bool × A) :
    BWBit (pEmp a₀ c) (pLow a₀ b) ↔ b.1 = true ∧ b.2 = c ∧ EmptyCl c := by
  rw [pEmp, pLow, pPos, bwBit_emp_pos]
  simp [ha₀]
  tauto

end Bits

/-! ### The place values -/

section Places

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

omit [Language.sat.Structure A] [LinearOrder A] in
private theorem key_pos (k : Bool) (f : Fin 3) (w : Fin 2 → A) :
    pKey (pPt (.pos k f) w) = (if k then 6 else 5, w 0, (f : ℕ), w 1) := by
  cases k <;> rfl

theorem bwLe_pos_pos (k k' : Bool) (f f' : Fin 3) (w w' : Fin 2 → A) :
    BWLe (pPt (.pos k f) w) (pPt (.pos k' f') w') ↔
      (k = false ∧ k' = true) ∨
        (k = k' ∧ (w 0 < w' 0 ∨
          (w 0 = w' 0 ∧ ((f : ℕ) < (f' : ℕ) ∨ ((f : ℕ) = (f' : ℕ) ∧ w 1 ≤ w' 1))))) := by
  rw [bwLe_iff, key_pos, key_pos]
  cases k <;> cases k' <;>
    simp [keyLe, lexRel, lt_iff_le_and_ne]

/-- **The block structure**: the rank of the lowest position of a block is
`3 |A|` times the rank of the block, so its place value is
`(2 ^ (3 |A|)) ^ rank` – one digit of base `2 ^ (3 |A|)` per block. -/
theorem bitRank_pLow {a₀ : A} (ha₀ : IsBot a₀) (b : Bool × A) :
    bitRank (BWLe (A := pInterp.Map A)) BWPosn (pLow a₀ b) = 3 * Nat.card A * blkRank b := by
  obtain ⟨k, e⟩ := b
  have hset : {q : pInterp.Map A | BWPosn q ∧ BWLe q (pLow a₀ (k, e)) ∧ q ≠ pLow a₀ (k, e)} =
      (fun u : (Bool × A) × Fin 3 × A => pPos u.2.1 u.1 u.2.2) ''
        ({b' : Bool × A | blkLe b' (k, e) ∧ b' ≠ (k, e)} ×ˢ Set.univ) := by
    ext q
    obtain ⟨t, w, rfl⟩ := pPt_surj q
    constructor
    · rintro ⟨hp, hle, hne⟩
      cases t with
      | lit s => exact absurd hp (bwPosn_lit s w)
      | slk s => exact absurd hp (bwPosn_slk s w)
      | emp => exact absurd hp (bwPosn_emp w)
      | pos k' f' =>
        rw [pLow, pPos, bwLe_pos_pos] at hle
        have hlt : blkLe (k', w 0) (k, e) ∧ (k', w 0) ≠ (k, e) := by
          refine blkLt_iff.mpr ?_
          rcases hle with ⟨h₁, h₂⟩ | ⟨rfl, h⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · refine Or.inl ⟨rfl, ?_⟩
            rcases h with h | ⟨he, h⟩
            · simpa using h
            · exfalso
              refine hne ?_
              have hf : f' = 0 := by
                rcases h with h | ⟨h, -⟩
                · simp at h
                · exact Fin.ext (by simpa using h)
              have hy : w 1 = a₀ := by
                rcases h with h | ⟨-, h⟩
                · simp at h
                · exact ((ha₀ (w 1)).antisymm (by simpa using h)).symm
              rw [pLow, pPos, hf]
              exact congrArg (pPt (PTag.pos k' 0))
                (tuple₂_ext (by simpa using he) (by simpa using hy))
        exact ⟨((k', w 0), f', w 1), ⟨hlt, Set.mem_univ _⟩,
          (congrArg (pPt (PTag.pos k' f')) (tuple₂_ext (by simp) (by simp))).symm⟩
    · rintro ⟨⟨⟨k', x⟩, f', y⟩, ⟨hlt, -⟩, hq⟩
      obtain ⟨ht, hw⟩ := pPt_eq_iff.mp hq.symm
      subst ht
      subst hw
      rcases blkLt_iff.mp hlt with hb | hb
      · refine ⟨bwPosn_pos _ _ _, ?_, ?_⟩
        · rw [pLow, pPos, bwLe_pos_pos]
          exact Or.inr ⟨hb.1, Or.inl (by simpa using hb.2)⟩
        · intro hcon
          rw [pLow, pPos] at hcon
          obtain ⟨-, hw⟩ := pPt_eq_iff.mp hcon
          exact absurd (by simpa using congrArg (fun u : Fin 2 → A => u 0) hw) (ne_of_lt hb.2)
      · refine ⟨bwPosn_pos _ _ _, ?_, ?_⟩
        · rw [pLow, pPos, bwLe_pos_pos]
          exact Or.inl ⟨hb.1, hb.2⟩
        · intro hcon
          rw [pLow, pPos] at hcon
          obtain ⟨ht, -⟩ := pPt_eq_iff.mp hcon
          have : k' = k := by injection ht
          rw [hb.1, hb.2] at this
          exact absurd this (by decide)
  rw [bitRank, hset, pPos_injective.injOn.ncard_image, Set.ncard_prod, Set.ncard_univ, blkRank,
    bitRank]
  have hcard : Nat.card (Fin 3 × A) = 3 * Nat.card A := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hset' : {q : Bool × A | (fun _ => True) q ∧ blkLe q (k, e) ∧ q ≠ (k, e)} =
      {b' : Bool × A | blkLe b' (k, e) ∧ b' ≠ (k, e)} := by
    ext q
    simp
  rw [hset', hcard, Nat.mul_comm]

end Places

/-! ### Weights, as base-`2 ^ (3 |A|)` numbers -/

section Numbers

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The base: one digit per block, `3 |A|` bits wide, which is above every
digit the gadget writes, so digits never carry into the next block. -/
noncomputable def pbase (A : Type) [Finite A] : ℕ := 2 ^ (3 * Nat.card A)

omit [Language.sat.Structure A] [LinearOrder A] in
theorem pbase_pos : 0 < pbase A := by
  rw [pbase]
  positivity

open Classical in
/-- A binary number whose bits sit on the lowest positions of the blocks
selected by `sub` is the base-`2 ^ (3 |A|)` number with digit `1` there. -/
theorem binNum_eq_digit {a₀ : A} (ha₀ : IsBot a₀) {p : pInterp.Map A → Prop}
    {sub : Bool × A → Prop}
    (hp : ∀ q : pInterp.Map A, (BWPosn q ∧ p q) ↔ ∃ b, sub b ∧ q = pLow a₀ b) :
    binNum (BWLe (A := pInterp.Map A)) BWPosn p =
      digitNum (blkLe (A := A)) (fun _ => True) (pbase A) (fun b => if sub b then 1 else 0) := by
  classical
  have hset : {q : pInterp.Map A | BWPosn q ∧ p q} = pLow a₀ '' {b | sub b} := by
    ext q
    rw [Set.mem_setOf_eq, hp q]
    exact ⟨fun ⟨b, hb, hq⟩ => ⟨b, hb, hq.symm⟩, fun ⟨b, hb, hq⟩ => ⟨b, hb, hq.symm⟩⟩
  rw [binNum, hset, finsum_mem_image (pLow_injective a₀).injOn]
  refine (finsum_mem_congr rfl fun b _ => ?_).trans (finsum_pow_eq_digitNum fun _ _ => trivial)
  rw [bitRank_pLow ha₀, pbase, pow_mul, blkRank]

open Classical in
/-- **Every weight is read digit by digit**: the digit of a block is `1` when
the item carries a bit at its lowest position, and `0` otherwise. -/
theorem bwWeight_eq {a₀ : A} (ha₀ : IsBot a₀) (i : pInterp.Map A) :
    BWWeight i = digitNum (blkLe (A := A)) (fun _ => True) (pbase A)
      (fun b => if BWBit i (pLow a₀ b) then 1 else 0) := by
  classical
  refine binNum_eq_digit ha₀ fun q => ?_
  constructor
  · rintro ⟨hq, hbit⟩
    obtain ⟨b, rfl⟩ := eq_pLow_of_bit ha₀ hbit hq
    exact ⟨b, hbit, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨by rw [pLow, pPos]; exact bwPosn_pos _ _ _, hb⟩

open Classical in
/-- **The weight of a set of items**, read digit by digit: the digit of a
block is the number of selected items carrying a bit there. -/
theorem sum_weights_eq {a₀ : A} (ha₀ : IsBot a₀) (S : pInterp.Map A → Prop) :
    (∑ᶠ i ∈ {i | S i}, BWWeight i) =
      digitNum (blkLe (A := A)) (fun _ => True) (pbase A)
        (fun b => ({i : pInterp.Map A | S i ∧ BWBit i (pLow a₀ b)} : Set _).ncard) := by
  classical
  haveI : Finite (pInterp.Map A) := pInterp.map_finite A
  have h₁ : (∑ᶠ i ∈ {i | S i}, BWWeight i) =
      ∑ᶠ i ∈ {i | S i}, digitNum (blkLe (A := A)) (fun _ => True) (pbase A)
        (fun b => if BWBit i (pLow a₀ b) then 1 else 0) :=
    finsum_mem_congr rfl fun i _ => bwWeight_eq ha₀ i
  rw [h₁, digitNum_finsum]
  refine digitNum_congr_on fun b _ => ?_
  refine (finsum_mem_ite_one (ι := pInterp.Map A) _ _).trans ?_
  exact congrArg Set.ncard (by ext i; simp)

end Numbers

/-! ### Counting the items of a block -/

section Counting

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The number of selected items carrying a bit in a block: the digit that
block contributes to the weight of the selection. -/
noncomputable def cnt (a₀ : A) (S : pInterp.Map A → Prop) (b : Bool × A) : ℕ :=
  ({i : pInterp.Map A | S i ∧ BWBit i (pLow a₀ b)} : Set _).ncard

theorem sum_weights_eq_cnt {a₀ : A} (ha₀ : IsBot a₀) (S : pInterp.Map A → Prop) :
    (∑ᶠ i ∈ {i | S i}, BWWeight i) =
      digitNum (blkLe (A := A)) (fun _ => True) (pbase A) (cnt a₀ S) :=
  sum_weights_eq ha₀ S

/-- A selection and the items it leaves out split every digit. -/
theorem cnt_add_cnt (a₀ : A) {S : pInterp.Map A → Prop} (hS : ∀ i, S i → BWItem i)
    (b : Bool × A) :
    cnt a₀ S b + cnt a₀ (fun i => BWItem i ∧ ¬S i) b = cnt a₀ BWItem b := by
  haveI : Finite (pInterp.Map A) := pInterp.map_finite A
  rw [cnt, cnt, cnt, ← Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _)]
  · congr 1
    ext i
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hi, hb⟩ | ⟨⟨hi, -⟩, hb⟩)
      · exact ⟨hS i hi, hb⟩
      · exact ⟨hi, hb⟩
    · rintro ⟨hi, hb⟩
      by_cases h : S i
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨⟨hi, h⟩, hb⟩
  · rw [Set.disjoint_left]
    rintro i ⟨hi, -⟩ ⟨⟨-, hn⟩, -⟩
    exact hn hi

/-! #### Which items carry a bit in a block -/

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pLow_eq (a₀ : A) (k : Bool) (e : A) : pLow a₀ (k, e) = pPt (.pos k 0) ![e, a₀] := rfl

omit [Finite A] in
/-- The items carrying a bit in a variable block are the two literals of that
variable. -/
theorem bit_pLow_var {a₀ : A} (ha₀ : IsBot a₀) (x : A) (i : pInterp.Map A) :
    BWBit i (pLow a₀ (false, x)) ↔ ∃ s, i = pLit a₀ s x := by
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  obtain ⟨t, w, rfl⟩ := pPt_surj i
  rw [pLow_eq]
  cases t with
  | lit s =>
    rw [bwBit_lit_pos]
    constructor
    · rintro ⟨-, hb, -, he⟩
      have hx : x = w 0 := by simpa using he
      refine ⟨s, ?_⟩
      rw [pLit, hx]
      exact congrArg (pPt (PTag.lit s)) (tuple₂_ext (by simp) (by simp [hbot (w 1) hb]))
    · rintro ⟨s', hs⟩
      rw [pLit] at hs
      obtain ⟨ht, hw⟩ := pPt_eq_iff.mp hs
      cases ht
      subst hw
      exact ⟨rfl, by simpa using ha₀, by simpa using ha₀, by simp⟩
  | slk s =>
    rw [bwBit_slk_pos]
    constructor
    · rintro ⟨-, hk, -⟩
      exact absurd hk (by simp)
    · rintro ⟨s', hs⟩
      exact absurd (pPt_eq_iff.mp hs).1 (by simp)
  | emp =>
    rw [bwBit_emp_pos]
    constructor
    · rintro ⟨-, hk, -⟩
      exact absurd hk (by simp)
    · rintro ⟨s', hs⟩
      exact absurd (pPt_eq_iff.mp hs).1 (by simp)
  | pos k f =>
    constructor
    · intro h
      exact absurd h (bwBit_pos_left k f w _)
    · rintro ⟨s', hs⟩
      exact absurd (pPt_eq_iff.mp hs).1 (by simp)

omit [Finite A] in
/-- The items carrying a bit in a clause block are the literals occurring in
the clause, its slack items, and its own item if it is empty. -/
theorem bit_pLow_cls {a₀ : A} (ha₀ : IsBot a₀) (c : A) (i : pInterp.Map A) :
    BWBit i (pLow a₀ (true, c)) ↔
      (∃ p : A × Bool, OccIn c p.1 p.2 ∧ i = pLit a₀ p.2 p.1) ∨
        (∃ p : A × Bool, Mid c p.1 p.2 ∧ i = pSlk p.2 c p.1) ∨
        (EmptyCl c ∧ i = pEmp a₀ c) := by
  have hbot : ∀ y : A, IsBot y → y = a₀ := fun y hy => le_antisymm (hy a₀) (ha₀ y)
  obtain ⟨t, w, rfl⟩ := pPt_surj i
  rw [pLow_eq]
  cases t with
  | lit s =>
    rw [bwBit_lit_pos]
    constructor
    · rintro ⟨-, hb, -, hocc⟩
      refine Or.inl ⟨(w 0, s), by simpa using hocc, ?_⟩
      rw [pLit]
      exact congrArg (pPt (PTag.lit s)) (tuple₂_ext (by simp) (by simp [hbot (w 1) hb]))
    · rintro (⟨⟨y, r⟩, hocc, hs⟩ | ⟨⟨y, r⟩, -, hs⟩ | ⟨-, hs⟩)
      · rw [pLit] at hs
        obtain ⟨ht, hw⟩ := pPt_eq_iff.mp hs
        cases ht
        subst hw
        exact ⟨rfl, by simpa using ha₀, by simpa using ha₀, by simpa using hocc⟩
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
  | slk s =>
    rw [bwBit_slk_pos]
    constructor
    · rintro ⟨-, -, hmid, -, hc⟩
      have hc' : c = w 0 := by simpa using hc
      refine Or.inr (Or.inl ⟨(w 1, s), ?_, ?_⟩)
      · rw [hc']
        exact hmid
      · rw [pSlk]
        exact congrArg (pPt (PTag.slk s)) (tuple₂_ext (by simp [hc']) (by simp))
    · rintro (⟨⟨y, r⟩, -, hs⟩ | ⟨⟨y, r⟩, hmid, hs⟩ | ⟨-, hs⟩)
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
      · rw [pSlk] at hs
        obtain ⟨ht, hw⟩ := pPt_eq_iff.mp hs
        cases ht
        subst hw
        exact ⟨rfl, rfl, by simpa using hmid, by simpa using ha₀, by simp⟩
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
  | emp =>
    rw [bwBit_emp_pos]
    constructor
    · rintro ⟨-, -, hemp, hb, -, hc⟩
      have hc' : c = w 0 := by simpa using hc
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hc']
        exact hemp
      · rw [pEmp]
        exact congrArg (pPt PTag.emp)
          (tuple₂_ext (by simp [hc']) (by simp [hbot (w 1) hb]))
    · rintro (⟨⟨y, r⟩, -, hs⟩ | ⟨⟨y, r⟩, -, hs⟩ | ⟨hemp, hs⟩)
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
      · exact absurd (pPt_eq_iff.mp hs).1 (by simp)
      · rw [pEmp] at hs
        obtain ⟨-, hw⟩ := pPt_eq_iff.mp hs
        subst hw
        exact ⟨rfl, rfl, by simpa using hemp, by simpa using ha₀, by simpa using ha₀, by simp⟩
  | pos k f =>
    constructor
    · intro h
      exact absurd h (bwBit_pos_left k f w _)
    · rintro (⟨⟨y, r⟩, -, hs⟩ | ⟨⟨y, r⟩, -, hs⟩ | ⟨-, hs⟩) <;>
        exact absurd (pPt_eq_iff.mp hs).1 (by simp)

/-! #### The digits, block by block -/

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pLit_ne_pSlk (a₀ : A) (s s' : Bool) (x c y : A) : pLit a₀ s x ≠ pSlk s' c y := by
  intro h
  rw [pLit, pSlk] at h
  exact absurd (pPt_eq_iff.mp h).1 (by simp)

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pLit_ne_pEmp (a₀ : A) (s : Bool) (x c : A) : pLit a₀ s x ≠ pEmp a₀ c := by
  intro h
  rw [pLit, pEmp] at h
  exact absurd (pPt_eq_iff.mp h).1 (by simp)

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pSlk_ne_pEmp (a₀ : A) (s : Bool) (c x c' : A) : pSlk s c x ≠ pEmp a₀ c' := by
  intro h
  rw [pSlk, pEmp] at h
  exact absurd (pPt_eq_iff.mp h).1 (by simp)

omit [Finite A] in
/-- The digit of a variable block counts the selected literals of that
variable. -/
theorem cnt_var {a₀ : A} (ha₀ : IsBot a₀) (S : pInterp.Map A → Prop) (x : A) :
    cnt a₀ S (false, x) = ({s : Bool | S (pLit a₀ s x)} : Set Bool).ncard := by
  have hinj : Set.InjOn (fun s : Bool => pLit a₀ s x) {s | S (pLit a₀ s x)} := by
    intro s _ s' _ h
    have ht := congrArg (fun q : pInterp.Map A => q.1) h
    simpa [pLit, pPt] using ht
  have hset : {i : pInterp.Map A | S i ∧ BWBit i (pLow a₀ (false, x))} =
      (fun s : Bool => pLit a₀ s x) '' {s | S (pLit a₀ s x)} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hi, hb⟩
      obtain ⟨s, rfl⟩ := (bit_pLow_var ha₀ x i).mp hb
      exact ⟨s, hi, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, (bit_pLow_var ha₀ x _).mpr ⟨s, rfl⟩⟩
  rw [cnt, hset, hinj.ncard_image]

open Classical in
/-- The digit of a clause block counts the selected literals occurring in the
clause, its selected slack items, and its own item if it is empty. -/
theorem cnt_cls {a₀ : A} (ha₀ : IsBot a₀) (S : pInterp.Map A → Prop) (c : A) :
    cnt a₀ S (true, c) =
      ({p ∈ OccSet c | S (pLit a₀ p.2 p.1)} : Set (A × Bool)).ncard +
        ({p ∈ MidSet c | S (pSlk p.2 c p.1)} : Set (A × Bool)).ncard +
        (if EmptyCl c ∧ S (pEmp a₀ c) then 1 else 0) := by
  classical
  haveI : Finite (pInterp.Map A) := pInterp.map_finite A
  have hset : {i : pInterp.Map A | S i ∧ BWBit i (pLow a₀ (true, c))} =
      (((fun p : A × Bool => pLit a₀ p.2 p.1) '' {p ∈ OccSet c | S (pLit a₀ p.2 p.1)}) ∪
        ((fun p : A × Bool => pSlk p.2 c p.1) '' {p ∈ MidSet c | S (pSlk p.2 c p.1)})) ∪
        {i : pInterp.Map A | (EmptyCl c ∧ S (pEmp a₀ c)) ∧ i = pEmp a₀ c} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hi, hb⟩
      rcases (bit_pLow_cls ha₀ c i).mp hb with ⟨p, hocc, rfl⟩ | ⟨p, hmid, rfl⟩ | ⟨hemp, rfl⟩
      · exact Or.inl (Or.inl ⟨p, ⟨hocc, hi⟩, rfl⟩)
      · exact Or.inl (Or.inr ⟨p, ⟨hmid, hi⟩, rfl⟩)
      · exact Or.inr ⟨⟨hemp, hi⟩, rfl⟩
    · rintro ((⟨p, ⟨hocc, hs⟩, rfl⟩ | ⟨p, ⟨hmid, hs⟩, rfl⟩) | ⟨⟨hemp, hs⟩, rfl⟩)
      · exact ⟨hs, (bit_pLow_cls ha₀ c _).mpr (Or.inl ⟨p, hocc, rfl⟩)⟩
      · exact ⟨hs, (bit_pLow_cls ha₀ c _).mpr (Or.inr (Or.inl ⟨p, hmid, rfl⟩))⟩
      · exact ⟨hs, (bit_pLow_cls ha₀ c _).mpr (Or.inr (Or.inr ⟨hemp, rfl⟩))⟩
  have hd₁ : Disjoint
      ((fun p : A × Bool => pLit a₀ p.2 p.1) '' {p ∈ OccSet c | S (pLit a₀ p.2 p.1)})
      ((fun p : A × Bool => pSlk p.2 c p.1) '' {p ∈ MidSet c | S (pSlk p.2 c p.1)}) := by
    rw [Set.disjoint_left]
    rintro i ⟨p, -, rfl⟩ ⟨q, -, hq⟩
    exact absurd hq.symm (pLit_ne_pSlk a₀ p.2 q.2 p.1 c q.1)
  have hd₂ : Disjoint
      (((fun p : A × Bool => pLit a₀ p.2 p.1) '' {p ∈ OccSet c | S (pLit a₀ p.2 p.1)}) ∪
        ((fun p : A × Bool => pSlk p.2 c p.1) '' {p ∈ MidSet c | S (pSlk p.2 c p.1)}))
      {i : pInterp.Map A | (EmptyCl c ∧ S (pEmp a₀ c)) ∧ i = pEmp a₀ c} := by
    rw [Set.disjoint_left]
    rintro i (⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) ⟨-, hq⟩
    · exact absurd hq (pLit_ne_pEmp a₀ p.2 p.1 c)
    · exact absurd hq (pSlk_ne_pEmp a₀ p.2 c p.1 c)
  have hlast : ({i : pInterp.Map A | (EmptyCl c ∧ S (pEmp a₀ c)) ∧ i = pEmp a₀ c} : Set _).ncard =
      if EmptyCl c ∧ S (pEmp a₀ c) then 1 else 0 := by
    by_cases hp : EmptyCl c ∧ S (pEmp a₀ c)
    · have : {i : pInterp.Map A | (EmptyCl c ∧ S (pEmp a₀ c)) ∧ i = pEmp a₀ c} = {pEmp a₀ c} := by
        ext i
        simp [hp]
      rw [this, Set.ncard_singleton, if_pos hp]
    · have : {i : pInterp.Map A | (EmptyCl c ∧ S (pEmp a₀ c)) ∧ i = pEmp a₀ c} = ∅ := by
        ext i
        simp [hp]
      rw [this, Set.ncard_empty, if_neg hp]
  rw [cnt, hset, Set.ncard_union_eq hd₂ (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd₁ (Set.toFinite _) (Set.toFinite _),
    (pLit_injective a₀).injOn.ncard_image, (pSlk_injective c).injOn.ncard_image, hlast]

omit [Finite A] in
/-- Every variable block totals two: a balanced split takes exactly one of the
two literals of the variable. -/
theorem cnt_item_var {a₀ : A} (ha₀ : IsBot a₀) (x : A) : cnt a₀ BWItem (false, x) = 2 := by
  rw [cnt_var ha₀]
  have hset : {s : Bool | BWItem (pLit a₀ s x)} = Set.univ := by
    ext s
    simp [pLit, ha₀]
  rw [hset, Set.ncard_univ]
  simp

open Classical in
/-- A clause block totals its occurrences plus its slack occurrences, plus one
if the clause is empty. -/
theorem cnt_item_cls {a₀ : A} (ha₀ : IsBot a₀) (c : A) :
    cnt a₀ BWItem (true, c) =
      (OccSet c).ncard + (MidSet c).ncard + (if EmptyCl c then 1 else 0) := by
  classical
  have h₁ : {p ∈ OccSet c | BWItem (pLit a₀ p.2 p.1)} = OccSet c := by
    ext p
    simp [pLit, ha₀]
  have h₂ : {p ∈ MidSet c | BWItem (pSlk p.2 c p.1)} = MidSet c := by
    ext p
    simp [pSlk, MidSet]
  rw [cnt_cls ha₀, h₁, h₂]
  by_cases hemp : EmptyCl c <;> simp [hemp, pEmp, ha₀]

end Counting

/-! ### The digits stay below the base -/

section Bound

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

omit [Language.sat.Structure A] [LinearOrder A] in
theorem ncard_le_two_card (X : Set (A × Bool)) : X.ncard ≤ 2 * Nat.card A := by
  have h1 : X.ncard ≤ (Set.univ : Set (A × Bool)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ X) (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have hb : Nat.card (A × Bool) = Nat.card A * 2 := by
    rw [Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

/-- A selection weighs at most as much as all the items, digit by digit. -/
theorem cnt_le (a₀ : A) {S : pInterp.Map A → Prop} (hS : ∀ i, S i → BWItem i) (b : Bool × A) :
    cnt a₀ S b ≤ cnt a₀ BWItem b := by
  haveI : Finite (pInterp.Map A) := pInterp.map_finite A
  exact Set.ncard_le_ncard (fun i hi => ⟨hS i hi.1, hi.2⟩) (Set.toFinite _)

variable [Nonempty A]

/-- **No carry**: every digit the gadget writes stays below the base, `3 |A|`
bits being more than the `4 |A| + 1` items a block can hold. -/
theorem cnt_item_lt_pbase {a₀ : A} (ha₀ : IsBot a₀) (b : Bool × A) :
    cnt a₀ BWItem b < pbase A := by
  classical
  have hn : 1 ≤ Nat.card A := Nat.card_pos
  have hkey : 4 * Nat.card A + 1 < pbase A := by
    have h1 : Nat.card A + 1 ≤ 2 ^ Nat.card A := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ (Nat.card A + 2) ≤ 2 ^ (3 * Nat.card A) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ (Nat.card A + 2) = 2 ^ Nat.card A * 4 := by
      rw [pow_add]
      norm_num
    rw [pbase]
    omega
  obtain ⟨k, e⟩ := b
  cases k with
  | false =>
    rw [cnt_item_var ha₀]
    omega
  | true =>
    rw [cnt_item_cls ha₀]
    have h1 := ncard_le_two_card (OccSet e)
    have h2 := ncard_le_two_card (MidSet e)
    by_cases hemp : EmptyCl e <;> simp only [hemp, if_true, if_false] <;> omega

/-- **The balance condition, digit by digit**: a selection weighs as much as
the items it leaves out exactly when it takes half of every digit. -/
theorem sum_eq_iff {a₀ : A} (ha₀ : IsBot a₀) {S : pInterp.Map A → Prop}
    (hS : ∀ i, S i → BWItem i) :
    ((∑ᶠ i ∈ {i | S i}, BWWeight i) = ∑ᶠ i ∈ {i | BWItem i ∧ ¬S i}, BWWeight i) ↔
      ∀ b : Bool × A, 2 * cnt a₀ S b = cnt a₀ BWItem b := by
  have hS' : ∀ i, (BWItem i ∧ ¬S i) → BWItem i := fun _ h => h.1
  rw [sum_weights_eq_cnt ha₀, sum_weights_eq_cnt ha₀]
  constructor
  · intro heq b
    have hd := digitNum_inj (Le := blkLe (A := A)) isLinOrd_blkLe pbase_pos
      ({b : Bool × A | True} : Set _).ncard (fun _ => True) rfl _ _
      (fun b' => lt_of_le_of_lt (cnt_le a₀ hS b') (cnt_item_lt_pbase ha₀ b'))
      (fun b' => lt_of_le_of_lt (cnt_le a₀ hS' b') (cnt_item_lt_pbase ha₀ b')) heq b trivial
    have hadd := cnt_add_cnt a₀ hS b
    omega
  · intro h
    refine digitNum_congr_on fun b _ => ?_
    have hadd := cnt_add_cnt a₀ hS b
    have hb := h b
    omega

end Bound

/-! ### The selection made by an assignment -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- The items a not-all-equal assignment selects: the true literals, and the
slack items chosen by `M`. -/
def splitSet (a₀ : A) (ν : A → Prop) (M : A → Set (A × Bool)) : pInterp.Map A → Prop := fun i =>
  (∃ p : A × Bool, LitTrue ν p.1 p.2 ∧ i = pLit a₀ p.2 p.1) ∨
    (∃ (c : A) (p : A × Bool), p ∈ M c ∧ i = pSlk p.2 c p.1)

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pLit_eq_iff {a₀ : A} {s s' : Bool} {x x' : A} :
    pLit a₀ s x = pLit a₀ s' x' ↔ s = s' ∧ x = x' := by
  rw [pLit, pLit, pPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    exact ⟨by simpa using ht, by simpa using congrArg (fun u : Fin 2 → A => u 0) hw⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem pSlk_eq_iff {s s' : Bool} {c c' x x' : A} :
    pSlk s c x = pSlk s' c' x' ↔ s = s' ∧ c = c' ∧ x = x' := by
  rw [pSlk, pSlk, pPt_eq_iff]
  constructor
  · rintro ⟨ht, hw⟩
    exact ⟨by simpa using ht, by simpa using congrArg (fun u : Fin 2 → A => u 0) hw,
      by simpa using congrArg (fun u : Fin 2 → A => u 1) hw⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl⟩

variable {a₀ : A} {ν : A → Prop} {M : A → Set (A × Bool)}

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem splitSet_pLit (s : Bool) (x : A) : splitSet a₀ ν M (pLit a₀ s x) ↔ LitTrue ν x s := by
  constructor
  · rintro (⟨p, hT, hp⟩ | ⟨c, p, -, hp⟩)
    · obtain ⟨h₁, h₂⟩ := pLit_eq_iff.mp hp
      rw [h₁, h₂]
      exact hT
    · exact absurd hp (pLit_ne_pSlk a₀ s p.2 x c p.1)
  · intro h
    exact Or.inl ⟨(x, s), h, rfl⟩

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem splitSet_pSlk (s : Bool) (c x : A) :
    splitSet a₀ ν M (pSlk s c x) ↔ (x, s) ∈ M c := by
  constructor
  · rintro (⟨p, -, hp⟩ | ⟨c', p, hp, hq⟩)
    · exact absurd hp.symm (pLit_ne_pSlk a₀ p.2 s p.1 c x)
    · obtain ⟨h₁, h₂, h₃⟩ := pSlk_eq_iff.mp hq
      subst h₂
      have hp' : ((x, s) : A × Bool) = p := Prod.ext h₃ h₁
      rw [hp']
      exact hp
  · intro h
    exact Or.inr ⟨c, (x, s), h, rfl⟩

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem splitSet_pEmp (c : A) : ¬splitSet a₀ ν M (pEmp a₀ c) := by
  rintro (⟨p, -, hp⟩ | ⟨c', p, -, hp⟩)
  · exact absurd hp.symm (pLit_ne_pEmp a₀ p.2 p.1 c)
  · exact absurd hp.symm (pSlk_ne_pEmp a₀ p.2 c' p.1 c)

/-- The true occurrences of a clause under an assignment. -/
def TrueSet (ν : A → Prop) (c : A) : Set (A × Bool) := {p ∈ OccSet c | LitTrue ν p.1 p.2}

end Correctness

/-! ### Correctness of the reduction -/

section Correct

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

private theorem ncard_bool_eq_one {P : Bool → Prop} (h : ({s | P s} : Set Bool).ncard = 1) :
    P false ↔ ¬P true := by
  classical
  by_cases h2 : P true <;> by_cases h3 : P false
  · exfalso
    have hset : {s : Bool | P s} = Set.univ := by
      ext s
      cases s <;> simp [h2, h3]
    rw [hset, Set.ncard_univ] at h
    simp [Nat.card_eq_fintype_card] at h
  · simp [h2, h3]
  · simp [h2, h3]
  · exfalso
    have hset : {s : Bool | P s} = ∅ := by
      ext s
      cases s <;> simp [h2, h3]
    rw [hset, Set.ncard_empty] at h
    exact absurd h (by norm_num)

omit [Finite A] [Nonempty A] in
/-- **A balanced split is an assignment**: the two literals of a variable
split its block, so exactly one of them is selected. -/
theorem litTrue_iff_sel {a₀ : A} (ha₀ : IsBot a₀) {S : pInterp.Map A → Prop}
    (hbal : ∀ b, 2 * cnt a₀ S b = cnt a₀ BWItem b) (x : A) (s : Bool) :
    S (pLit a₀ s x) ↔ LitTrue (fun y => S (pLit a₀ true y)) x s := by
  have h := hbal (false, x)
  rw [cnt_var ha₀, cnt_item_var ha₀] at h
  have h1 : ({s : Bool | S (pLit a₀ s x)} : Set Bool).ncard = 1 := by omega
  cases s with
  | true => exact Iff.rfl
  | false =>
    change S (pLit a₀ false x) ↔ ¬S (pLit a₀ true x)
    exact ncard_bool_eq_one h1

omit [Nonempty A] in
/-- **A balanced split satisfies every clause, not all equal**: if no
occurrence of a clause were selected, the slack of that clause – strictly
fewer items than it has occurrences – would have to make up for all of them,
and an empty clause could not be split at all. -/
theorem exists_occ_selected {a₀ : A} (ha₀ : IsBot a₀) {S T : pInterp.Map A → Prop}
    (hcompl : ∀ i, BWItem i → (S i ↔ ¬T i))
    (hbal : ∀ b, cnt a₀ S b = cnt a₀ T b) {c : A} (hc : IsCl c) :
    ∃ p : A × Bool, p ∈ OccSet c ∧ S (pLit a₀ p.2 p.1) := by
  classical
  by_contra hcon
  push Not at hcon
  have hlitem : ∀ p : A × Bool, BWItem (pLit a₀ p.2 p.1) := by
    intro p
    rw [pLit]
    exact (bwItem_lit _ _).mpr (by simpa using ha₀)
  have hlitS : {p ∈ OccSet c | S (pLit a₀ p.2 p.1)} = ∅ := by
    ext p
    simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hp => hcon p hp
  have hlitT : {p ∈ OccSet c | T (pLit a₀ p.2 p.1)} = OccSet c := by
    ext p
    simp only [Set.mem_sep_iff, and_iff_left_iff_imp]
    intro hp
    by_contra hnT
    exact hcon p hp ((hcompl _ (hlitem p)).mpr hnT)
  have hbc := hbal (true, c)
  rw [cnt_cls ha₀, cnt_cls ha₀, hlitS, hlitT, Set.ncard_empty] at hbc
  by_cases hne : (OccSet c).Nonempty
  · have hemp : ¬EmptyCl c := by
      rintro ⟨-, hno⟩
      obtain ⟨p, hp⟩ := hne
      exact hno p.1 p.2 hp
    rw [if_neg (fun h => hemp h.1), if_neg (fun h => hemp h.1)] at hbc
    have hle : ({p ∈ MidSet c | S (pSlk p.2 c p.1)} : Set (A × Bool)).ncard ≤
        (MidSet c).ncard := Set.ncard_le_ncard (fun p hp => hp.1) (Set.toFinite _)
    have hlt := card_midSet_lt hne
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hemp : EmptyCl c := ⟨hc, fun x s hx => by
      have hx' : ((x, s) : A × Bool) ∈ OccSet c := hx
      rw [hne] at hx'
      exact hx'⟩
    have hmid : MidSet c = ∅ := Set.subset_empty_iff.mp (hne ▸ midSet_subset)
    have hz : ∀ U : pInterp.Map A → Prop,
        ({p ∈ MidSet c | U (pSlk p.2 c p.1)} : Set (A × Bool)).ncard = 0 := by
      intro U
      have hsub : {p ∈ MidSet c | U (pSlk p.2 c p.1)} ⊆ (∅ : Set (A × Bool)) :=
        fun p hp => hmid ▸ hp.1
      rw [Set.subset_empty_iff.mp hsub, Set.ncard_empty]
    have hitem : BWItem (pEmp a₀ c) := by
      rw [pEmp]
      exact (bwItem_emp _).mpr ⟨by simpa using hemp, by simpa using ha₀⟩
    have hcp := hcompl (pEmp a₀ c) hitem
    rw [hne, Set.ncard_empty, hz S, hz T] at hbc
    by_cases hSe : S (pEmp a₀ c)
    · rw [if_pos ⟨hemp, hSe⟩, if_neg (fun h => hcp.mp hSe h.2)] at hbc
      omega
    · have hTe : T (pEmp a₀ c) := by
        by_contra h
        exact hSe (hcp.mpr h)
      rw [if_neg (fun h => hSe h.2), if_pos ⟨hemp, hTe⟩] at hbc
      omega

/-- **Correctness of the reduction**: a CNF structure is not-all-equal
satisfiable iff the interpreted binary-weighted instance splits into two
halves of equal weight. -/
theorem naeSatisfiable_iff_hasEqualSplit (A : Type) [Language.sat.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] : NAESatisfiable A ↔ HasEqualSplit (pInterp.Map A) := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  haveI : Finite (pInterp.Map A) := pInterp.map_finite A
  constructor
  · rintro ⟨ν, hν⟩
    -- a clause has a true occurrence, and at least one more occurrence
    have hocc : ∀ c : A, IsCl c →
        1 ≤ (TrueSet ν c).ncard ∧ (TrueSet ν c).ncard < (OccSet c).ncard := by
      intro c hc
      obtain ⟨⟨x, s, hx, hxT⟩, ⟨y, t, hy, hyT⟩⟩ := naeProper_occ hν c hc
      have h1 : 0 < (TrueSet ν c).ncard :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨(x, s), hx, hxT⟩
      refine ⟨by omega, ?_⟩
      refine Set.ncard_lt_ncard ⟨fun p hp => hp.1, fun hsub => ?_⟩ (Set.toFinite _)
      exact hyT (hsub (show ((y, t) : A × Bool) ∈ OccSet c from hy)).2
    have hOccEmpty : ∀ c : A, ¬IsCl c → OccSet c = ∅ := by
      intro c hc
      ext p
      simp only [OccSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hc h.1
    -- enough slack to balance every clause block
    have hsub : ∀ c : A,
        ((OccSet c).ncard - 1 - (TrueSet ν c).ncard) ≤ (MidSet c).ncard := by
      intro c
      by_cases hc : IsCl c
      · by_cases hne : (OccSet c).Nonempty
        · obtain ⟨h1, h2⟩ := hocc c hc
          have h3 := card_midSet_add_two (show 2 ≤ (OccSet c).ncard by omega)
          omega
        · rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, Set.ncard_empty]
          omega
      · rw [hOccEmpty c hc, Set.ncard_empty]
        omega
    choose M hMsub hMcard using fun c : A => Set.exists_subset_card_eq (hsub c)
    have hitems : ∀ i, splitSet a₀ ν M i → BWItem i := by
      rintro i (⟨p, -, rfl⟩ | ⟨c, p, hp, rfl⟩)
      · rw [pLit]
        exact (bwItem_lit _ _).mpr (by simpa using ha₀)
      · rw [pSlk]
        exact (bwItem_slk _ _).mpr (by simpa [MidSet] using hMsub c hp)
    refine ⟨inferInstance, isLinOrd_bwLe, splitSet a₀ ν M, hitems, ?_⟩
    rw [sum_eq_iff ha₀ hitems]
    rintro ⟨k, e⟩
    cases k with
    | false =>
      rw [cnt_var ha₀, cnt_item_var ha₀]
      have hset : {s : Bool | splitSet a₀ ν M (pLit a₀ s e)} = {s | LitTrue ν e s} := by
        ext s
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, splitSet_pLit]
      rw [hset]
      have hone : ({s : Bool | LitTrue ν e s} : Set Bool).ncard = 1 := by
        by_cases hv : ν e
        · have : {s : Bool | LitTrue ν e s} = {true} := by
            ext s
            cases s <;> simp [LitTrue, hv]
          rw [this, Set.ncard_singleton]
        · have : {s : Bool | LitTrue ν e s} = {false} := by
            ext s
            cases s <;> simp [LitTrue, hv]
          rw [this, Set.ncard_singleton]
      rw [hone]
    | true =>
      rw [cnt_cls ha₀, cnt_item_cls ha₀]
      have hlit : {p ∈ OccSet e | splitSet a₀ ν M (pLit a₀ p.2 p.1)} = TrueSet ν e := by
        ext p
        rw [Set.mem_sep_iff, splitSet_pLit]
        exact Iff.rfl
      have hslk : {p ∈ MidSet e | splitSet a₀ ν M (pSlk p.2 e p.1)} = M e := by
        ext p
        rw [Set.mem_sep_iff, splitSet_pSlk]
        constructor
        · rintro ⟨-, h⟩
          simpa using h
        · intro h
          exact ⟨hMsub e h, by simpa using h⟩
      rw [hlit, hslk, if_neg (fun h : _ ∧ _ => splitSet_pEmp e h.2), hMcard e]
      by_cases hc : IsCl e
      · obtain ⟨h1, h2⟩ := hocc e hc
        have h3 := card_midSet_add_two (show 2 ≤ (OccSet e).ncard by omega)
        have hemp : ¬EmptyCl e := by
          rintro ⟨-, hno⟩
          have hne : (OccSet e).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
          obtain ⟨p, hp⟩ := hne
          exact hno p.1 p.2 hp
        rw [if_neg hemp]
        omega
      · have ho := hOccEmpty e hc
        have hm : MidSet e = ∅ := Set.subset_empty_iff.mp (ho ▸ midSet_subset)
        have hTe : TrueSet ν e = ∅ :=
          Set.subset_empty_iff.mp (ho ▸ (fun p hp => hp.1 : TrueSet ν e ⊆ OccSet e))
        rw [hTe, ho, hm, Set.ncard_empty, if_neg (fun h : EmptyCl e => hc h.1)]
  · rintro ⟨-, -, S, hSi, hsum⟩
    have hbal := (sum_eq_iff ha₀ hSi).mp hsum
    have hcompl : ∀ i, BWItem i → (S i ↔ ¬(BWItem i ∧ ¬S i)) := by
      intro i hi
      constructor
      · rintro h ⟨-, hn⟩
        exact hn h
      · intro h
        by_contra hn
        exact h ⟨hi, hn⟩
    have hbal' : ∀ b, cnt a₀ S b = cnt a₀ (fun i => BWItem i ∧ ¬S i) b := by
      intro b
      have h1 := cnt_add_cnt a₀ hSi b
      have h2 := hbal b
      omega
    refine ⟨fun y => S (pLit a₀ true y), naeProper_of_occ fun c hc => ?_⟩
    obtain ⟨p, hp, hpS⟩ := exists_occ_selected ha₀ hcompl hbal' hc
    obtain ⟨q, hq, hqT⟩ := exists_occ_selected ha₀
      (fun i hi => ⟨fun h hn => h.2 hn, fun h => ⟨hi, h⟩⟩) (fun b => (hbal' b).symm) hc
    exact ⟨⟨p.1, p.2, hp, (litTrue_iff_sel ha₀ hbal p.1 p.2).mp hpS⟩,
      ⟨q.1, q.2, hq, fun hT => hqT.2 ((litTrue_iff_sel ha₀ hbal q.1 q.2).mpr hT)⟩⟩

end Correct

end PartRed

open PartRed in
/-- **NAE-SAT ordered-FO-reduces to Partition**: one item per literal, one per
slack occurrence and one per empty clause; one digit block of `3 |A|` bit
positions per variable and per clause. A variable block totals `2`, so a
balanced split is an assignment; a clause block of width `w` totals
`w + (w − 2)`, so a balanced split takes between `1` and `w − 1` true
literals, which is not-all-equal satisfaction. -/
noncomputable def naeSat_ordered_fo_reduction_partition : NAESAT ≤ᶠᵒ[≤] Partition where
  Tag := PTag
  dim := 2
  toInterpretation := pInterp
  correct A _ _ _ _ := naeSatisfiable_iff_hasEqualSplit A

end DescriptiveComplexity
