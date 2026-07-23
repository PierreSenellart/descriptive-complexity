/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Knapsack.Defs
import DescriptiveComplexity.Problems.SetFamily
import DescriptiveComplexity.Numbers.Digits
import DescriptiveComplexity.Padding

/-!
# Knapsack is NP-hard

The reduction is Karp's, from EXACT COVER: give the set `s` the weight
`∑_{e ∈ s} B ^ rank e`, one *digit block* per ground element, and give the
target the digit `1` in every block. A subfamily then has the right weight
exactly when it covers every element once – provided that the digits never
carry, which is what choosing the base `B` above the number of sets buys.

## The gadget, in the shape an interpretation can build

The base is `B = 2 ^ |A|`, so a block is `|A|` bit positions, and the bit
positions are *pairs*: the position `(e, x)` is the `x`-th bit of the block of
the ground element `e`. The order on positions is lexicographic, so the block
of `e` is a contiguous range of `|A|` positions and the rank of its lowest
position is `|A| * rank e` (`DescriptiveComplexity.KnapRed.bitRank_kLow`) – place
value `(2 ^ |A|) ^ rank e`, as wanted.

Only the *lowest* position of a block ever carries a bit: the weight of `s`
has a `1` at `(e, ⊥)` for `e ∈ s`, and the target has a `1` at `(e, ⊥)` for
every `e`. The digit of the block of `e` in the sum over a subfamily `G` is
therefore the number of sets of `G` containing `e`, at most the number of
sets, hence at most `|A| < 2 ^ |A| = B`. Uniqueness of base-`B` expansions
(`DescriptiveComplexity.digitNum_inj`) turns the equation into “every digit is `1`”,
which is exactly exactness of the cover.

The order is needed twice – to say “the lowest position of a block” and to
pin the padding of the items down to a single representative – so this is an
`DescriptiveComplexity.OrderedFOReduction`, and being one has the pleasant side effect
of supplying the finiteness that the counting needs.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace KnapRed

open Language Structure

/-! ### Formula builders over the ordered expansion of set systems -/

/-- The ordered expansion of the language of set systems. -/
abbrev ssOrd : Language := Language.setSystem.sum Language.order

/-- The ground-element symbol in the ordered expansion. -/
abbrev elemSym : ssOrd.Relations 1 := Sum.inl ssElem

/-- The family symbol in the ordered expansion. -/
abbrev famSym : ssOrd.Relations 1 := Sum.inl ssFam

/-- The incidence symbol in the ordered expansion. -/
abbrev memSym : ssOrd.Relations 2 := Sum.inl ssMem

section Builders

variable {α : Type}

/-- `x` is a ground element, as a formula. -/
def elemF (x : α) : ssOrd.Formula α := Relations.formula₁ elemSym (Term.var x)

/-- `f` is a set of the family, as a formula. -/
def famF (f : α) : ssOrd.Formula α := Relations.formula₁ famSym (Term.var f)

/-- `x` belongs to `f`, as a formula. -/
def memF (x f : α) : ssOrd.Formula α :=
  Relations.formula₂ memSym (Term.var x) (Term.var f)

/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : ssOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : ssOrd.Formula α := Term.equal (Term.var x) (Term.var y)

/-- `x < y`, as a formula. -/
def ltF (x y : α) : ssOrd.Formula α := leF x y ⊓ ∼(eqF x y)

/-- `x` holds a minimum of the order, as a formula. -/
noncomputable def minF (x : α) : ssOrd.Formula α := botF (L := Language.setSystem) x

end Builders

section RealizeBuilders

variable {α A : Type} [Language.setSystem.Structure A] [LinearOrder A] {v : α → A}

@[simp]
theorem realize_elemF {x : α} : (elemF x).Realize v ↔ SSElem (v x) := by
  rw [elemF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_famF {f : α} : (famF f).Realize v ↔ SSFam (v f) := by
  rw [famF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_memF {x f : α} : (memF x f).Realize v ↔ SSMem (v x) (v f) := by
  rw [memF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize v ↔ v x ≤ v y := by
  simp [leF, Formula.realize_rel₂]

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize v ↔ v x < v y := by
  simp [ltF, lt_iff_le_and_ne]

@[simp]
theorem realize_minF {x : α} : (minF x).Realize v ↔ IsBot (v x) :=
  realize_botF

end RealizeBuilders

/-! ### Lexicographic order on pairs -/

section Lex

variable {A : Type} [LinearOrder A]

/-- The lexicographic order on pairs of elements, as the interpretation sees
them: coordinates of a `2`-tuple. -/
def Lex2 (w w' : Fin 2 → A) : Prop := w 0 < w' 0 ∨ (w 0 = w' 0 ∧ w 1 ≤ w' 1)

omit [LinearOrder A] in
/-- Two `2`-tuples with the same coordinates are equal. -/
theorem tuple₂_ext {w w' : Fin 2 → A} (h0 : w 0 = w' 0) (h1 : w 1 = w' 1) : w = w' := by
  funext j
  fin_cases j
  · exact h0
  · exact h1

theorem lex2_refl (w : Fin 2 → A) : Lex2 w w := Or.inr ⟨rfl, le_rfl⟩

theorem lex2_trans {u v w : Fin 2 → A} (h₁ : Lex2 u v) (h₂ : Lex2 v w) : Lex2 u w := by
  rcases h₁ with h | ⟨he, hle⟩ <;> rcases h₂ with h' | ⟨he', hle'⟩
  · exact Or.inl (h.trans h')
  · exact Or.inl (he' ▸ h)
  · exact Or.inl (he ▸ h')
  · exact Or.inr ⟨he.trans he', hle.trans hle'⟩

theorem lex2_antisymm {u v : Fin 2 → A} (h₁ : Lex2 u v) (h₂ : Lex2 v u) : u = v := by
  rcases h₁ with h | ⟨he, hle⟩ <;> rcases h₂ with h' | ⟨he', hle'⟩
  · exact absurd h' (asymm h)
  · exact absurd he' (ne_of_gt h)
  · exact absurd he (ne_of_gt h')
  · exact tuple₂_ext he (hle.antisymm hle')

theorem lex2_total (u v : Fin 2 → A) : Lex2 u v ∨ Lex2 v u := by
  rcases lt_trichotomy (u 0) (v 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (u 1) (v 1) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

end Lex


/-! ### The interpretation -/

/-- Tags of the reduction: the items (one per set of the family) and the bit
positions (one per pair “ground element, index inside its block”). -/
inductive KTag : Type
  /-- The item of a set of the family. -/
  | itm
  /-- A bit position. -/
  | pos
  deriving DecidableEq

instance : Fintype KTag where
  elems := {KTag.itm, KTag.pos}
  complete := by
    intro t
    cases t <;> decide

instance : Nonempty KTag := ⟨KTag.itm⟩

/-- Defining formula for the items: the sets of the family, padded
canonically. -/
noncomputable def itemF : KTag → ssOrd.Formula (Fin 1 × Fin 2)
  | .itm => famF (0, 0) ⊓ minF (0, 1)
  | .pos => ⊥

/-- Defining formula for the bit positions: the pairs whose first coordinate
is a ground element. -/
def posnF : KTag → ssOrd.Formula (Fin 1 × Fin 2)
  | .pos => elemF (0, 0)
  | .itm => ⊥

/-- Defining formula for the bits of the weights: the weight of the set `s`
has a `1` at the lowest position of the block of `e` exactly when `e ∈ s`. -/
noncomputable def bitF : KTag → KTag → ssOrd.Formula (Fin 2 × Fin 2)
  | .itm, .pos => famF (0, 0) ⊓ minF (0, 1) ⊓ elemF (1, 0) ⊓ memF (1, 0) (0, 0) ⊓ minF (1, 1)
  | _, _ => ⊥

/-- Defining formula for the bits of the target: a `1` at the lowest position
of every block. -/
noncomputable def tgtF : KTag → ssOrd.Formula (Fin 1 × Fin 2)
  | .pos => elemF (0, 0) ⊓ minF (0, 1)
  | .itm => ⊥

/-- The lexicographic comparison of the two argument tuples, as a formula. -/
def lexF : ssOrd.Formula (Fin 2 × Fin 2) :=
  ltF (0, 0) (1, 0) ⊔ (eqF (0, 0) (1, 0) ⊓ leF (0, 1) (1, 1))

/-- Defining formula for the order: items first, positions next, each group
ordered lexicographically. -/
def leKF : KTag → KTag → ssOrd.Formula (Fin 2 × Fin 2)
  | .itm, .itm => lexF
  | .itm, .pos => ⊤
  | .pos, .itm => ⊥
  | .pos, .pos => lexF

/-- The interpretation of a binary-weighted instance in a set system: one item
per set, one bit position per pair “ground element, index”. -/
noncomputable def kInterp : FOInterpretation ssOrd Language.binWeights KTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .item => fun t => itemF (t 0)
    | _, .posn => fun t => posnF (t 0)
    | _, .bit => fun t => bitF (t 0) (t 1)
    | _, .tgt => fun t => tgtF (t 0)
    | _, .le => fun t => leKF (t 0) (t 1)

/-! ### The points of the interpreted structure -/

section Points

variable {A : Type}

/-- The point of tag `t` over the pair `w`. -/
def kPt (t : KTag) (w : Fin 2 → A) : kInterp.Map A := (t, w)

theorem kPt_surj (q : kInterp.Map A) : ∃ t w, q = kPt t w := ⟨q.1, q.2, rfl⟩

theorem kPt_eq_iff {t t' : KTag} {w w' : Fin 2 → A} :
    kPt t w = kPt t' w' ↔ t = t' ∧ w = w' := by
  constructor
  · intro h
    exact ⟨congrArg (fun q : kInterp.Map A => q.1) h, congrArg (fun q : kInterp.Map A => q.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem kPt_snd (t : KTag) (w : Fin 2 → A) (j : Fin 2) : (kPt t w).2 j = w j := rfl

/-- The item of the set `s`, padded with the minimum `a₀`. -/
def kItem (a₀ s : A) : kInterp.Map A := kPt .itm ![s, a₀]

/-- The bit position `(e, x)`: the `x`-th position of the block of `e`. -/
def kPos (e x : A) : kInterp.Map A := kPt .pos ![e, x]

/-- The lowest position of the block of `e`. -/
def kLow (a₀ e : A) : kInterp.Map A := kPos e a₀

@[simp]
theorem kItem_fst (a₀ s : A) : (kItem a₀ s).2 0 = s := rfl

@[simp]
theorem kLow_fst (a₀ e : A) : (kLow a₀ e).2 0 = e := rfl

@[simp]
theorem kLow_snd (a₀ e : A) : (kLow a₀ e).2 1 = a₀ := rfl

theorem kItem_injective (a₀ : A) : Function.Injective (kItem a₀) := fun _ _ h =>
  congrArg (fun q : kInterp.Map A => q.2 0) h

theorem kLow_injective (a₀ : A) : Function.Injective (kLow a₀) := fun _ _ h =>
  congrArg (fun q : kInterp.Map A => q.2 0) h

/-- Being the lowest position of a block, coordinate by coordinate. -/
theorem eq_kLow_iff {a₀ e : A} {t : KTag} {w : Fin 2 → A} :
    kPt t w = kLow a₀ e ↔ t = KTag.pos ∧ w = ![e, a₀] := kPt_eq_iff

end Points

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.setSystem.Structure A] [LinearOrder A]

@[simp]
theorem bwItem_itm (w : Fin 2 → A) :
    BWItem (kPt .itm w) ↔ SSFam (w 0) ∧ IsBot (w 1) := by
  rw [BWItem, kPt, FOInterpretation.relMap_map]
  simp [kInterp, itemF]

@[simp]
theorem bwItem_pos (w : Fin 2 → A) : ¬BWItem (kPt .pos w) := by
  rw [BWItem, kPt, FOInterpretation.relMap_map]
  simp [kInterp, itemF]

@[simp]
theorem bwPosn_pos (w : Fin 2 → A) : BWPosn (kPt .pos w) ↔ SSElem (w 0) := by
  rw [BWPosn, kPt, FOInterpretation.relMap_map]
  simp [kInterp, posnF]

@[simp]
theorem bwPosn_itm (w : Fin 2 → A) : ¬BWPosn (kPt .itm w) := by
  rw [BWPosn, kPt, FOInterpretation.relMap_map]
  simp [kInterp, posnF]

@[simp]
theorem bwTgt_pos (w : Fin 2 → A) :
    BWTgt (kPt .pos w) ↔ SSElem (w 0) ∧ IsBot (w 1) := by
  rw [BWTgt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, tgtF]

@[simp]
theorem bwTgt_itm (w : Fin 2 → A) : ¬BWTgt (kPt .itm w) := by
  rw [BWTgt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, tgtF]

@[simp]
theorem bwBit_itm_pos (w w' : Fin 2 → A) :
    BWBit (kPt .itm w) (kPt .pos w') ↔
      (SSFam (w 0) ∧ IsBot (w 1)) ∧ SSElem (w' 0) ∧ SSMem (w' 0) (w 0) ∧ IsBot (w' 1) := by
  rw [BWBit, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, bitF, and_assoc]

@[simp]
theorem bwBit_itm_itm (w w' : Fin 2 → A) : ¬BWBit (kPt .itm w) (kPt .itm w') := by
  rw [BWBit, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, bitF]

@[simp]
theorem bwBit_pos (w w' : Fin 2 → A) (t : KTag) : ¬BWBit (kPt .pos w) (kPt t w') := by
  rw [BWBit, kPt, kPt, FOInterpretation.relMap_map]
  cases t <;> simp [kInterp, bitF]

@[simp]
theorem bwLe_itm_itm (w w' : Fin 2 → A) :
    BWLe (kPt .itm w) (kPt .itm w') ↔ Lex2 w w' := by
  rw [BWLe, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, leKF, lexF, Lex2]

@[simp]
theorem bwLe_pos_pos (w w' : Fin 2 → A) :
    BWLe (kPt .pos w) (kPt .pos w') ↔ Lex2 w w' := by
  rw [BWLe, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, leKF, lexF, Lex2]

@[simp]
theorem bwLe_itm_pos (w w' : Fin 2 → A) : BWLe (kPt .itm w) (kPt .pos w') := by
  rw [BWLe, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, leKF]

/-- Comparison with the lowest position of a block. -/
theorem bwLe_pos_kLow (w : Fin 2 → A) (a₀ e : A) :
    BWLe (kPt .pos w) (kLow a₀ e) ↔ Lex2 w ![e, a₀] := bwLe_pos_pos w ![e, a₀]

@[simp]
theorem bwLe_pos_itm (w w' : Fin 2 → A) : ¬BWLe (kPt .pos w) (kPt .itm w') := by
  rw [BWLe, kPt, kPt, FOInterpretation.relMap_map]
  simp [kInterp, leKF]

/-- The interpreted order is a linear order: the two tags in order, each
carrying the lexicographic order on pairs. -/
theorem isLinOrd_bwLe : IsLinOrd (BWLe (A := kInterp.Map A)) := by
  refine ⟨fun q => ?_, fun q₁ q₂ q₃ h₁ h₂ => ?_, fun q₁ q₂ h₁ h₂ => ?_, fun q₁ q₂ => ?_⟩
  · obtain ⟨t, w, rfl⟩ := kPt_surj q
    cases t
    · exact (bwLe_itm_itm w w).mpr (lex2_refl w)
    · exact (bwLe_pos_pos w w).mpr (lex2_refl w)
  · obtain ⟨t₁, w₁, rfl⟩ := kPt_surj q₁
    obtain ⟨t₂, w₂, rfl⟩ := kPt_surj q₂
    obtain ⟨t₃, w₃, rfl⟩ := kPt_surj q₃
    cases t₁ <;> cases t₂ <;> cases t₃
    · exact (bwLe_itm_itm _ _).mpr
        (lex2_trans ((bwLe_itm_itm _ _).mp h₁) ((bwLe_itm_itm _ _).mp h₂))
    · exact bwLe_itm_pos _ _
    · exact absurd h₂ (bwLe_pos_itm _ _)
    · exact bwLe_itm_pos _ _
    · exact absurd h₁ (bwLe_pos_itm _ _)
    · exact absurd h₁ (bwLe_pos_itm _ _)
    · exact absurd h₂ (bwLe_pos_itm _ _)
    · exact (bwLe_pos_pos _ _).mpr
        (lex2_trans ((bwLe_pos_pos _ _).mp h₁) ((bwLe_pos_pos _ _).mp h₂))
  · obtain ⟨t₁, w₁, rfl⟩ := kPt_surj q₁
    obtain ⟨t₂, w₂, rfl⟩ := kPt_surj q₂
    cases t₁ <;> cases t₂
    · exact congrArg (kPt KTag.itm)
        (lex2_antisymm ((bwLe_itm_itm _ _).mp h₁) ((bwLe_itm_itm _ _).mp h₂))
    · exact absurd h₂ (bwLe_pos_itm _ _)
    · exact absurd h₁ (bwLe_pos_itm _ _)
    · exact congrArg (kPt KTag.pos)
        (lex2_antisymm ((bwLe_pos_pos _ _).mp h₁) ((bwLe_pos_pos _ _).mp h₂))
  · obtain ⟨t₁, w₁, rfl⟩ := kPt_surj q₁
    obtain ⟨t₂, w₂, rfl⟩ := kPt_surj q₂
    cases t₁ <;> cases t₂
    · exact (lex2_total w₁ w₂).imp (bwLe_itm_itm _ _).mpr (bwLe_itm_itm _ _).mpr
    · exact Or.inl (bwLe_itm_pos _ _)
    · exact Or.inr (bwLe_itm_pos _ _)
    · exact (lex2_total w₁ w₂).imp (bwLe_pos_pos _ _).mpr (bwLe_pos_pos _ _).mpr

end Characterizations

/-! ### The place values -/

section Places

variable {A : Type} [Language.setSystem.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
/-- An item is the padded item of the set it carries. -/
theorem eq_kItem {a₀ : A} (ha₀ : IsBot a₀) {i : kInterp.Map A} (h : BWItem i) :
    i = kItem a₀ (i.2 0) ∧ SSFam (i.2 0) := by
  obtain ⟨t, w, rfl⟩ := kPt_surj i
  cases t
  · obtain ⟨hs, hb⟩ := (bwItem_itm w).mp h
    refine ⟨?_, hs⟩
    rw [kPt_snd, kItem]
    exact congrArg (kPt KTag.itm)
      (tuple₂_ext (by simp) (by simp [(ha₀ (w 1)).antisymm (hb a₀)]))
  · exact absurd h (bwItem_pos w)

omit [Finite A] in
/-- **The block structure**: the rank of the lowest position of the block of
`e` is `|A|` times the rank of `e`, so its place value is `(2 ^ |A|) ^ rank e`
– one digit of base `2 ^ |A|` per ground element. -/
theorem bitRank_kLow {a₀ : A} (ha₀ : IsBot a₀) (e : A) :
    bitRank (BWLe (A := kInterp.Map A)) BWPosn (kLow a₀ e) =
      Nat.card A * bitRank (· ≤ · : A → A → Prop) SSElem e := by
  have hinj : Set.InjOn (fun ax : A × A => kPos ax.1 ax.2)
      ({a | SSElem a ∧ a ≤ e ∧ a ≠ e} ×ˢ (Set.univ : Set A)) := by
    rintro ⟨a, x⟩ - ⟨a', x'⟩ - h
    have h0 := congrArg (fun q : kInterp.Map A => q.2 0) h
    have h1 := congrArg (fun q : kInterp.Map A => q.2 1) h
    exact Prod.ext_iff.mpr ⟨by simpa [kPos] using h0, by simpa [kPos] using h1⟩
  have hset : {q : kInterp.Map A | BWPosn q ∧ BWLe q (kLow a₀ e) ∧ q ≠ kLow a₀ e} =
      (fun ax : A × A => kPos ax.1 ax.2) '' ({a | SSElem a ∧ a ≤ e ∧ a ≠ e} ×ˢ Set.univ) := by
    ext q
    obtain ⟨t, w, rfl⟩ := kPt_surj q
    constructor
    · rintro ⟨hp, hle, hne⟩
      cases t
      · exact absurd hp (bwPosn_itm w)
      · rw [bwLe_pos_kLow] at hle
        have hlt : w 0 < e := by
          rcases hle with h | ⟨he, hx⟩
          · simpa using h
          · refine absurd ?_ hne
            exact congrArg (kPt KTag.pos) (tuple₂_ext (by simpa using he)
              (by simp [(ha₀ (w 1)).antisymm (by simpa using hx)]))
        exact ⟨(w 0, w 1), ⟨⟨(bwPosn_pos w).mp hp, hlt.le, ne_of_lt hlt⟩, Set.mem_univ _⟩,
          (congrArg (kPt KTag.pos) (tuple₂_ext (by simp) (by simp))).symm⟩
    · rintro ⟨⟨a, x⟩, ⟨⟨hea, hle, hne⟩, -⟩, hq⟩
      obtain ⟨rfl, rfl⟩ : KTag.pos = t ∧ (![a, x] : Fin 2 → A) = w := kPt_eq_iff.mp hq
      refine ⟨by simpa using hea, ?_, ?_⟩
      · rw [bwLe_pos_kLow]
        exact Or.inl (by simpa using lt_of_le_of_ne hle hne)
      · intro hcon
        exact hne (by simpa using congrArg (fun q : kInterp.Map A => q.2 0) hcon)
  rw [bitRank, hset, hinj.ncard_image, Set.ncard_prod, Set.ncard_univ, bitRank, Nat.mul_comm]

end Places

/-! ### Weights and target, as base-`2 ^ |A|` numbers -/

section Numbers

variable {A : Type} [Language.setSystem.Structure A] [LinearOrder A] [Finite A]

/-- The base: one digit per ground element, `|A|` bits wide, which is above
the number of sets, so digits never carry into the next block. -/
noncomputable def base (A : Type) [Finite A] : ℕ := 2 ^ Nat.card A

omit [Language.setSystem.Structure A] [LinearOrder A] in
theorem base_pos : 0 < base A := by
  rw [base]
  positivity

omit [Language.setSystem.Structure A] [LinearOrder A] in
theorem one_lt_base [Nonempty A] : 1 < base A := by
  rw [base]
  exact Nat.one_lt_two_pow (Nat.card_pos (α := A)).ne'

open Classical in
/-- A binary number whose bits sit on the lowest positions of the blocks
selected by `sub` is the base-`2 ^ |A|` number with digit `1` there. -/
theorem binNum_eq_digit {a₀ : A} (ha₀ : IsBot a₀) {p : kInterp.Map A → Prop} {sub : A → Prop}
    (hsub : ∀ e, sub e → SSElem e)
    (hp : ∀ q : kInterp.Map A, (BWPosn q ∧ p q) ↔ ∃ e, sub e ∧ q = kLow a₀ e) :
    binNum (BWLe (A := kInterp.Map A)) BWPosn p =
      digitNum (· ≤ · : A → A → Prop) SSElem (base A) (fun e => if sub e then 1 else 0) := by
  classical
  have hset : {q : kInterp.Map A | BWPosn q ∧ p q} = kLow a₀ '' {e | sub e} := by
    ext q
    rw [Set.mem_setOf_eq, hp q]
    exact ⟨fun ⟨e, he, hq⟩ => ⟨e, he, hq.symm⟩, fun ⟨e, he, hq⟩ => ⟨e, he, hq.symm⟩⟩
  rw [binNum, hset, finsum_mem_image (kLow_injective a₀).injOn]
  refine (finsum_mem_congr rfl fun e _ => ?_).trans (finsum_pow_eq_digitNum hsub)
  rw [bitRank_kLow ha₀, base, pow_mul]

open Classical in
/-- The target is the number with digit `1` in every block. -/
theorem bwTarget_eq {a₀ : A} (ha₀ : IsBot a₀) :
    BWTarget (kInterp.Map A) =
      digitNum (· ≤ · : A → A → Prop) SSElem (base A) (fun e => if SSElem e then 1 else 0) := by
  refine binNum_eq_digit ha₀ (fun _ he => he) fun q => ?_
  obtain ⟨t, w, rfl⟩ := kPt_surj q
  cases t
  · refine ⟨fun h => absurd h.1 (bwPosn_itm w), ?_⟩
    rintro ⟨e, -, hq⟩
    rw [eq_kLow_iff] at hq
    exact absurd hq.1 (by decide)
  · constructor
    · rintro ⟨hp, htgt⟩
      refine ⟨w 0, (bwPosn_pos w).mp hp, ?_⟩
      exact congrArg (kPt KTag.pos) (tuple₂_ext (by simp)
        (by simp [(ha₀ (w 1)).antisymm (((bwTgt_pos w).mp htgt).2 a₀)]))
    · rintro ⟨e, he, hq⟩
      rw [eq_kLow_iff] at hq
      obtain ⟨-, rfl⟩ := hq
      exact ⟨by simpa using he, by simpa using ⟨he, ha₀⟩⟩

open Classical in
/-- The weight of an item is the number with digit `1` in the blocks of the
elements of its set. -/
theorem bwWeight_eq {a₀ : A} (ha₀ : IsBot a₀) {i : kInterp.Map A} (h : BWItem i) :
    BWWeight i = digitNum (· ≤ · : A → A → Prop) SSElem (base A)
      (fun e => if SSElem e ∧ SSMem e (i.2 0) then 1 else 0) := by
  obtain ⟨hi, hfam⟩ := eq_kItem ha₀ h
  refine (binNum_eq_digit (sub := fun e => SSElem e ∧ SSMem e (i.2 0)) ha₀
    (fun _ he => he.1) fun q => ?_).trans (digitNum_congr_on fun e _ => ?_)
  · obtain ⟨t, w, rfl⟩ := kPt_surj q
    cases t
    · refine ⟨fun hq => absurd hq.1 (bwPosn_itm w), ?_⟩
      rintro ⟨e, -, hq⟩
      rw [eq_kLow_iff] at hq
      exact absurd hq.1 (by decide)
    · rw [hi, kItem]
      constructor
      · rintro ⟨hp, hbit⟩
        obtain ⟨-, he, hmem, hb⟩ := (bwBit_itm_pos ![i.2 0, a₀] w).mp hbit
        refine ⟨w 0, ⟨he, by simpa using hmem⟩, ?_⟩
        exact congrArg (kPt KTag.pos)
          (tuple₂_ext (by simp) (by simp [(ha₀ (w 1)).antisymm (hb a₀)]))
      · rintro ⟨e, ⟨he, hmem⟩, hq⟩
        rw [eq_kLow_iff] at hq
        obtain ⟨-, rfl⟩ := hq
        refine ⟨by simpa using he, ?_⟩
        rw [bwBit_itm_pos]
        exact ⟨⟨by simpa using hfam, by simpa using ha₀⟩, by simpa using he,
          by simpa using hmem, by simpa using ha₀⟩
  · by_cases he : SSElem e ∧ SSMem e (i.2 0) <;> simp [he]

end Numbers

/-! ### The counting step -/

section Counting

variable {A : Type} [Language.setSystem.Structure A] [LinearOrder A] [Finite A]

open Classical in
/-- **The sum of the selected weights**, read digit by digit: the digit of the
block of `e` is the number of selected items whose set contains `e`. -/
theorem sum_weights_eq {a₀ : A} (ha₀ : IsBot a₀) {S : kInterp.Map A → Prop}
    (hS : ∀ i, S i → BWItem i) :
    (∑ᶠ i ∈ {i | S i}, BWWeight i) =
      digitNum (· ≤ · : A → A → Prop) SSElem (base A)
        (fun e => ({i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} : Set _).ncard) := by
  classical
  haveI : Finite (kInterp.Map A) := kInterp.map_finite A
  have h₁ : (∑ᶠ i ∈ {i | S i}, BWWeight i) =
      ∑ᶠ i ∈ {i | S i}, digitNum (· ≤ · : A → A → Prop) SSElem (base A)
        (fun e => if SSElem e ∧ SSMem e (i.2 0) then 1 else 0) :=
    finsum_mem_congr rfl fun i hi => bwWeight_eq ha₀ (hS i hi)
  rw [h₁, digitNum_finsum]
  refine digitNum_congr_on fun e _ => ?_
  refine (finsum_mem_ite_one (ι := kInterp.Map A) _ _).trans ?_
  exact congrArg Set.ncard (by ext i; simp)

/-- Only items are selected, and there are at most `|A|` of them, so the
digits of the sum stay below the base. -/
theorem count_lt_base {S : kInterp.Map A → Prop} (hS : ∀ i, S i → BWItem i)
    {a₀ : A} (ha₀ : IsBot a₀) (e : A) :
    ({i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} : Set _).ncard < base A := by
  haveI : Finite (kInterp.Map A) := kInterp.map_finite A
  have hsub : {i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} ⊆
      kItem a₀ '' (Set.univ : Set A) := by
    rintro i ⟨hi, -, -⟩
    exact ⟨i.2 0, Set.mem_univ _, ((eq_kItem ha₀ (hS i hi)).1).symm⟩
  have h₁ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h₂ : (kItem a₀ '' (Set.univ : Set A)).ncard = Nat.card A := by
    rw [(kItem_injective a₀).injOn.ncard_image, Set.ncard_univ]
  exact lt_of_le_of_lt (h₁.trans h₂.le) (by simpa [base] using Nat.lt_two_pow_self)

end Counting

/-! ### Correctness -/

section Correctness

variable (A : Type) [Language.setSystem.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

open Classical in
/-- **Correctness of the reduction**: the set system has an exact cover iff the
interpreted binary-weighted instance has a set of items summing to the
target. -/
theorem hasExactCover_iff_hasSubsetSum :
    HasExactCover A ↔ HasSubsetSum (kInterp.Map A) := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  haveI : Finite (kInterp.Map A) := kInterp.map_finite A
  constructor
  · rintro ⟨G, hGfam, hcov, hdisj⟩
    have hS : ∀ i : kInterp.Map A, (∃ s, G s ∧ i = kItem a₀ s) → BWItem i := by
      rintro i ⟨s, hs, rfl⟩
      exact (bwItem_itm _).mpr ⟨by simpa [kItem] using hGfam s hs, by simpa [kItem] using ha₀⟩
    refine ⟨inferInstance, isLinOrd_bwLe, fun i => ∃ s, G s ∧ i = kItem a₀ s, hS, ?_⟩
    rw [sum_weights_eq ha₀ hS, bwTarget_eq ha₀]
    refine digitNum_congr_on fun e he => ?_
    obtain ⟨s₀, hs₀, hmem₀⟩ := hcov e he
    have huniq : ∀ s, G s → SSMem e s → s = s₀ := fun s hs hmem => by
      by_contra hne
      exact hdisj s s₀ hs hs₀ hne e he ⟨hmem, hmem₀⟩
    have hset : {i : kInterp.Map A | (∃ s, G s ∧ i = kItem a₀ s) ∧ SSElem e ∧ SSMem e (i.2 0)} =
        {kItem a₀ s₀} := by
      ext i
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, -, hmem⟩
        rw [Set.mem_singleton_iff, huniq s hs (by simpa using hmem)]
      · rintro rfl
        exact ⟨⟨s₀, hs₀, rfl⟩, he, by simpa using hmem₀⟩
    rw [hset, Set.ncard_singleton, if_pos he]
  · rintro ⟨-, -, S, hSi, hsum⟩
    rw [sum_weights_eq ha₀ hSi, bwTarget_eq ha₀] at hsum
    have hkey : ∀ e, SSElem e →
        ({i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} : Set _).ncard = 1 := by
      intro e he
      have h := digitNum_inj (Le := (· ≤ · : A → A → Prop)) (B := base A)
        ⟨fun _ => le_rfl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, le_total⟩ base_pos
        ({e : A | SSElem e} : Set A).ncard SSElem rfl _ _
        (fun e' => count_lt_base hSi ha₀ e')
        (fun e' => by by_cases h' : SSElem e' <;> simp [h', base_pos, one_lt_base]) hsum e he
      rw [h, if_pos he]
    refine (exactlyCoversOn_iff_unique _ _ _).mpr
      ⟨fun s => S (kItem a₀ s), fun s hs => ?_, fun e he => ?_⟩
    · simpa [kItem] using ((bwItem_itm _).mp (hSi _ hs)).1
    · obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp (hkey e he)
      have hmem₀ : i₀ ∈ {i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} := by
        rw [hi₀]
        exact rfl
      obtain ⟨hS₀, -, hmem⟩ := hmem₀
      obtain ⟨hi, -⟩ := eq_kItem ha₀ (hSi _ hS₀)
      refine ⟨i₀.2 0, ⟨show S (kItem a₀ (i₀.2 0)) by rw [← hi]; exact hS₀, hmem⟩, fun s hs => ?_⟩
      have hmem' : kItem a₀ s ∈ {i : kInterp.Map A | S i ∧ SSElem e ∧ SSMem e (i.2 0)} :=
        ⟨hs.1, he, by simpa using hs.2⟩
      rw [hi₀, Set.mem_singleton_iff] at hmem'
      exact congrArg (fun q : kInterp.Map A => q.2 0) hmem'

end Correctness

end KnapRed

open KnapRed in
/-- **Exact Cover FO-reduces to Knapsack**, over any linear order on the input:
one item per set, one digit block of `|A|` bits per ground element, weights
carrying a `1` in the block of each of their elements and the target a `1` in
every block. -/
noncomputable def exactCover_ordered_fo_reduction_knapsack : ExactCover ≤ᶠᵒ[≤] Knapsack where
  Tag := KTag
  dim := 2
  toInterpretation := kInterp
  correct A _ _ _ _ := hasExactCover_iff_hasSubsetSum A

end DescriptiveComplexity
