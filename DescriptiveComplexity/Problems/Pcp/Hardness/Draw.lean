/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import DescriptiveComplexity.Problems.Pcp.Hardness.ConfigWord
import DescriptiveComplexity.Problems.Machine.Defs

/-!
# Drawing the domino system of a machine

The elements of the PCP instance the reduction from
`DescriptiveComplexity.HALT` writes, and what its relations are to say about
them – everything semantic, no formula in sight. The sibling `Interp` file
writes first-order formulas realizing exactly the predicates of this file, and
the `Match` file proves that an instance reading this way has a match exactly
when the machine accepts.

## The universe

An element is a tag with a `5`-tuple of source elements
(`DescriptiveComplexity.HaltPcp.PV`); the dimension is set by the move
dominoes, whose rules of `DescriptiveComplexity.HaltPcp.MRule` are indexed by
up to five attribute values. Tags fall into three groups:

* **letters** – the alphabet `DescriptiveComplexity.Pcp.History.Letter` over
  `DescriptiveComplexity.HaltPcp.TapeLetter`, drawn by
  `DescriptiveComplexity.HaltPcp.letterElem`: one constant tag per constant
  letter, and a tag carrying one source element for the symbol and state
  letters;
* **positions** – eight shared constants carrying the short words of every
  domino, the interleaved page block `pairSym p < pairStar p < pairSym p' …`
  carrying the input page of the start domino's bottom word, and four high
  constants closing it;
* **dominoes** – one tag per shape of `DescriptiveComplexity.Pcp.History.Dom`
  at the rules of the machine, the rule dominoes carrying their attribute
  values in the tuple.

## The word tables

Every short word is a **static list of letter specifications**
(`DescriptiveComplexity.HaltPcp.LSpec`): each letter is a constant or is
indexed by one coordinate of the domino. `uSpec`/`vSpec` give the table of
each domino tag, and the letter relations `PUAt`/`PVAt` say exactly “the pair
(position, letter) is an entry of the zipped table” – one uniform definition,
one uniform sortedness argument, one uniform reading lemma, instead of one per
domino. Only the start domino's bottom word – the one word whose length grows
with the instance – has its own relation, `StartBotAt`.

## The order

One uniform lexicographic key orders the whole universe: the static block
index of the tag, then the first coordinate *in the machine's own order* –
which is what interleaves the page block correctly – then the static sub-index
(letter before star inside the page block), then the remaining coordinates in
the ambient order. On a well-formed machine this is a linear order on all of
`PV A`, junk included.
-/

namespace DescriptiveComplexity

namespace HaltPcp

open FirstOrder

open Language Structure

/-! ### The tags -/

/-- The tags of the drawn PCP instance: letters, positions and dominoes. -/
inductive PTag
  /-- The decoration letter. -/
  | ltStar
  /-- The separator letter between configurations. -/
  | ltSep
  /-- The letter opening a history. -/
  | ltTri
  /-- The letter closing a match. -/
  | ltDia
  /-- The left endmarker, as a letter. -/
  | ltLft
  /-- The right endmarker, as a letter. -/
  | ltRgt
  /-- The boot letter. -/
  | ltBoot
  /-- The halting letter. -/
  | ltHalt
  /-- A tape symbol, carrying its element. -/
  | ltSym
  /-- A state, carrying its element. -/
  | ltState
  /-- The eight shared positions of the short words. -/
  | pos0 | pos1 | pos2 | pos3 | pos4 | pos5 | pos6 | pos7
  /-- The page block: the position carrying the input symbol of a source
  position. -/
  | pairSym
  /-- The page block: the decoration position after a source position. -/
  | pairStar
  /-- The four positions closing the start domino's bottom word. -/
  | hi0 | hi1 | hi2 | hi3
  /-- The start domino. -/
  | dStart
  /-- The closing domino. -/
  | dClose
  /-- The domino copying the separator. -/
  | dCopySep
  /-- The dominoes copying the constant letters of the alphabet. -/
  | dCopyLft | dCopyRgt | dCopyBoot | dCopyHalt
  /-- The domino copying a tape symbol, carrying its element. -/
  | dCopySym
  /-- The domino copying a state letter, carrying its element. -/
  | dCopyState
  /-- The boot rule, carrying its start state. -/
  | dBoot
  /-- The halting rule, carrying its accepting state. -/
  | dAcc
  /-- The four move rules, carrying `(q, a, b, q', c)` respectively
  `(q, a, b, q', blank)`. -/
  | dMoveR | dMoveREnd | dMoveL | dMoveLEnd
  /-- The four erasers, the symbol ones carrying their element. -/
  | dEraseSymL | dEraseLft | dEraseSymR | dEraseRgt
  deriving DecidableEq

instance : Nonempty PTag := ⟨.dStart⟩

instance : Fintype PTag :=
  ⟨⟨([.ltStar, .ltSep, .ltTri, .ltDia, .ltLft, .ltRgt, .ltBoot, .ltHalt, .ltSym, .ltState,
    .pos0, .pos1, .pos2, .pos3, .pos4, .pos5, .pos6, .pos7, .pairSym, .pairStar,
    .hi0, .hi1, .hi2, .hi3, .dStart, .dClose, .dCopySep,
    .dCopyLft, .dCopyRgt, .dCopyBoot, .dCopyHalt, .dCopySym, .dCopyState,
    .dBoot, .dAcc, .dMoveR, .dMoveREnd, .dMoveL, .dMoveLEnd,
    .dEraseSymL, .dEraseLft, .dEraseSymR, .dEraseRgt] : List PTag), by decide⟩,
    fun t => by cases t <;> decide⟩

/-- The block index of a tag: the primary key of the order of the universe.
The page block is the only block shared by two tags. -/
def PTag.bIdx : PTag → ℕ
  | .pos0 => 0 | .pos1 => 1 | .pos2 => 2 | .pos3 => 3
  | .pos4 => 4 | .pos5 => 5 | .pos6 => 6 | .pos7 => 7
  | .pairSym => 8 | .pairStar => 8
  | .hi0 => 9 | .hi1 => 10 | .hi2 => 11 | .hi3 => 12
  | .ltStar => 13 | .ltSep => 14 | .ltTri => 15 | .ltDia => 16
  | .ltLft => 17 | .ltRgt => 18 | .ltBoot => 19 | .ltHalt => 20
  | .ltSym => 21 | .ltState => 22
  | .dStart => 23 | .dClose => 24 | .dCopySep => 25
  | .dCopyLft => 26 | .dCopyRgt => 27 | .dCopyBoot => 28 | .dCopyHalt => 29
  | .dCopySym => 30 | .dCopyState => 31
  | .dBoot => 32 | .dAcc => 33
  | .dMoveR => 34 | .dMoveREnd => 35 | .dMoveL => 36 | .dMoveLEnd => 37
  | .dEraseSymL => 38 | .dEraseLft => 39 | .dEraseSymR => 40 | .dEraseRgt => 41

/-- The sub-index inside a block: the input symbol comes before the
decoration that follows it. -/
def PTag.sIdx : PTag → ℕ
  | .pairStar => 1
  | _ => 0

/-- The pair of indices identifies the tag. -/
theorem PTag.bIdx_sIdx_inj : ∀ {t t' : PTag}, t.bIdx = t'.bIdx → t.sIdx = t'.sIdx → t = t' :=
  by decide

/-! ### The universe and its distinguished elements -/

variable {A : Type}

/-- The universe of the drawn instance: a tag and a `5`-tuple of source
elements. -/
abbrev PV (A : Type) : Type := PTag × (Fin 5 → A)

section Elements

variable [LinearOrder A] [Finite A] [Nonempty A]

/-- The least source element, the padding of the unused coordinates. -/
noncomputable def pbot : A := (Finite.exists_min (id : A → A)).choose

theorem pbot_le (a : A) : pbot (A := A) ≤ a :=
  (Finite.exists_min (id : A → A)).choose_spec a

/-- An element is minimal exactly when it is the least element. -/
theorem eq_pbot_iff {a : A} : a = pbot ↔ ∀ b, a ≤ b :=
  ⟨fun h b => h ▸ pbot_le b, fun h => le_antisymm (h pbot) (pbot_le a)⟩

/-- The constant element of a tag. -/
noncomputable def cstE (t : PTag) : PV A := (t, fun _ => pbot)

/-- The element of a tag carrying one source element. -/
noncomputable def idxE (t : PTag) (a : A) : PV A :=
  (t, fun i => if i = 0 then a else pbot)

@[simp] theorem cstE_fst (t : PTag) : (cstE (A := A) t).1 = t := rfl

@[simp] theorem idxE_fst (t : PTag) (a : A) : (idxE t a).1 = t := rfl

@[simp] theorem idxE_snd_zero (t : PTag) (a : A) : (idxE t a).2 0 = a := by
  simp [idxE]

theorem idxE_inj {t : PTag} {a a' : A} (h : idxE t a = idxE t a') : a = a' := by
  have := congrFun (congrArg Prod.snd h) 0
  simpa using this

/-- The image of a letter of the domino alphabet. -/
noncomputable def letterElem : Pcp.History.Letter (TapeLetter A) → PV A
  | .star => cstE .ltStar
  | .sep => cstE .ltSep
  | .tri => cstE .ltTri
  | .dia => cstE .ltDia
  | .sym .lft => cstE .ltLft
  | .sym .rgt => cstE .ltRgt
  | .sym .boot => cstE .ltBoot
  | .sym .halt => cstE .ltHalt
  | .sym (.sym a) => idxE .ltSym a
  | .sym (.state q) => idxE .ltState q

/-- The letter map is injective: distinct letters are distinct elements. -/
theorem letterElem_injective :
    Function.Injective (letterElem (A := A)) := by
  intro x y h
  rcases x with (_ | _ | _ | _ | a | q) | _ | _ | _ | _ <;>
    rcases y with (_ | _ | _ | _ | b | q') | _ | _ | _ | _ <;>
    first
      | rfl
      | (rw [idxE_inj h])
      | (exact absurd (congrArg Prod.fst h) (by simp [letterElem, cstE, idxE]))

end Elements

/-! ### The order of the universe

One lexicographic key: the static block index, the first coordinate in the
machine's order, the static sub-index, the remaining coordinates in the
ambient order. -/

section Order

variable [Language.turing.Structure A] [LinearOrder A]

/-- Strictly below, in the machine's order. -/
def MLt (a b : A) : Prop := TMLe a b ∧ a ≠ b

/-- The ambient lexicographic order on the last four coordinates. -/
def TupLe (w w' : Fin 5 → A) : Prop :=
  w 1 < w' 1 ∨ (w 1 = w' 1 ∧ (w 2 < w' 2 ∨ (w 2 = w' 2 ∧
    (w 3 < w' 3 ∨ (w 3 = w' 3 ∧ w 4 ≤ w' 4)))))

/-- **The order of the drawn instance**: block index, first coordinate in the
machine's order, sub-index, remaining coordinates. On a well-formed machine
this is a linear order on the whole universe. -/
def PLe (x y : PV A) : Prop :=
  x.1.bIdx < y.1.bIdx ∨ (x.1.bIdx = y.1.bIdx ∧
    (MLt (x.2 0) (y.2 0) ∨ (x.2 0 = y.2 0 ∧
      (x.1.sIdx < y.1.sIdx ∨ (x.1.sIdx = y.1.sIdx ∧ TupLe x.2 y.2)))))

/-- The strict part of the order of the drawn instance. -/
def PLt (x y : PV A) : Prop := PLe x y ∧ x ≠ y

omit [Language.turing.Structure A] in
theorem tupLe_refl (w : Fin 5 → A) : TupLe w w := by
  simp [TupLe]

theorem pLe_refl (x : PV A) : PLe x x :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, tupLe_refl x.2⟩⟩⟩

omit [Language.turing.Structure A] in
theorem tupLe_trans {u v w : Fin 5 → A} (h1 : TupLe u v) (h2 : TupLe v w) : TupLe u w := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · refine Or.inr ⟨e1.trans e2, ?_⟩
    rcases h1 with h1 | ⟨f1, h1⟩ <;> rcases h2 with h2 | ⟨f2, h2⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (f2 ▸ h1)
    · exact Or.inl (f1 ▸ h2)
    · refine Or.inr ⟨f1.trans f2, ?_⟩
      rcases h1 with h1 | ⟨g1, h1⟩ <;> rcases h2 with h2 | ⟨g2, h2⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inl (g2 ▸ h1)
      · exact Or.inl (g1 ▸ h2)
      · exact Or.inr ⟨g1.trans g2, h1.trans h2⟩

omit [Language.turing.Structure A] in
theorem tupLe_antisymm {u v : Fin 5 → A} (h1 : TupLe u v) (h2 : TupLe v u) :
    u 1 = v 1 ∧ u 2 = v 2 ∧ u 3 = v 3 ∧ u 4 = v 4 := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (e2 ▸ lt_irrefl _)
  · exact absurd h2 (e1 ▸ lt_irrefl _)
  refine ⟨e1, ?_⟩
  rcases h1 with h1 | ⟨f1, h1⟩ <;> rcases h2 with h2 | ⟨f2, h2⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (f2 ▸ lt_irrefl _)
  · exact absurd h2 (f1 ▸ lt_irrefl _)
  refine ⟨f1, ?_⟩
  rcases h1 with h1 | ⟨g1, h1⟩ <;> rcases h2 with h2 | ⟨g2, h2⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (g2 ▸ lt_irrefl _)
  · exact absurd h2 (g1 ▸ lt_irrefl _)
  exact ⟨g1, le_antisymm h1 h2⟩

omit [Language.turing.Structure A] in
theorem tupLe_total (u v : Fin 5 → A) : TupLe u v ∨ TupLe v u := by
  rcases lt_trichotomy (u 1) (v 1) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (u 2) (v 2) with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
    · rcases lt_trichotomy (u 3) (v 3) with h3 | h3 | h3
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, Or.inl h3⟩⟩)
      · rcases le_total (u 4) (v 4) with h4 | h4
        · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, Or.inr ⟨h3, h4⟩⟩⟩)
        · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, Or.inr ⟨h3.symm, h4⟩⟩⟩)
      · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, Or.inl h3⟩⟩)
    · exact Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩)
  · exact Or.inr (Or.inl h)

variable {M : TMData A}

omit [LinearOrder A] in
theorem mLt_trans (hlin : IsLinOrd (TMLe (A := A))) {a b c : A}
    (h1 : MLt a b) (h2 : MLt b c) : MLt a c := by
  refine ⟨hlin.2.1 _ _ _ h1.1 h2.1, fun hcon => ?_⟩
  exact h1.2 (hlin.2.2.1 _ _ h1.1 (hcon ▸ h2.1))

/-- On a well-formed machine, the order of the drawn instance is transitive. -/
theorem pLe_trans (hlin : IsLinOrd (TMLe (A := A))) {x y z : PV A}
    (h1 : PLe x y) (h2 : PLe y z) : PLe x z := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  refine Or.inr ⟨e1.trans e2, ?_⟩
  rcases h1 with h1 | ⟨f1, h1⟩ <;> rcases h2 with h2 | ⟨f2, h2⟩
  · exact Or.inl (mLt_trans hlin h1 h2)
  · exact Or.inl (f2 ▸ h1)
  · exact Or.inl (f1 ▸ h2)
  refine Or.inr ⟨f1.trans f2, ?_⟩
  rcases h1 with h1 | ⟨g1, h1⟩ <;> rcases h2 with h2 | ⟨g2, h2⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (g2 ▸ h1)
  · exact Or.inl (g1 ▸ h2)
  exact Or.inr ⟨g1.trans g2, tupLe_trans h1 h2⟩

/-- On a well-formed machine, the order of the drawn instance is
antisymmetric. -/
theorem pLe_antisymm (hlin : IsLinOrd (TMLe (A := A))) {x y : PV A}
    (h1 : PLe x y) (h2 : PLe y x) : x = y := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (e2 ▸ lt_irrefl _)
  · exact absurd h2 (e1 ▸ lt_irrefl _)
  have h0 : x.2 0 = y.2 0 := by
    rcases h1 with h1 | ⟨f1, -⟩ <;> rcases h2 with h2 | ⟨f2, -⟩
    · exact absurd (mLt_trans hlin h1 h2).2 (by simp)
    · exact f2.symm
    · exact f1
    · exact f1
  rcases h1 with h1 | ⟨-, h1⟩
  · exact absurd h1.2 (fun hcon => hcon h0)
  rcases h2 with h2 | ⟨-, h2⟩
  · exact absurd h2.2 (fun hcon => hcon h0.symm)
  rcases h1 with h1 | ⟨s1, h1⟩ <;> rcases h2 with h2 | ⟨s2, h2⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (s2 ▸ lt_irrefl _)
  · exact absurd h2 (s1 ▸ lt_irrefl _)
  obtain ⟨e14, e24, e34, e44⟩ := tupLe_antisymm h1 h2
  have htag : x.1 = y.1 := PTag.bIdx_sIdx_inj e1 s1
  refine Prod.ext htag (funext fun i => ?_)
  fin_cases i <;> assumption

/-- On a well-formed machine, the order of the drawn instance is total. -/
theorem pLe_total (hlin : IsLinOrd (TMLe (A := A))) (x y : PV A) :
    PLe x y ∨ PLe y x := by
  rcases Nat.lt_trichotomy x.1.bIdx y.1.bIdx with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases eq_or_ne (x.2 0) (y.2 0) with h0 | h0
    · rcases Nat.lt_trichotomy x.1.sIdx y.1.sIdx with hs | hs | hs
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h0, Or.inl hs⟩⟩)
      · rcases tupLe_total x.2 y.2 with ht | ht
        · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h0, Or.inr ⟨hs, ht⟩⟩⟩)
        · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h0.symm, Or.inr ⟨hs.symm, ht⟩⟩⟩)
      · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h0.symm, Or.inl hs⟩⟩)
    · rcases hlin.2.2.2 (x.2 0) (y.2 0) with hle | hle
      · exact Or.inl (Or.inr ⟨h, Or.inl ⟨hle, h0⟩⟩)
      · exact Or.inr (Or.inr ⟨h.symm, Or.inl ⟨hle, h0.symm⟩⟩)
  · exact Or.inr (Or.inl h)

/-- A block-index gap is a strict comparison, whatever the tuples. -/
theorem pLt_of_bIdx_lt {x y : PV A} (h : x.1.bIdx < y.1.bIdx) : PLt x y :=
  ⟨Or.inl h, fun hcon => absurd (hcon ▸ h) (lt_irrefl _)⟩

end Order

/-! ### The word tables -/

/-- A letter of a short word: a constant, or a letter carrying one coordinate
of its domino. -/
inductive LSpec
  /-- A constant letter. -/
  | cst : PTag → LSpec
  /-- A letter carrying the given coordinate of the domino. -/
  | idx : PTag → Fin 5 → LSpec

section Tables

variable [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The letter an entry of the table stands for, at a domino's tuple. -/
noncomputable def LSpec.eval (w : Fin 5 → A) : LSpec → PV A
  | .cst s => cstE s
  | .idx s j => idxE s (w j)

/-- The eight shared positions of the short words. -/
noncomputable def posE : ℕ → PV A
  | 0 => cstE .pos0
  | 1 => cstE .pos1
  | 2 => cstE .pos2
  | 3 => cstE .pos3
  | 4 => cstE .pos4
  | 5 => cstE .pos5
  | 6 => cstE .pos6
  | _ => cstE .pos7

/-- The first `n` of the shared positions, in order. -/
noncomputable def posPrefix (n : ℕ) : List (PV A) := (List.range n).map posE

/-- **The top words**, as tables: the decorated left-hand sides of the rules,
and the tops of the bookkeeping dominoes. -/
def uSpec : PTag → List LSpec
  | .dStart => [.cst .ltStar, .cst .ltTri]
  | .dClose => [.cst .ltStar, .cst .ltHalt, .cst .ltStar, .cst .ltSep,
      .cst .ltStar, .cst .ltDia]
  | .dCopySep => [.cst .ltStar, .cst .ltSep]
  | .dCopyLft => [.cst .ltStar, .cst .ltLft]
  | .dCopyRgt => [.cst .ltStar, .cst .ltRgt]
  | .dCopyBoot => [.cst .ltStar, .cst .ltBoot]
  | .dCopyHalt => [.cst .ltStar, .cst .ltHalt]
  | .dCopySym => [.cst .ltStar, .idx .ltSym 0]
  | .dCopyState => [.cst .ltStar, .idx .ltState 0]
  | .dBoot => [.cst .ltStar, .cst .ltBoot]
  | .dAcc => [.cst .ltStar, .idx .ltState 0]
  | .dMoveR => [.cst .ltStar, .idx .ltState 0, .cst .ltStar, .idx .ltSym 1,
      .cst .ltStar, .idx .ltSym 4]
  | .dMoveREnd => [.cst .ltStar, .idx .ltState 0, .cst .ltStar, .idx .ltSym 1,
      .cst .ltStar, .cst .ltRgt]
  | .dMoveL => [.cst .ltStar, .idx .ltSym 4, .cst .ltStar, .idx .ltState 0,
      .cst .ltStar, .idx .ltSym 1]
  | .dMoveLEnd => [.cst .ltStar, .cst .ltLft, .cst .ltStar, .idx .ltState 0,
      .cst .ltStar, .idx .ltSym 1]
  | .dEraseSymL => [.cst .ltStar, .idx .ltSym 0, .cst .ltStar, .cst .ltHalt]
  | .dEraseLft => [.cst .ltStar, .cst .ltLft, .cst .ltStar, .cst .ltHalt]
  | .dEraseSymR => [.cst .ltStar, .cst .ltHalt, .cst .ltStar, .idx .ltSym 0]
  | .dEraseRgt => [.cst .ltStar, .cst .ltHalt, .cst .ltStar, .cst .ltRgt]
  | _ => []

/-- **The bottom words**, as tables – all but the start domino's, which has
its own layout. -/
def vSpec : PTag → List LSpec
  | .dClose => [.cst .ltDia]
  | .dCopySep => [.cst .ltSep, .cst .ltStar]
  | .dCopyLft => [.cst .ltLft, .cst .ltStar]
  | .dCopyRgt => [.cst .ltRgt, .cst .ltStar]
  | .dCopyBoot => [.cst .ltBoot, .cst .ltStar]
  | .dCopyHalt => [.cst .ltHalt, .cst .ltStar]
  | .dCopySym => [.idx .ltSym 0, .cst .ltStar]
  | .dCopyState => [.idx .ltState 0, .cst .ltStar]
  | .dBoot => [.idx .ltState 0, .cst .ltStar]
  | .dAcc => [.cst .ltHalt, .cst .ltStar]
  | .dMoveR => [.idx .ltSym 2, .cst .ltStar, .idx .ltState 3, .cst .ltStar,
      .idx .ltSym 4, .cst .ltStar]
  | .dMoveREnd => [.idx .ltSym 2, .cst .ltStar, .idx .ltState 3, .cst .ltStar,
      .idx .ltSym 4, .cst .ltStar, .cst .ltRgt, .cst .ltStar]
  | .dMoveL => [.idx .ltState 3, .cst .ltStar, .idx .ltSym 4, .cst .ltStar,
      .idx .ltSym 2, .cst .ltStar]
  | .dMoveLEnd => [.cst .ltLft, .cst .ltStar, .idx .ltState 3, .cst .ltStar,
      .idx .ltSym 4, .cst .ltStar, .idx .ltSym 2, .cst .ltStar]
  | .dEraseSymL => [.cst .ltHalt, .cst .ltStar]
  | .dEraseLft => [.cst .ltHalt, .cst .ltStar]
  | .dEraseSymR => [.cst .ltHalt, .cst .ltStar]
  | .dEraseRgt => [.cst .ltHalt, .cst .ltStar]
  | _ => []

/-- The top word of a domino element. -/
noncomputable def uWord (x : PV A) : List (PV A) := (uSpec x.1).map (LSpec.eval x.2)

/-- The bottom word of a domino element other than the start domino. -/
noncomputable def vWord (x : PV A) : List (PV A) := (vSpec x.1).map (LSpec.eval x.2)

/-- **The top letter relation**: the pair is an entry of the zipped table. -/
def PUAt (d p c : PV A) : Prop :=
  (p, c) ∈ (posPrefix (uSpec d.1).length).zip (uWord d)

/-- **The bottom word of the start domino**: seven low constants, the
interleaved page block carrying the input, four high constants. -/
def StartBotAt (p c : PV A) : Prop :=
  match p.1 with
  | .pos0 => p = cstE .pos0 ∧ c = cstE .ltStar
  | .pos1 => p = cstE .pos1 ∧ c = cstE .ltTri
  | .pos2 => p = cstE .pos2 ∧ c = cstE .ltStar
  | .pos3 => p = cstE .pos3 ∧ c = cstE .ltLft
  | .pos4 => p = cstE .pos4 ∧ c = cstE .ltStar
  | .pos5 => p = cstE .pos5 ∧ c = cstE .ltBoot
  | .pos6 => p = cstE .pos6 ∧ c = cstE .ltStar
  | .pairSym => TMPosn (p.2 0) ∧ p = idxE .pairSym (p.2 0) ∧
      ∃ a, (tmData A).InitTape (p.2 0) a ∧ c = idxE .ltSym a
  | .pairStar => TMPosn (p.2 0) ∧ p = idxE .pairStar (p.2 0) ∧ c = cstE .ltStar
  | .hi0 => p = cstE .hi0 ∧ c = cstE .ltRgt
  | .hi1 => p = cstE .hi1 ∧ c = cstE .ltStar
  | .hi2 => p = cstE .hi2 ∧ c = cstE .ltSep
  | .hi3 => p = cstE .hi3 ∧ c = cstE .ltStar
  | _ => False

/-- **The bottom letter relation**: the start domino reads its own layout,
every other domino its table. -/
def PVAt (d p c : PV A) : Prop :=
  match d.1 with
  | .dStart => StartBotAt p c
  | _ => (p, c) ∈ (posPrefix (vSpec d.1).length).zip (vWord d)

/-! ### The dominoes -/

/-- The side condition a domino tag places on its tuple: the promises of the
rule it stands for. -/
def DomGuard (x : PV A) : Prop :=
  match x.1 with
  | .dStart | .dClose | .dCopySep => True
  | .dCopyLft | .dCopyRgt | .dCopyBoot | .dCopyHalt => True
  | .dCopySym | .dCopyState => True
  | .dBoot => TMStart (x.2 0)
  | .dAcc => TMAcc (x.2 0)
  | .dMoveR => ∃ τ, TMTr τ ∧ TMRight τ ∧ TMSrc τ (x.2 0) ∧ TMRead τ (x.2 1) ∧
      TMDst τ (x.2 3) ∧ TMWrite τ (x.2 2)
  | .dMoveREnd => (∃ τ, TMTr τ ∧ TMRight τ ∧ TMSrc τ (x.2 0) ∧ TMRead τ (x.2 1) ∧
      TMDst τ (x.2 3) ∧ TMWrite τ (x.2 2)) ∧ TMBlank (x.2 4)
  | .dMoveL => ∃ τ, TMTr τ ∧ ¬TMRight τ ∧ TMSrc τ (x.2 0) ∧ TMRead τ (x.2 1) ∧
      TMDst τ (x.2 3) ∧ TMWrite τ (x.2 2)
  | .dMoveLEnd => (∃ τ, TMTr τ ∧ ¬TMRight τ ∧ TMSrc τ (x.2 0) ∧ TMRead τ (x.2 1) ∧
      TMDst τ (x.2 3) ∧ TMWrite τ (x.2 2)) ∧ TMBlank (x.2 4)
  | .dEraseSymL | .dEraseLft | .dEraseSymR | .dEraseRgt => True
  | _ => False

/-- **Being a domino of the drawn instance**: the machine is well-formed and
the tag's side condition holds. -/
def PDom (x : PV A) : Prop :=
  (tmData A).WellFormed ∧ DomGuard x

/-- The abstract domino an element stands for. -/
def decodeDom (x : PV A) : Pcp.History.Dom (TapeLetter A) :=
  match x.1 with
  | .dStart => .start
  | .dClose => .close
  | .dCopySep => .copySep
  | .dCopyLft => .copy .lft
  | .dCopyRgt => .copy .rgt
  | .dCopyBoot => .copy .boot
  | .dCopyHalt => .copy .halt
  | .dCopySym => .copy (.sym (x.2 0))
  | .dCopyState => .copy (.state (x.2 0))
  | .dBoot => .rule [.boot] [.state (x.2 0)]
  | .dAcc => .rule [.state (x.2 0)] [.halt]
  | .dMoveR => .rule [.state (x.2 0), .sym (x.2 1), .sym (x.2 4)]
      [.sym (x.2 2), .state (x.2 3), .sym (x.2 4)]
  | .dMoveREnd => .rule [.state (x.2 0), .sym (x.2 1), .rgt]
      [.sym (x.2 2), .state (x.2 3), .sym (x.2 4), .rgt]
  | .dMoveL => .rule [.sym (x.2 4), .state (x.2 0), .sym (x.2 1)]
      [.state (x.2 3), .sym (x.2 4), .sym (x.2 2)]
  | .dMoveLEnd => .rule [.lft, .state (x.2 0), .sym (x.2 1)]
      [.lft, .state (x.2 3), .sym (x.2 4), .sym (x.2 2)]
  | .dEraseSymL => .rule [.sym (x.2 0), .halt] [.halt]
  | .dEraseLft => .rule [.lft, .halt] [.halt]
  | .dEraseSymR => .rule [.halt, .sym (x.2 0)] [.halt]
  | .dEraseRgt => .rule [.halt, .rgt] [.halt]
  | _ => .start

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- **A domino element stands for a legitimate domino** of the machine's
system. -/
theorem ok_decodeDom {x : PV A} (hx : PDom x) :
    Pcp.History.Ok (MRule (tmData A)) (decodeDom x) := by
  obtain ⟨t, w⟩ := x
  obtain ⟨-, hg⟩ := hx
  cases t <;> first
    | exact hg.elim
    | trivial
    | skip
  case dBoot => exact ⟨MRule.boot hg, by simp, by simp⟩
  case dAcc => exact ⟨MRule.acc hg, by simp, by simp⟩
  case dMoveR =>
    obtain ⟨τ, hτ, hR, hsrc, hread, hdst, hwr⟩ := hg
    exact ⟨MRule.moveR hτ hR hsrc hread hdst hwr, by simp, by simp⟩
  case dMoveREnd =>
    obtain ⟨⟨τ, hτ, hR, hsrc, hread, hdst, hwr⟩, hbk⟩ := hg
    exact ⟨MRule.moveREnd hτ hR hsrc hread hdst hwr hbk, by simp, by simp⟩
  case dMoveL =>
    obtain ⟨τ, hτ, hR, hsrc, hread, hdst, hwr⟩ := hg
    exact ⟨MRule.moveL hτ hR hsrc hread hdst hwr, by simp, by simp⟩
  case dMoveLEnd =>
    obtain ⟨⟨τ, hτ, hR, hsrc, hread, hdst, hwr⟩, hbk⟩ := hg
    exact ⟨MRule.moveLEnd hτ hR hsrc hread hdst hwr hbk, by simp, by simp⟩
  case dEraseSymL => exact ⟨MRule.eraseSymL _, by simp, by simp⟩
  case dEraseLft => exact ⟨MRule.eraseLft, by simp, by simp⟩
  case dEraseSymR => exact ⟨MRule.eraseSymR _, by simp, by simp⟩
  case dEraseRgt => exact ⟨MRule.eraseRgt, by simp, by simp⟩

/-- The top table of a domino element is the decorated top word of the domino
it stands for. -/
theorem uWord_eq {x : PV A} (hx : PDom x) :
    uWord x = (Pcp.History.topW TapeLetter.halt (decodeDom x)).map letterElem := by
  obtain ⟨t, w⟩ := x
  cases t <;> first
    | exact hx.2.elim
    | rfl

/-- The bottom table of a domino element other than the start domino is the
decorated bottom word of the domino it stands for; the start word of the
system is irrelevant to those. -/
theorem vWord_eq {x : PV A} (hx : PDom x) (hne : x.1 ≠ .dStart) (C₀ : List (TapeLetter A)) :
    vWord x = (Pcp.History.botW C₀ (decodeDom x)).map letterElem := by
  obtain ⟨t, w⟩ := x
  cases t <;> first
    | exact hx.2.elim
    | exact absurd rfl hne
    | rfl

/-- **Every legitimate domino is drawn**: an element with the right guard
stands for it. -/
theorem exists_encode (hwf : (tmData A).WellFormed) {d : Pcp.History.Dom (TapeLetter A)}
    (hok : Pcp.History.Ok (MRule (tmData A)) d) :
    ∃ x : PV A, PDom x ∧ decodeDom x = d := by
  cases d with
  | start => exact ⟨cstE .dStart, ⟨hwf, trivial⟩, rfl⟩
  | close => exact ⟨cstE .dClose, ⟨hwf, trivial⟩, rfl⟩
  | copySep => exact ⟨cstE .dCopySep, ⟨hwf, trivial⟩, rfl⟩
  | copy γ =>
    cases γ with
    | lft => exact ⟨cstE .dCopyLft, ⟨hwf, trivial⟩, rfl⟩
    | rgt => exact ⟨cstE .dCopyRgt, ⟨hwf, trivial⟩, rfl⟩
    | boot => exact ⟨cstE .dCopyBoot, ⟨hwf, trivial⟩, rfl⟩
    | halt => exact ⟨cstE .dCopyHalt, ⟨hwf, trivial⟩, rfl⟩
    | sym a => exact ⟨idxE .dCopySym a, ⟨hwf, trivial⟩, rfl⟩
    | state q => exact ⟨idxE .dCopyState q, ⟨hwf, trivial⟩, rfl⟩
  | rule l r =>
    obtain ⟨hrule, -, -⟩ := hok
    cases hrule with
    | @boot q hq =>
      exact ⟨idxE .dBoot q, ⟨hwf, hq⟩, rfl⟩
    | @acc q hq =>
      exact ⟨idxE .dAcc q, ⟨hwf, hq⟩, rfl⟩
    | @moveR τ q a b q' c hτ hR hs hr hd hw =>
      exact ⟨(.dMoveR, ![q, a, b, q', c]), ⟨hwf, τ, hτ, hR, hs, hr, hd, hw⟩, rfl⟩
    | @moveREnd τ q a b q' bk hτ hR hs hr hd hw hbk =>
      exact ⟨(.dMoveREnd, ![q, a, b, q', bk]), ⟨hwf, ⟨τ, hτ, hR, hs, hr, hd, hw⟩, hbk⟩, rfl⟩
    | @moveL τ q a b q' c hτ hR hs hr hd hw =>
      exact ⟨(.dMoveL, ![q, a, b, q', c]), ⟨hwf, τ, hτ, hR, hs, hr, hd, hw⟩, rfl⟩
    | @moveLEnd τ q a b q' bk hτ hR hs hr hd hw hbk =>
      exact ⟨(.dMoveLEnd, ![q, a, b, q', bk]), ⟨hwf, ⟨τ, hτ, hR, hs, hr, hd, hw⟩, hbk⟩, rfl⟩
    | eraseSymL c =>
      exact ⟨idxE .dEraseSymL c, ⟨hwf, trivial⟩, rfl⟩
    | eraseLft => exact ⟨cstE .dEraseLft, ⟨hwf, trivial⟩, rfl⟩
    | eraseSymR c =>
      exact ⟨idxE .dEraseSymR c, ⟨hwf, trivial⟩, rfl⟩
    | eraseRgt => exact ⟨cstE .dEraseRgt, ⟨hwf, trivial⟩, rfl⟩

/-! ### The positions, in order -/

omit [Language.turing.Structure A] in
/-- The block index of a shared position is its number. -/
theorem posE_bIdx : ∀ {i : ℕ}, i < 8 → (posE (A := A) i).1.bIdx = i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

/-- The shared positions are strictly increasing. -/
theorem pairwise_posPrefix {n : ℕ} (hn : n ≤ 8) :
    (posPrefix (A := A) n).Pairwise PLt := by
  rw [posPrefix, List.pairwise_map]
  refine (List.pairwise_lt_range).imp_of_mem ?_
  intro i j hi hj hij
  have hi8 : i < 8 := lt_of_lt_of_le (List.mem_range.mp hi) hn
  have hj8 : j < 8 := lt_of_lt_of_le (List.mem_range.mp hj) hn
  exact pLt_of_bIdx_lt (by rw [posE_bIdx hi8, posE_bIdx hj8]; exact hij)

/-- The page block of the start domino's bottom word: the input position and
its decoration, per source position. -/
noncomputable def pagePos (ps : List A) : List (PV A) :=
  ps.flatMap fun p => [idxE .pairSym p, idxE .pairStar p]

/-- The positions of the start domino's bottom word. -/
noncomputable def startPos (ps : List A) : List (PV A) :=
  posPrefix 7 ++ pagePos ps ++ [cstE .hi0, cstE .hi1, cstE .hi2, cstE .hi3]

/-- The letters of the page block: the input symbol and the decoration. -/
noncomputable def pageBot (inp : List A) : List (PV A) :=
  inp.flatMap fun a => [idxE .ltSym a, cstE .ltStar]

/-- The letters of the start domino's bottom word. -/
noncomputable def startBot (inp : List A) : List (PV A) :=
  [cstE .ltStar, cstE .ltTri, cstE .ltStar, cstE .ltLft, cstE .ltStar, cstE .ltBoot,
    cstE .ltStar] ++ pageBot inp ++
    [cstE .ltRgt, cstE .ltStar, cstE .ltSep, cstE .ltStar]

omit [Language.turing.Structure A] in
@[simp] theorem length_pagePos (ps : List A) : (pagePos ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [pagePos, List.flatMap_cons, ← pagePos, List.length_append, ih]
    simp
    omega

omit [Language.turing.Structure A] in
@[simp] theorem length_pageBot (inp : List A) : (pageBot inp).length = 2 * inp.length := by
  induction inp with
  | nil => rfl
  | cons a inp ih =>
    rw [pageBot, List.flatMap_cons, ← pageBot, List.length_append, ih]
    simp
    omega

omit [Language.turing.Structure A] in
/-- Members of the page block are page positions over members of the list. -/
theorem mem_pagePos {ps : List A} {x : PV A} :
    x ∈ pagePos ps ↔ ∃ p ∈ ps, x = idxE .pairSym p ∨ x = idxE .pairStar p := by
  rw [pagePos, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hx⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨p, hp, Or.inl rfl⟩
    · obtain rfl : x = idxE .pairStar p := by simpa using hx
      exact ⟨p, hp, Or.inr rfl⟩
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact ⟨p, hp, by simp⟩
    · exact ⟨p, hp, by simp⟩

/-- The page block is strictly increasing along a sorted list of positions. -/
theorem pairwise_pagePos {ps : List A}
    (hps : ps.Pairwise fun p q => TMLe p q ∧ p ≠ q) :
    (pagePos ps).Pairwise PLt := by
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons p ps ih =>
    rw [List.pairwise_cons] at hps
    rw [pagePos, List.flatMap_cons, ← pagePos]
    rw [List.pairwise_append]
    have hcross : ∀ x ∈ [idxE (A := A) .pairSym p, idxE .pairStar p],
        ∀ y ∈ pagePos ps, PLt x y := by
      intro x hx y hy
      obtain ⟨q, hq, hy⟩ := mem_pagePos.mp hy
      have hpq : TMLe p q ∧ p ≠ q := hps.1 q hq
      have hple : ∀ t t' : PTag, t.bIdx = 8 → t'.bIdx = 8 →
          PLt (A := A) (idxE t p) (idxE t' q) := by
        intro t t' ht ht'
        refine ⟨Or.inr ⟨ht.trans ht'.symm, Or.inl ?_⟩, ?_⟩
        · exact ⟨by simpa [idxE] using hpq.1, by simpa [idxE] using hpq.2⟩
        · intro hcon
          exact hpq.2 (by simpa [idxE] using congrFun (congrArg Prod.snd hcon) 0)
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hy with rfl | rfl
        · exact hple _ _ rfl rfl
        · exact hple _ _ rfl rfl
      · obtain rfl : x = idxE .pairStar p := by simpa using hx
        rcases hy with rfl | rfl
        · exact hple _ _ rfl rfl
        · exact hple _ _ rfl rfl
    refine ⟨?_, ih hps.2, hcross⟩
    refine List.pairwise_pair.mpr ?_
    refine ⟨Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl (by simp [PTag.sIdx])⟩⟩, ?_⟩
    intro hcon
    exact absurd (congrArg Prod.fst hcon) (by simp [idxE])

/-- The whole position list of the start domino's bottom word is strictly
increasing. -/
theorem pairwise_startPos {ps : List A}
    (hps : ps.Pairwise fun p q => TMLe p q ∧ p ≠ q) :
    (startPos ps).Pairwise PLt := by
  have hbounds : ∀ x ∈ pagePos (A := A) ps, x.1.bIdx = 8 := by
    intro x hx
    obtain ⟨p, -, rfl | rfl⟩ := mem_pagePos.mp hx <;> rfl
  rw [startPos, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨pairwise_posPrefix (by omega), pairwise_pagePos hps, ?_⟩
    intro x hx y hy
    rw [posPrefix, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi7 : i < 7 := List.mem_range.mp hi
    refine pLt_of_bIdx_lt ?_
    rw [posE_bIdx (by omega), hbounds y hy]
    omega
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
      List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl <;>
        exact pLt_of_bIdx_lt (by simp only [cstE_fst]; decide)
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;>
        exact pLt_of_bIdx_lt (by simp only [cstE_fst]; decide)
    · intro y hy
      obtain rfl : y = cstE .hi3 := by simpa using hy
      exact pLt_of_bIdx_lt (by simp only [cstE_fst]; decide)
  · intro x hx y hy
    have hx13 : x.1.bIdx ≤ 8 := by
      rcases List.mem_append.mp hx with hx | hx
      · rw [posPrefix, List.mem_map] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have : i < 7 := List.mem_range.mp hi
        rw [posE_bIdx (by omega)]
        omega
      · rw [hbounds x hx]
    have hy9 : 9 ≤ y.1.bIdx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> (simp only [cstE_fst]; decide)
    exact pLt_of_bIdx_lt (by omega)

omit [Language.turing.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
/-- The decorated page, letter by letter. -/
theorem starR_page (l : List A) :
    Pcp.History.starR (Pcp.History.symW (l.map TapeLetter.sym)) =
      l.flatMap fun a =>
        [Pcp.History.Letter.sym (TapeLetter.sym a), Pcp.History.Letter.star] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

omit [Language.turing.Structure A] in
/-- The drawn page, letter by letter. -/
theorem map_letterElem_page (l : List A) :
    (l.flatMap fun a =>
      [Pcp.History.Letter.sym (TapeLetter.sym a), Pcp.History.Letter.star]).map
        (letterElem (A := A)) = pageBot l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [pageBot, List.flatMap_cons, List.flatMap_cons, List.map_append, ih, pageBot]
    rfl

omit [Language.turing.Structure A] in
/-- **The letters of the start domino's bottom word** are the drawn bottom
word of the abstract start domino. -/
theorem startBot_eq (inp : List A) :
    startBot inp =
      (Pcp.History.botW (startWord inp) Pcp.History.Dom.start).map
        (letterElem (A := A)) := by
  change startBot inp = (Pcp.History.Letter.star ::
    Pcp.History.starR (Pcp.History.Letter.tri ::
      (Pcp.History.symW (startWord inp) ++ [Pcp.History.Letter.sep]))).map letterElem
  rw [startWord]
  simp only [Pcp.History.symW_cons, Pcp.History.symW_append, Pcp.History.starR_cons,
    Pcp.History.starR_append, starR_page]
  rw [startBot]
  simp only [List.map_cons, List.map_append, map_letterElem_page]
  simp [letterElem]

omit [Language.turing.Structure A] in
/-- The two sides of the start domino's bottom word have the same length. -/
theorem length_startPos {ps inp : List A} (h : ps.length = inp.length) :
    (startPos (A := A) ps).length = (startBot (A := A) inp).length := by
  simp only [startPos, startBot, posPrefix, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil, length_pagePos, length_pageBot, h]

end Tables

end HaltPcp

end DescriptiveComplexity
