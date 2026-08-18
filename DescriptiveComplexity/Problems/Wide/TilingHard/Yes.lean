/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Run
import DescriptiveComplexity.Problems.Machine.Program

/-!
# An accepting run tiles the emitted square

The forward half of the hardness: the table of
`DescriptiveComplexity.TilingHard.tileAt` is a tiling of the square the
reduction emits. Each of the five conditions is one fact about the run –

* every cell carries a tile, because a head tile carries the transition the step
  fires and the machine's own promises say it applies;
* some cell carries an accepting tile, at the row of the accepting
  configuration;
* the bottom row is the initial tape, with the head at the corner;
* horizontal neighbours agree, because the head is unique and an arrival stands
  next to it;
* vertical neighbours agree, because a step writes under the head and leaves
  every other cell alone.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

section Yes

variable {A : Type} [Nonempty A] [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable {g : ℕ → Config (WPoint A)} {tr : ℕ → WPoint A} {n : ℕ}

/-- **The address a coordinate of the emitted grid is.** -/
def addrOf : WPoint (TilePt A) → (A → Prop)
  | Sum.inl u => fun a => u (tpDig a)
  | Sum.inr _ => fun _ => False

omit [Nonempty A] [LinearOrder A] [Finite A] [Language.wide.Structure A] in
@[simp]
theorem addrOf_tpCol (s : A → Prop) : addrOf (Sum.inl (tpCol s)) = s :=
  funext fun a => propext (tpCol_dig s a)

/-- **The table a run draws**: the row of rank `k` is the configuration at time
`k`, and its cell at a column is the tile that configuration puts there. -/
noncomputable def tableTiling (g : ℕ → Config (WPoint A)) (tr : ℕ → WPoint A) (n : ℕ) :
    WPoint (TilePt A) → WPoint (TilePt A) → WPoint (TilePt A) :=
  fun col row => Sum.inr (tileAt g tr n (wideRank (addrOf row)) (Sum.inl (addrOf col)))

/-! ### Every cell carries a tile -/

omit [Finite A] in
/-- **A head tile carries a transition the machine may fire**, which is all
`DescriptiveComplexity.TPTile` asks of it; every other kind of tile asks
nothing. -/
theorem tpTile_tileAt (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    (k : ℕ) (cell : WPoint A) : TPTile (tileAt g tr n k cell) := by
  by_cases hh : (g k).head = cell
  · by_cases hk : k < n
    · obtain ⟨htr, hsrc, hread, -, -, -, -⟩ := hstep k hk
      rw [tileAt_head hh hk]
      refine ⟨wpMark_elt htr, wpAttr_elt hsrc, ?_⟩
      have := wpAttr_elt hread
      rwa [hh] at this
    · rw [tileAt_halt hh hk]
      trivial
  · by_cases hnext : k < n ∧ (g (k + 1)).head = cell
    · rw [tileAt_arr hh hnext.1 hnext.2]
      by_cases hr : WMRight (wpElt (tr k))
      · simp only [if_pos hr]
        trivial
      · simp only [if_neg hr]
        trivial
    · rw [tileAt_sym hh hnext]
      trivial

/-! ### Some cell carries an accepting tile -/

omit [LinearOrder A] [Finite A] in
/-- **The accepting configuration's head cell carries an accepting tile**: the
run has stopped there, so the tile is the halt, and it carries the accepting
state. -/
theorem tpAcc_tileAt (hacc : (wideRegData A).Acc (g n).state) :
    TPAcc (tileAt g tr n n ((g n).head)) := by
  rw [tileAt_halt rfl (lt_irrefl n)]
  exact ⟨Or.inr rfl, wpMark_elt hacc⟩


/-! ### One row becomes the next -/

omit [LinearOrder A] [Finite A] in
/-- A cell the head is not on carries no head. -/
theorem tpNoHead_tileAt {k : ℕ} {cell : WPoint A} (hh : (g k).head ≠ cell) :
    TPNoHead (tileAt g tr n k cell) := by
  by_cases hnext : k < n ∧ (g (k + 1)).head = cell
  · rw [tileAt_arr hh hnext.1 hnext.2]
    by_cases hr : WMRight (wpElt (tr k))
    · simp only [if_pos hr]
      exact Or.inr (Or.inl rfl)
    · simp only [if_neg hr]
      exact Or.inr (Or.inr rfl)
  · rw [tileAt_sym hh hnext]
    exact Or.inl rfl

omit [Nonempty A] [LinearOrder A] [Finite A] [Language.wide.Structure A] in
/-- **After the last step the run stands still.** -/
theorem eq_of_not_lt {k : ℕ} (hfreeze : ∀ i, n ≤ i → g i = g n) (hk : ¬k < n) :
    g (k + 1) = g k := by
  rw [hfreeze (k + 1) (by omega), hfreeze k (by omega)]

omit [Nonempty A] [LinearOrder A] [Finite A] in
/-- **A step moves the head**, so the cell it leaves is not the cell it
enters. -/
theorem head_ne_next {k : ℕ}
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i)) (hk : k < n) :
    (g k).head ≠ (g (k + 1)).head := by
  obtain ⟨-, -, -, -, -, -, hmove⟩ := hstep k hk
  rcases hmove with ⟨-, hs⟩ | ⟨-, hs⟩
  · exact hs.2.2.2.1
  · exact fun hc => hs.2.2.2.1 hc.symm

omit [Nonempty A] [LinearOrder A] [Finite A] in
/-- **A step writes under the head and leaves every other cell alone.** -/
theorem tape_frame {k : ℕ} {cell : WPoint A}
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    (hfreeze : ∀ i, n ≤ i → g i = g n) (hh : (g k).head ≠ cell) :
    (g (k + 1)).tape cell = (g k).tape cell := by
  by_cases hk : k < n
  · obtain ⟨-, -, -, -, -, hframe, -⟩ := hstep k hk
    exact hframe cell fun hc => hh hc.symm
  · rw [eq_of_not_lt hfreeze hk]

omit [LinearOrder A] [Finite A] in
/-- **The row above is the step's**: the head's cell holds what the step wrote,
the cell the head is entering becomes the head, and every other cell copies
itself. -/
theorem tpVert_tileAt
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    (hfreeze : ∀ i, n ≤ i → g i = g n) (k : ℕ) (cell : WPoint A) :
    TPVert (tileAt g tr n k cell) (tileAt g tr n (k + 1) cell) := by
  by_cases hh : (g k).head = cell
  · by_cases hk : k < n
    · -- the head is here and steps away
      obtain ⟨-, -, -, -, hwrite, -, -⟩ := hstep k hk
      have hne : (g (k + 1)).head ≠ cell := fun hc =>
        head_ne_next hstep hk (hh.trans hc.symm)
      rw [tileAt_head hh hk]
      refine ⟨tpNoHead_tileAt hne, ?_⟩
      have hw := wpAttr_elt hwrite
      rw [hh] at hw
      rw [show tpSym (tileAt g tr n (k + 1) cell) = wpElt ((g (k + 1)).tape cell) from
        tpSym_tileAt]
      exact hw
    · -- the run has stopped: the row repeats
      have hgk : g (k + 1) = g k := eq_of_not_lt hfreeze hk
      have hh' : (g (k + 1)).head = cell := by rw [hgk]; exact hh
      have hk' : ¬k + 1 < n := by omega
      rw [tileAt_halt hh hk, tileAt_halt hh' hk']
      refine ⟨rfl, ?_, ?_⟩ <;> rw [hgk]
  · by_cases hnext : k < n ∧ (g (k + 1)).head = cell
    · -- the head arrives here
      have hsame : (g (k + 1)).tape cell = (g k).tape cell := tape_frame hstep hfreeze hh
      rw [tileAt_arr hh hnext.1 hnext.2]
      by_cases hk' : k + 1 < n
      · rw [tileAt_head hnext.2 hk']
        by_cases hr : WMRight (wpElt (tr k))
        · simp only [if_pos hr]
          exact ⟨Or.inl rfl, by rw [hsame]; rfl, rfl⟩
        · simp only [if_neg hr]
          exact ⟨Or.inl rfl, by rw [hsame]; rfl, rfl⟩
      · rw [tileAt_halt hnext.2 hk']
        by_cases hr : WMRight (wpElt (tr k))
        · simp only [if_pos hr]
          exact ⟨Or.inr rfl, by rw [hsame]; rfl, rfl⟩
        · simp only [if_neg hr]
          exact ⟨Or.inr rfl, by rw [hsame]; rfl, rfl⟩
    · -- nothing happens here
      have hne : (g (k + 1)).head ≠ cell := by
        by_cases hk : k < n
        · exact fun hc => hnext ⟨hk, hc⟩
        · rw [eq_of_not_lt hfreeze hk]
          exact hh
      have hsame : (g (k + 1)).tape cell = (g k).tape cell := tape_frame hstep hfreeze hh
      rw [tileAt_sym hh hnext]
      refine ⟨tpNoHead_tileAt hne, ?_⟩
      rw [show tpSym (tileAt g tr n (k + 1) cell) = wpElt ((g (k + 1)).tape cell) from
        tpSym_tileAt, hsame]
      rfl

/-! ### Neighbours in one row -/

omit [LinearOrder A] [Finite A] in
/-- **A head or a halt tile stands where the head stands.** -/
theorem head_eq_of_tileAt {k : ℕ} {cell : WPoint A}
    (h : (tileAt g tr n k cell).1 = TileTag.head ∨ (tileAt g tr n k cell).1 = TileTag.halt) :
    (g k).head = cell := by
  by_cases hh : (g k).head = cell
  · exact hh
  · by_cases hnext : k < n ∧ (g (k + 1)).head = cell
    · rw [tileAt_arr hh hnext.1 hnext.2] at h
      by_cases hr : WMRight (wpElt (tr k))
      · rw [if_pos hr] at h
        rcases h with h | h <;> exact TileTag.noConfusion h
      · rw [if_neg hr] at h
        rcases h with h | h <;> exact TileTag.noConfusion h
    · rw [tileAt_sym hh hnext] at h
      rcases h with h | h <;> exact TileTag.noConfusion h

omit [LinearOrder A] [Finite A] in
/-- **A head tile is the head, with a step left to take.** -/
theorem head_of_tileAt {k : ℕ} {cell : WPoint A}
    (h : (tileAt g tr n k cell).1 = TileTag.head) : (g k).head = cell ∧ k < n := by
  have hh : (g k).head = cell := head_eq_of_tileAt (Or.inl h)
  refine ⟨hh, ?_⟩
  by_contra hk
  rw [tileAt_halt hh hk] at h
  exact TileTag.noConfusion h

omit [LinearOrder A] [Finite A] in
/-- **An arrival is the cell the head is entering**, from the left when the
transition moves right. -/
theorem arr_of_tileAt {k : ℕ} {cell : WPoint A} {right : Bool}
    (h : (tileAt g tr n k cell).1 = if right then TileTag.arrL else TileTag.arrR) :
    (g k).head ≠ cell ∧ k < n ∧ (g (k + 1)).head = cell ∧
      (WMRight (wpElt (tr k)) ↔ right = true) := by
  have hh : (g k).head ≠ cell := by
    intro hc
    by_cases hk : k < n
    · rw [tileAt_head hc hk] at h
      cases right <;> simp only [Bool.false_eq_true, if_true, if_false] at h <;>
        exact TileTag.noConfusion h
    · rw [tileAt_halt hc hk] at h
      cases right <;> simp only [Bool.false_eq_true, if_true, if_false] at h <;>
        exact TileTag.noConfusion h
  by_cases hnext : k < n ∧ (g (k + 1)).head = cell
  · refine ⟨hh, hnext.1, hnext.2, ?_⟩
    rw [tileAt_arr hh hnext.1 hnext.2] at h
    by_cases hr : WMRight (wpElt (tr k))
    · rw [if_pos hr] at h
      cases right
      · exact absurd h (by simp)
      · exact iff_of_true hr rfl
    · rw [if_neg hr] at h
      cases right
      · exact iff_of_false hr (by simp)
      · exact absurd h (by simp)
  · rw [tileAt_sym hh hnext] at h
    cases right <;> simp only [Bool.false_eq_true] at h <;> exact TileTag.noConfusion h

omit [LinearOrder A] [Finite A] in
/-- The transition a head tile of the table carries is the one the step fires. -/
theorem tpTr_tileAt_head {k : ℕ} {cell : WPoint A} (hh : (g k).head = cell) (hk : k < n) :
    tpTr (tileAt g tr n k cell) = wpElt (tr k) := by
  rw [tileAt_head hh hk]
  rfl

omit [LinearOrder A] [Finite A] in
/-- The state an arrival of the table carries is the state the step reaches. -/
theorem tpState_tileAt_arr {k : ℕ} {cell : WPoint A} (hh : (g k).head ≠ cell) (hk : k < n)
    (hnext : (g (k + 1)).head = cell) :
    tpState (tileAt g tr n k cell) = wpElt (g (k + 1)).state := by
  rw [tileAt_arr hh hk hnext]
  rfl

omit [LinearOrder A] [Finite A] in
open Classical in
/-- The tag an arrival of the table carries names the side the head comes
from. -/
theorem tileAt_arr_tag {k : ℕ} {cell : WPoint A} (hh : (g k).head ≠ cell) (hk : k < n)
    (hnext : (g (k + 1)).head = cell) :
    (tileAt g tr n k cell).1 =
      if WMRight (wpElt (tr k)) then TileTag.arrL else TileTag.arrR := by
  rw [tileAt_arr hh hk hnext]

omit [LinearOrder A] [Finite A] in
/-- A transition moving right, read at the element it is. -/
theorem wmRight_iff_right {p : WPoint A} (htr : (wideRegData A).Tr p) :
    (wideRegData A).Right p ↔ WMRight (wpElt p) := by
  rcases p with s | x
  · exact htr.elim
  · exact Iff.rfl

/-- **Neighbouring cells of a row agree**: the head is unique, so no two heads
stand side by side; and the arrival next to it is on the side the transition
moves, since the head moves to *the* neighbour in that direction. -/
theorem tpHoriz_tileAt (hlin : IsLinOrd (WMLe (A := A)))
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    {cL cR : WPoint A}
    (hs : SuccPos (wideRegData A).Le (wideRegData A).Posn cL cR) (k : ℕ) :
    TPHoriz (tileAt g tr n k cL) (tileAt g tr n k cR) := by
  have hwp : IsLinOrd (wideRegData A).Le := isLinOrd_wpLe hlin
  refine ⟨tpTile_tileAt hstep k cL, tpTile_tileAt hstep k cR, ?_, ?_, ?_, ?_, ?_⟩
  · -- a head at the left that moves right hands the state to the right cell
    intro hhd hright
    obtain ⟨hhL, hk⟩ := head_of_tileAt hhd
    obtain ⟨htr, -, -, hdst, -, -, hmove⟩ := hstep k hk
    rw [tpTr_tileAt_head hhL hk] at hright
    have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g k).head (g (k + 1)).head := by
      rcases hmove with ⟨-, hsucc⟩ | ⟨hnr, -⟩
      · exact hsucc
      · exact absurd ((wmRight_iff_right htr).mpr hright) hnr
    rw [hhL] at hmv
    have hnext : (g (k + 1)).head = cR := TMData.succPos_right_unique hwp hmv hs
    have hhR : (g k).head ≠ cR := fun hc => hs.2.2.2.1 (hhL.symm.trans hc)
    refine ⟨?_, ?_⟩
    · rw [tileAt_arr_tag hhR hk hnext, if_pos hright]
    · rw [tpTr_tileAt_head hhL hk, tpState_tileAt_arr hhR hk hnext]
      exact wpAttr_elt hdst
  · -- a head at the right that moves left hands the state to the left cell
    intro hhd hleft
    obtain ⟨hhR, hk⟩ := head_of_tileAt hhd
    obtain ⟨htr, -, -, hdst, -, -, hmove⟩ := hstep k hk
    rw [tpTr_tileAt_head hhR hk] at hleft
    have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g (k + 1)).head (g k).head := by
      rcases hmove with ⟨hr, -⟩ | ⟨-, hsucc⟩
      · exact absurd ((wmRight_iff_right htr).mp hr) hleft
      · exact hsucc
    rw [hhR] at hmv
    have hprev : (g (k + 1)).head = cL := succPos_left_unique hwp hmv hs
    have hhL : (g k).head ≠ cL := fun hc => hs.2.2.2.1 (hc.symm.trans hhR)
    refine ⟨?_, ?_⟩
    · rw [tileAt_arr_tag hhL hk hprev, if_neg hleft]
    · rw [tpTr_tileAt_head hhR hk, tpState_tileAt_arr hhL hk hprev]
      exact wpAttr_elt hdst
  · -- an arrival from the left is the left neighbour's head, moving right
    intro harr
    obtain ⟨hhR, hk, hnext, hright⟩ :=
      arr_of_tileAt (right := true) (by rw [harr]; rfl)
    have hright' : WMRight (wpElt (tr k)) := hright.mpr rfl
    obtain ⟨htr, -, -, hdst, -, -, hmove⟩ := hstep k hk
    have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g k).head (g (k + 1)).head := by
      rcases hmove with ⟨-, hsucc⟩ | ⟨hnr, -⟩
      · exact hsucc
      · exact absurd ((wmRight_iff_right htr).mpr hright') hnr
    rw [hnext] at hmv
    have hhL : (g k).head = cL := succPos_left_unique hwp hmv hs
    refine ⟨?_, ?_, ?_⟩
    · rw [tileAt_head hhL hk]
    · rw [tpTr_tileAt_head hhL hk]
      exact hright'
    · rw [tpTr_tileAt_head hhL hk, tpState_tileAt_arr hhR hk hnext]
      exact wpAttr_elt hdst
  · -- an arrival from the right is the right neighbour's head, moving left
    intro harr
    obtain ⟨hhL, hk, hnext, hright⟩ :=
      arr_of_tileAt (right := false) (by rw [harr]; rfl)
    have hleft : ¬WMRight (wpElt (tr k)) := fun hc => by simpa using hright.mp hc
    obtain ⟨htr, -, -, hdst, -, -, hmove⟩ := hstep k hk
    have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g (k + 1)).head (g k).head := by
      rcases hmove with ⟨hr, -⟩ | ⟨-, hsucc⟩
      · exact absurd ((wmRight_iff_right htr).mp hr) hleft
      · exact hsucc
    rw [hnext] at hmv
    have hhR : (g k).head = cR := TMData.succPos_right_unique hwp hmv hs
    refine ⟨?_, ?_, ?_⟩
    · rw [tileAt_head hhR hk]
    · rw [tpTr_tileAt_head hhR hk]
      exact hleft
    · rw [tpTr_tileAt_head hhR hk, tpState_tileAt_arr hhL hk hnext]
      exact wpAttr_elt hdst
  · -- two heads never stand side by side
    rintro ⟨h1, h2⟩
    exact hs.2.2.2.1 ((head_eq_of_tileAt h1).symm.trans (head_eq_of_tileAt h2))

/-! ### The bottom row is the initial tape -/

omit [Nonempty A] [Finite A] in
/-- **The elements the bottom row is described at are the ones carrying
input**: a digit whose element has an input symbol, since a cell holding that
symbol and no head is always a tile of the emitted instance. -/
theorem wtHasFirst_tileStr (p : TilePt A) :
    letI := tileStr A
    (WTHasFirst p ↔ TPDig p ∧ WMHasInp (p.2 0)) := by
  letI := tileStr A
  constructor
  · rintro ⟨t, a, hdig, -, hinp, -⟩
    exact ⟨hdig, a, hinp⟩
  · rintro ⟨hdig, a, hinp⟩
    exact ⟨(TileTag.sym, ![a, a, a]), a, hdig, Or.inl rfl, hinp, rfl⟩

omit [Nonempty A] [Finite A] in
/-- **The cells of the emitted file are the machine's register cells**: a
coordinate is a cell of the digit of `x` exactly when the address it is is the
machine's cell of `x`. -/
theorem wmFileSeg_tpCol (s : A → Prop) (x : A) :
    letI := tileStr A
    (WMFileSeg WTLe WTHasFirst (tpCol s) (tpDig x) ↔ WMRegSeg s x) := by
  letI := tileStr A
  have hdig : ∀ y : A, (tpCol s (tpDig y) ↔
      (WTLe (tpDig (A := A) y) (tpDig x) ∧ WTHasFirst (tpDig (A := A) y))) ↔
      (s y ↔ (WMLe y x ∧ WMHasInp y)) := by
    intro y
    rw [tpCol_dig, wtLe_tileStr, tpLe_dig, wtHasFirst_tileStr]
    exact iff_congr Iff.rfl (and_congr_right fun _ =>
      ⟨fun h => h.2, fun h => ⟨tpDig_isDig y, h⟩⟩)
  constructor
  · exact fun h y => (hdig y).mp (h (tpDig y))
  · intro h p
    by_cases hd : TPDig p
    · have hp : tpDig (A := A) (p.2 0) = p := tpDig_eq_self hd
      rw [← hp]
      exact (hdig (p.2 0)).mpr (h (p.2 0))
    · refine iff_of_false (fun hc => hd (tpCol_dig_of_mem hc)) ?_
      rintro ⟨-, hhas⟩
      exact hd ((wtHasFirst_tileStr p).mp hhas).1

omit [Nonempty A] [Finite A] in
/-- **The bottom row of the emitted tiling is the machine's initial tape**: the
cell of an element may carry a tile holding that element's input symbol, and no
head. -/
theorem wtpFirst_tpCol (s : A → Prop) (t : TilePt A) :
    letI := tileStr A
    ((wideTileData (TilePt A)).First (Sum.inl (tpCol s)) (Sum.inr t) ↔
      ∃ x a, WMRegSeg s x ∧ WMInp x a ∧ TPNoHead t ∧ tpSym t = a) := by
  letI := tileStr A
  constructor
  · rintro ⟨x', hseg, a, hdig, hnohead, hinp, hsym⟩
    have hx' : tpDig (A := A) (x'.2 0) = x' := tpDig_eq_self hdig
    refine ⟨x'.2 0, a, (wmFileSeg_tpCol s (x'.2 0)).mp ?_, hinp, hnohead, hsym⟩
    rw [hx']
    exact hseg
  · rintro ⟨x, a, hseg, hinp, hnohead, hsym⟩
    exact ⟨tpDig x, (wmFileSeg_tpCol s x).mpr hseg, a, tpDig_isDig x, hnohead, hinp, hsym⟩

omit [Nonempty A] [LinearOrder A] [Finite A] in
/-- The empty address is no register cell, so the machine starts on a blank. -/
theorem not_wmRegSeg_bot (hlin : IsLinOrd (WMLe (A := A))) {x a : A} (hinp : WMInp x a) :
    ¬WMRegSeg (fun _ : A => False) x :=
  fun h => (h x).mpr ⟨hlin.1 x, a, hinp⟩

/-- **The bottom row the table draws is one the description allows**: the corner
carries the machine's start – the head, on the blank cell it begins on – and
every other column carries the input symbol of its element, or the blank where
the description names none. -/
theorem first_tableTiling (hwf : WideWF A)
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    (hinit : (wideRegData A).IsInit (g 0)) {x y : WPoint (TilePt A)}
    (hx : letI := tileStr A; (wideTileData (TilePt A)).Posn x)
    (hy : letI := tileStr A
      MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn y) :
    letI := tileStr A
    ((MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn x →
        (wideTileData (TilePt A)).Start (tableTiling g tr n x y)) ∧
      (¬MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn x →
        (wideTileData (TilePt A)).FirstTile x (tableTiling g tr n x y))) := by
  letI := tileStr A
  obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
  obtain rfl : y = Sum.inl (tpCol (fun _ : A => False)) := eq_bot_of_minPos hwf.1 hy
  have hhead : (g 0).head = (Sum.inl fun _ : A => False) :=
    (minPos_wpLe_iff hwf.1 _).mp hinit.2.1
  have htile : tableTiling g tr n (Sum.inl (tpCol s))
      (Sum.inl (tpCol (fun _ : A => False))) = Sum.inr (tileAt g tr n 0 (Sum.inl s)) := by
    rw [tableTiling, addrOf_tpCol, addrOf_tpCol, wideRank_bot hwf.1]
  rw [htile]
  constructor
  · -- the corner: the machine's start
    intro hmin
    obtain rfl : s = fun _ : A => False :=
      tpCol_injective (Sum.inl.inj (eq_bot_of_minPos hwf.1 hmin))
    have hhh : (g 0).head = (Sum.inl fun _ : A => False) := hhead
    have hblank : WMBlank (wpElt ((g 0).tape (Sum.inl fun _ : A => False))) := by
      rcases hinit.2.2 (Sum.inl fun _ : A => False) with hinp | ⟨-, hb⟩
      · rcases h : (g 0).tape (Sum.inl fun _ : A => False) with u | b
        · rw [h] at hinp
          exact hinp.elim
        · rw [h] at hinp
          obtain ⟨z, hseg, hz⟩ := hinp
          exact absurd hseg (not_wmRegSeg_bot hwf.1 hz)
      · exact wpMark_elt hb
    have hstart : TPStart (tileAt g tr n 0 (Sum.inl fun _ : A => False)) := by
      refine ⟨hwf, ?_, ?_, ?_⟩
      · by_cases hk : 0 < n
        · have htl := tpTile_tileAt hstep 0 (Sum.inl fun _ : A => False)
          rw [tileAt_head hhh hk] at htl ⊢
          exact Or.inl ⟨rfl, htl.1, htl.2.1, htl.2.2⟩
        · rw [tileAt_halt hhh hk]
          exact Or.inr rfl
      · have hst : tpState (tileAt g tr n 0 (Sum.inl fun _ : A => False)) =
            wpElt (g 0).state := by
          by_cases hk : 0 < n
          · rw [tileAt_head hhh hk]
            rfl
          · rw [tileAt_halt hhh hk]
            rfl
        rw [hst]
        exact wpMark_elt hinit.1
      · rw [show tpSym (tileAt g tr n 0 (Sum.inl fun _ : A => False)) =
          wpElt ((g 0).tape (Sum.inl fun _ : A => False)) from tpSym_tileAt]
        exact hblank
    exact hstart
  · -- every other column: the input symbol of its element, or the blank
    intro hmin
    have hs : s ≠ fun _ : A => False := by
      intro hc
      exact hmin (hc ▸ minPos_tpCol_bot hwf.1)
    have hne : (g 0).head ≠ Sum.inl s := by
      rw [hhead]
      exact fun hc => hs (Sum.inl.inj hc).symm
    have hnh : TPNoHead (tileAt g tr n 0 (Sum.inl s)) := tpNoHead_tileAt hne
    have hsym : tpSym (tileAt g tr n 0 (Sum.inl s)) =
        wpElt ((g 0).tape (Sum.inl s)) := tpSym_tileAt
    rcases hinit.2.2 (Sum.inl s) with hinp | ⟨hno, hb⟩
    · refine Or.inl ((wtpFirst_tpCol s _).mpr ?_)
      rcases h : (g 0).tape (Sum.inl s) with u | b
      · rw [h] at hinp
        exact hinp.elim
      · rw [h] at hinp
        obtain ⟨z, hseg, hz⟩ := hinp
        exact ⟨z, b, hseg, hz, hnh, hsym.trans ((congrArg wpElt h).trans (wpElt_inr b))⟩
    · have hbase : TPBase (tileAt g tr n 0 (Sum.inl s)) := by
        refine ⟨hnh, ?_⟩
        rw [hsym]
        exact wpMark_elt hb
      refine Or.inr ⟨?_, hbase⟩
      rintro (u | t) hu
      · exact hu.elim
      · obtain ⟨z, a, hseg, hz, -, -⟩ := (wtpFirst_tpCol s t).mp hu
        exact hno (Sum.inr a) ⟨z, hseg, hz⟩


/-! ### The two edge columns -/

omit [LinearOrder A] in
/-- **The head never arrives from the left at the first cell**: an arrival from
the left is a step moving right into that cell, and nothing lies below the least
position. -/
theorem tpEdgeL_tileAt (hlin : IsLinOrd (WMLe (A := A)))
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    {cell : WPoint A} (hmin : MinPos (wideRegData A).Le (wideRegData A).Posn cell) (k : ℕ) :
    TPEdgeL (tileAt g tr n k cell) := by
  intro harr
  obtain ⟨hh, hk, hnext, hright⟩ := arr_of_tileAt (right := true) (by rw [harr]; rfl)
  obtain ⟨htr, -, -, -, -, -, hmove⟩ := hstep k hk
  have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g k).head (g (k + 1)).head := by
    rcases hmove with ⟨-, hsucc⟩ | ⟨hnr, -⟩
    · exact hsucc
    · exact absurd ((wmRight_iff_right htr).mpr (hright.mpr rfl)) hnr
  rw [hnext] at hmv
  exact hmv.2.2.2.1
    ((isLinOrd_wpLe hlin).2.2.1 _ _ hmv.2.2.1 (hmin.2 (g k).head hmv.1))

omit [LinearOrder A] in
/-- **And never from the right at the last cell**: an arrival from the right is a
step moving left into that cell, and nothing lies above the greatest
position. -/
theorem tpEdgeR_tileAt (hlin : IsLinOrd (WMLe (A := A)))
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i))
    {cell : WPoint A} (hmax : MaxPos (wideRegData A).Le (wideRegData A).Posn cell) (k : ℕ) :
    TPEdgeR (tileAt g tr n k cell) := by
  intro harr
  obtain ⟨hh, hk, hnext, hright⟩ := arr_of_tileAt (right := false) (by rw [harr]; rfl)
  have hleft : ¬WMRight (wpElt (tr k)) := fun hc => by simpa using hright.mp hc
  obtain ⟨htr, -, -, -, -, -, hmove⟩ := hstep k hk
  have hmv : SuccPos (wideRegData A).Le (wideRegData A).Posn (g (k + 1)).head (g k).head := by
    rcases hmove with ⟨hr, -⟩ | ⟨-, hsucc⟩
    · exact absurd ((wmRight_iff_right htr).mp hr) hleft
    · exact hsucc
  rw [hnext] at hmv
  exact hmv.2.2.2.1
    ((isLinOrd_wpLe hlin).2.2.1 _ _ hmv.2.2.1 (hmax.2 (g k).head hmv.2.1))

/-! ### The table is a tiling -/

omit [LinearOrder A] [Finite A] in
/-- The tile the table puts at a coordinate of the emitted square, read at the
machine's own address and time. -/
theorem tableTiling_tpCol (s r : A → Prop) :
    tableTiling g tr n (Sum.inl (tpCol s)) (Sum.inl (tpCol r)) =
      Sum.inr (tileAt g tr n (wideRank r) (Sum.inl s)) := by
  rw [tableTiling, addrOf_tpCol, addrOf_tpCol]

/-- **An accepting run draws a tiling of the emitted square.** Each of the five
conditions is one fact about the run: every cell carries a tile because a head
tile carries the transition the step fires; the bottom row is the initial tape;
neighbours in a row agree because the head is unique; one row becomes the next
because a step writes under the head and leaves every other cell alone; and the
accepting configuration's own cell carries an accepting tile. -/
theorem isTiling_tableTiling (hwf : WideWF A)
    (hinit : (wideRegData A).IsInit (g 0))
    (hlt : n < Nat.card {p : WPoint A // (wideRegData A).Posn p})
    (hfreeze : ∀ i, n ≤ i → g i = g n) (hacc : (wideRegData A).Acc (g n).state)
    (hstep : ∀ i, i < n → StepWith (wideRegData A) (g i) (g (i + 1)) (tr i)) :
    letI := tileStr A
    (wideTileData (TilePt A)).IsTiling (tableTiling g tr n) := by
  letI := tileStr A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every cell carries a tile
    intro x y hx hy
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
    obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hy
    rw [tableTiling_tpCol]
    exact tpTile_tileAt hstep _ _
  · -- the bottom row is the initial tape
    exact fun x y hx hy => first_tableTiling hwf hstep hinit hx hy
  · -- the leftmost column
    intro x y hy hmin
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hy
    obtain rfl : x = Sum.inl (tpCol (fun _ : A => False)) := eq_bot_of_minPos hwf.1 hmin
    rw [tableTiling_tpCol]
    exact tpEdgeL_tileAt hwf.1 hstep (minPos_wpLe hwf.1) _
  · -- the rightmost column
    intro x y hy hmax
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hy
    obtain rfl : x = Sum.inl (tpCol (fun _ : A => True)) := eq_top_of_maxPos hwf.1 hmax
    rw [tableTiling_tpCol]
    exact tpEdgeR_tileAt hwf.1 hstep (maxPos_wpLe hwf.1) _
  · -- neighbours in a row agree
    intro x x' y hsucc hy
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hsucc.1
    obtain ⟨t, rfl⟩ := exists_tpCol_of_posn hsucc.2.1
    obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hy
    rw [tableTiling_tpCol, tableTiling_tpCol]
    exact tpHoriz_tileAt hwf.1 hstep
      ((succPos_wpLe_iff hwf.1 s t).mpr ((succPos_tpCol hwf.1 s t).mp hsucc)) _
  · -- one row becomes the next
    intro x y y' hx hsucc
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
    obtain ⟨r, rfl⟩ := exists_tpCol_of_posn hsucc.1
    obtain ⟨r', rfl⟩ := exists_tpCol_of_posn hsucc.2.1
    rw [tableTiling_tpCol, tableTiling_tpCol,
      wideRank_incr hwf.1 ((succPos_tpCol hwf.1 r r').mp hsucc)]
    exact tpVert_tileAt hstep hfreeze _ _
  · -- the accepting configuration's cell carries an accepting tile
    obtain ⟨r, hr⟩ := exists_wideRank_eq (A := A) hwf.1 hlt
    have hposn : (wideRegData A).Posn (g n).head := head_posn hinit hfreeze hstep n
    obtain ⟨c, hc⟩ : ∃ c : A → Prop, (g n).head = Sum.inl c := by
      rcases h : (g n).head with u | x
      · exact ⟨u, rfl⟩
      · rw [h] at hposn
        exact hposn.elim
    refine ⟨Sum.inl (tpCol c), Sum.inl (tpCol r), fun p hp => tpCol_dig_of_mem hp,
      fun p hp => tpCol_dig_of_mem hp, ?_⟩
    rw [tableTiling_tpCol, hr, ← hc]
    exact tpAcc_tileAt hacc

/-- **An accepting run makes the emitted square tileable**, which is the forward
half of the hardness: the table the run draws is a tiling. -/
theorem tileable_of_accepts (hwf : WideWF A) (h : (wideRegData A).Accepts) :
    letI := tileStr A
    (wideTileData (TilePt A)).WellFormed ∧ (wideTileData (TilePt A)).Tileable := by
  letI := tileStr A
  obtain ⟨g, tr, n, hinit, hlt, hfreeze, hacc, hstep⟩ := exists_runData h
  exact ⟨wideTileData_wellFormed (isLinOrd_tpLe hwf.1),
    ⟨tableTiling g tr n, isTiling_tableTiling hwf hinit hlt hfreeze hacc hstep⟩⟩


end Yes

end TilingHard

end DescriptiveComplexity
