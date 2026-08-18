/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Grid
import DescriptiveComplexity.Problems.Wide.TrackWrites
import DescriptiveComplexity.Problems.Wide.Roam
import DescriptiveComplexity.Problems.Wide.LowFile

/-!
# A run, read as a table of tiles

The half of the drawing that turns an accepting run of a clocked wide machine
into a tiling of the emitted square: the row of rank `k` is the configuration at
time `k`, and a cell of that row is the tile the configuration puts there.

## What a configuration puts in a cell

* the head's own cell carries `head` while the run still has a step to take, and
  `halt` once it has stopped – which is what lets a run shorter than the clock
  fill the rows above it, every one repeating the last configuration;
* the cell the head is *about to* enter carries the arrival, on the side the head
  comes from;
* every other cell carries `sym`, holding what the tape holds there.

The states, the symbols and the transitions of the machine are control elements
of its universe – `Sum.inr` points – and a tile stores the *element*, so the
reading `DescriptiveComplexity.TilingHard.wpElt` is used throughout; that it
loses nothing is `wpElt_mark` and `wpElt_attr`, since a mark or an attribute of
the instance holds of no address.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-! ### Control elements, read as elements -/

section Elements

variable {A : Type} [Nonempty A]

open Classical in
/-- **The element a point of the machine's universe is**, arbitrary at an
address. Every point a mark or an attribute of the instance holds of is a control
element, so nothing is lost where it is used. -/
noncomputable def wpElt (p : WPoint A) : A :=
  match p with
  | Sum.inl _ => Classical.arbitrary A
  | Sum.inr x => x

@[simp]
theorem wpElt_inr (x : A) : wpElt (Sum.inr x : WPoint A) = x := rfl

/-- A point carrying a mark of the instance is a control element. -/
theorem eq_inr_of_wpMark {R : A → Prop} {p : WPoint A} (h : wpMark R p) :
    p = Sum.inr (wpElt p) := by
  rcases p with s | x
  · exact h.elim
  · rfl

/-- And the mark holds of the element it is. -/
theorem wpMark_elt {R : A → Prop} {p : WPoint A} (h : wpMark R p) : R (wpElt p) := by
  rcases p with s | x
  · exact h.elim
  · exact h

/-- And the attribute holds of the elements they are. -/
theorem wpAttr_elt {R : A → A → Prop} {p q : WPoint A} (h : wpAttr R p q) :
    R (wpElt p) (wpElt q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · exact h

end Elements

/-! ### A run, with its transitions named -/

section RunData

variable {V : Type} {M : TMData V}

/-- **One step, with the transition it fires named**: `TMData.Step` with its
existential opened, so that a drawing may put *the* transition in a tile. -/
def StepWith (M : TMData V) (c c' : Config V) (τ : V) : Prop :=
  M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧ M.Dst τ c'.state ∧
    M.Write τ (c'.tape c.head) ∧ (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

theorem step_iff_stepWith {c c' : Config V} :
    M.Step c c' ↔ ∃ τ, StepWith M c c' τ := Iff.rfl

open Classical in
/-- **An accepting run, as a sequence with its transitions**: the configurations
at every time, the transition fired at every step before the last, and the run
standing still afterwards. -/
theorem exists_runData [Nonempty V] (h : M.Accepts) :
    ∃ (g : ℕ → Config V) (tr : ℕ → V) (n : ℕ),
      M.IsInit (g 0) ∧ n < Nat.card {p : V // M.Posn p} ∧ (∀ i, n ≤ i → g i = g n) ∧
      M.Acc (g n).state ∧ ∀ i, i < n → StepWith M (g i) (g (i + 1)) (tr i) := by
  obtain ⟨c₀, c, n, hinit, hlt, hsteps, hacc⟩ := h
  obtain ⟨g, hg0, hgn, hgs⟩ := TMData.exists_seq_of_stepsIn hsteps
  have hex : ∀ i, ∃ τ, i < n → StepWith M (g i) (g (i + 1)) τ := by
    intro i
    by_cases hi : i < n
    · obtain ⟨τ, hτ⟩ := step_iff_stepWith.mp (hgs i hi)
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨Classical.arbitrary V, fun hc => absurd hc hi⟩
  choose tr htr using hex
  refine ⟨g, tr, n, hg0 ▸ hinit, hlt, fun i hi => ?_, ?_, fun i hi => htr i hi⟩
  · rw [hgn i hi, hgn n le_rfl]
  · rw [hgn n le_rfl]
    exact hacc

open Classical in
/-- **An accepting run in bounded space, as a sequence with its transitions**:
the same reading as `DescriptiveComplexity.TilingHard.exists_runData` for a
machine with no clock – the run is still finite, only its length is not
bounded by the instance. -/
theorem exists_runDataSpace [Nonempty V] (h : M.AcceptsSpace) :
    ∃ (g : ℕ → Config V) (tr : ℕ → V) (n : ℕ),
      M.IsInit (g 0) ∧ (∀ i, n ≤ i → g i = g n) ∧ M.Acc (g n).state ∧
      ∀ i, i < n → StepWith M (g i) (g (i + 1)) (tr i) := by
  obtain ⟨c₀, c, hinit, hreach, hacc⟩ := h
  obtain ⟨n, hsteps⟩ := TMData.exists_stepsIn_of_reflTransGen hreach
  obtain ⟨g, hg0, hgn, hgs⟩ := TMData.exists_seq_of_stepsIn hsteps
  have hex : ∀ i, ∃ τ, i < n → StepWith M (g i) (g (i + 1)) τ := by
    intro i
    by_cases hi : i < n
    · obtain ⟨τ, hτ⟩ := step_iff_stepWith.mp (hgs i hi)
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨Classical.arbitrary V, fun hc => absurd hc hi⟩
  choose tr htr using hex
  refine ⟨g, tr, n, hg0 ▸ hinit, fun i hi => ?_, ?_, fun i hi => htr i hi⟩
  · rw [hgn i hi, hgn n le_rfl]
  · rw [hgn n le_rfl]
    exact hacc

/-- **The head stands on a position at every time**: it starts on the least one
and a step moves it to a neighbour. -/
theorem head_posn {g : ℕ → Config V} {tr : ℕ → V} {n : ℕ}
    (hinit : M.IsInit (g 0)) (hfreeze : ∀ i, n ≤ i → g i = g n)
    (hstep : ∀ i, i < n → StepWith M (g i) (g (i + 1)) (tr i)) (k : ℕ) :
    M.Posn (g k).head := by
  have hup : ∀ j, j ≤ n → M.Posn (g j).head := by
    intro j
    induction j with
    | zero => exact fun _ => hinit.2.1.1
    | succ m ih =>
      intro hm
      obtain ⟨-, -, -, -, -, -, hmove⟩ := hstep m (by omega)
      rcases hmove with ⟨-, hs⟩ | ⟨-, hs⟩
      · exact hs.2.1
      · exact hs.1
  by_cases hk : k ≤ n
  · exact hup k hk
  · rw [hfreeze k (by omega)]
    exact hup n le_rfl

end RunData

/-! ### A row for every step of the clock -/

section Rows

variable {A : Type} [Finite A] [Language.wide.Structure A]

/-- **Every rank below the number of addresses is taken**: the rank map is
injective into as many numbers as there are addresses, so it is onto them. That
is what gives the drawing a row for every step of the clock, the clock counting
the addresses. -/
theorem exists_wideRank_eq (h : IsLinOrd (WMLe (A := A))) {k : ℕ}
    (hk : k < Nat.card {p : WPoint A // (wideData A).Posn p}) :
    ∃ s : A → Prop, wideRank s = k := by
  classical
  have := Fintype.ofFinite (A → Prop)
  have hcard : Fintype.card (A → Prop) =
      Nat.card {p : WPoint A // (wideData A).Posn p} := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (wideAddrEquiv (A := A))).symm
  have hinj : Function.Injective fun s : A → Prop =>
      (⟨wideRank s, wideRank_lt_card s⟩ :
        Fin (Nat.card {p : WPoint A // (wideData A).Posn p})) :=
    fun s t he => wideRank_injective h (congrArg Fin.val he)
  have hsurj := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, hcard]⟩ |>.2
  obtain ⟨s, hs⟩ := hsurj ⟨k, hk⟩
  exact ⟨s, congrArg Fin.val hs⟩

end Rows

/-! ### The tile a configuration puts in a cell -/

section Table

variable {A : Type} [Nonempty A] [Language.wide.Structure A]

open Classical in
/-- **The tile the run puts at a cell of a row**: the head's cell carries the
head while a step is left and the halt afterwards, the cell the head is entering
carries the arrival on the side it comes from, and every other cell carries what
the tape holds. -/
noncomputable def tileAt (g : ℕ → Config (WPoint A)) (tr : ℕ → WPoint A) (n k : ℕ)
    (cell : WPoint A) : TilePt A :=
  let a := wpElt ((g k).tape cell)
  if (g k).head = cell then
    if k < n then (TileTag.head, ![a, wpElt (g k).state, wpElt (tr k)])
    else (TileTag.halt, ![a, wpElt (g k).state, a])
  else if k < n ∧ (g (k + 1)).head = cell then
    if WMRight (wpElt (tr k)) then (TileTag.arrL, ![a, wpElt (g (k + 1)).state, a])
    else (TileTag.arrR, ![a, wpElt (g (k + 1)).state, a])
  else (TileTag.sym, ![a, a, a])

variable {g : ℕ → Config (WPoint A)} {tr : ℕ → WPoint A} {n k : ℕ} {cell : WPoint A}

open Classical in
@[simp]
theorem tileAt_head (hh : (g k).head = cell) (hk : k < n) :
    tileAt g tr n k cell =
      (TileTag.head, ![wpElt ((g k).tape cell), wpElt (g k).state, wpElt (tr k)]) := by
  rw [tileAt]
  simp only [if_pos hh, if_pos hk]

open Classical in
@[simp]
theorem tileAt_halt (hh : (g k).head = cell) (hk : ¬k < n) :
    tileAt g tr n k cell =
      (TileTag.halt, ![wpElt ((g k).tape cell), wpElt (g k).state,
        wpElt ((g k).tape cell)]) := by
  rw [tileAt]
  simp only [if_pos hh, if_neg hk]

open Classical in
@[simp]
theorem tileAt_sym (hh : (g k).head ≠ cell) (hnext : ¬(k < n ∧ (g (k + 1)).head = cell)) :
    tileAt g tr n k cell =
      (TileTag.sym, ![wpElt ((g k).tape cell), wpElt ((g k).tape cell),
        wpElt ((g k).tape cell)]) := by
  rw [tileAt]
  simp only [if_neg hh, if_neg hnext]

open Classical in
theorem tileAt_arr (hh : (g k).head ≠ cell) (hk : k < n) (hnext : (g (k + 1)).head = cell) :
    tileAt g tr n k cell =
      (if WMRight (wpElt (tr k)) then TileTag.arrL else TileTag.arrR,
        ![wpElt ((g k).tape cell), wpElt (g (k + 1)).state,
          wpElt ((g k).tape cell)]) := by
  have hcond : k < n ∧ (g (k + 1)).head = cell := ⟨hk, hnext⟩
  rw [tileAt]
  simp only [if_neg hh, if_pos hcond]
  by_cases hr : WMRight (wpElt (tr k))
  · simp only [if_pos hr]
  · simp only [if_neg hr]

/-- The symbol a tile of the table holds is what the tape holds there. -/
theorem tpSym_tileAt : tpSym (tileAt g tr n k cell) = wpElt ((g k).tape cell) := by
  by_cases hh : (g k).head = cell
  · by_cases hk : k < n
    · rw [tileAt_head hh hk]
      rfl
    · rw [tileAt_halt hh hk]
      rfl
  · by_cases hnext : k < n ∧ (g (k + 1)).head = cell
    · rw [tileAt_arr hh hnext.1 hnext.2]
      rfl
    · rw [tileAt_sym hh hnext]
      rfl

end Table

end TilingHard

end DescriptiveComplexity
