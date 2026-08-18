/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard
import DescriptiveComplexity.Problems.Wide.Corridor
import DescriptiveComplexity.Problems.Wide.Membership
import DescriptiveComplexity.Problems.Wide.Reduce

/-!
# Tiling a wide corridor is EXPSPACE-complete

The corridor is the square's reduction with the clock taken out: the columns are
still the machine's addresses, the rows are still its configurations, but there
is no bound on how many of them there are – which is exactly a machine bounded
in *space* and not in time.

Everything the drawing consists of is the square's
(`DescriptiveComplexity.Problems.Wide.TilingHard`): the tiles, the transition a
head carries, the arrival that hands it on, the border marks. Only the **bottom
row** differs, because the two machines describe their tapes differently – the
clocked one by a register file, the space-bounded one by the ruler of all the
segments – which is why the drawing carries that row as a parameter
(`DescriptiveComplexity.TilingHard.tileStrOf`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

/-! ### The bottom row at the ruler -/

section Ruler

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

omit [Finite A] in
/-- **Every digit is described**, as soon as the instance has a blank: an
element with an input symbol has a tile holding it, and one without has the
blank. That is what makes the drawing's file the machine's whole ruler. -/
theorem wtHasFirst_tileStrR (hblank : ∃ b : A, WMBlank b) (p : TilePt A) :
    letI := tileStrR A
    (WTHasFirst p ↔ TPDig p) := by
  letI := tileStrR A
  refine ⟨fun h => h.choose_spec.1, fun hdig => ?_⟩
  by_cases hinp : ∃ a, WMInp (p.2 0) a
  · obtain ⟨a, ha⟩ := hinp
    exact ⟨(TileTag.sym, ![a, a, a]), hdig, Or.inl rfl, Or.inl ha⟩
  · obtain ⟨b, hb⟩ := hblank
    exact ⟨(TileTag.sym, ![b, b, b]), hdig, Or.inl rfl,
      Or.inr ⟨fun a ha => hinp ⟨a, ha⟩, hb⟩⟩

omit [Finite A] in
/-- **The cells of the drawing's file are the machine's own segments**: a
coordinate is the cell of the digit of `x` exactly when the address it is is the
initial segment `x` cuts. -/
theorem wmFileSeg_tpColR (hblank : ∃ b : A, WMBlank b) (s : A → Prop) (x : A) :
    letI := tileStrR A
    (WMFileSeg WTLe WTHasFirst (tpCol s) (tpDig x) ↔ WMDown WMLe s x) := by
  letI := tileStrR A
  have hdig : ∀ y : A, (tpCol s (tpDig y) ↔
      (WTLe (tpDig (A := A) y) (tpDig x) ∧ WTHasFirst (tpDig (A := A) y))) ↔
      (s y ↔ WMLe y x) := by
    intro y
    rw [tpCol_dig, wtLe_tileStrOf, tpLe_dig, wtHasFirst_tileStrR hblank]
    exact iff_congr Iff.rfl ⟨fun h => h.1, fun h => ⟨h, tpDig_isDig y⟩⟩
  constructor
  · exact fun h y => (hdig y).mp (h (tpDig y))
  · intro h p
    by_cases hd : TPDig p
    · have hp : tpDig (A := A) (p.2 0) = p := tpDig_eq_self hd
      rw [← hp]
      exact (hdig (p.2 0)).mpr (h (p.2 0))
    · refine iff_of_false (fun hc => hd (tpCol_dig_of_mem hc)) ?_
      rintro ⟨-, hhas⟩
      exact hd ((wtHasFirst_tileStrR hblank p).mp hhas)

omit [Finite A] in
/-- **The bottom row of the drawing is the machine's ruler**: the cell of an
element may carry a tile holding that element's input symbol, or the blank where
it has none. -/
theorem wtpFirst_tpColR (hblank : ∃ b : A, WMBlank b) (s : A → Prop) (t : TilePt A) :
    letI := tileStrR A
    ((wideTileData (TilePt A)).First (Sum.inl (tpCol s)) (Sum.inr t) ↔
      ∃ x, WMDown WMLe s x ∧ TPFirstR (tpDig x) t) := by
  letI := tileStrR A
  constructor
  · rintro ⟨x', hseg, hfirst⟩
    have hx' : tpDig (A := A) (x'.2 0) = x' := tpDig_eq_self hfirst.1
    refine ⟨x'.2 0, (wmFileSeg_tpColR hblank s (x'.2 0)).mp ?_, ?_⟩
    · rw [hx']
      exact hseg
    · rw [hx']
      exact hfirst
  · rintro ⟨x, hdown, hfirst⟩
    exact ⟨tpDig x, (wmFileSeg_tpColR hblank s x).mpr hdown, hfirst⟩

omit [LinearOrder A] [Finite A] in
/-- **An address is the segment of at most one element**: the two elements are
each below the other. -/
theorem wmDown_unique (hlin : IsLinOrd (WMLe (A := A))) {s : A → Prop} {x x' : A}
    (h : WMDown WMLe s x) (h' : WMDown WMLe s x') : x = x' :=
  hlin.2.2.1 _ _ ((h' x).mp ((h x).mpr (hlin.1 x))) ((h x').mp ((h' x').mpr (hlin.1 x')))

end Ruler

/-! ### An accepting run draws a corridor -/

section Yes

variable {A : Type} [Nonempty A] [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable {g : ℕ → Config (WPoint A)} {tr : ℕ → WPoint A} {n : ℕ}

/-- **The corridor a run draws**: the row of index `k` is the configuration at
time `k`, and its cell at a column is the tile that configuration puts there. -/
noncomputable def tableCorridor (g : ℕ → Config (WPoint A)) (tr : ℕ → WPoint A) (n : ℕ) :
    ℕ → WPoint (TilePt A) → WPoint (TilePt A) :=
  fun k col => Sum.inr (tileAt g tr n k (Sum.inl (addrOf col)))

omit [LinearOrder A] [Finite A] in
theorem tableCorridor_tpCol (k : ℕ) (s : A → Prop) :
    tableCorridor g tr n k (Sum.inl (tpCol s)) = Sum.inr (tileAt g tr n k (Sum.inl s)) := by
  rw [tableCorridor, addrOf_tpCol]

/-- **The bottom row the table draws is the machine's initial tape**, read at
the ruler: the corner carries the machine's start, and every other column the
input symbol of the element whose segment it is, or the blank. -/
theorem first_tableCorridor (hwf : WideWF A)
    (hstep : ∀ i, i < n → StepWith (wideData A) (g i) (g (i + 1)) (tr i))
    (hinit : (wideData A).IsInit (g 0)) {x : WPoint (TilePt A)}
    (hx : letI := tileStrR A; (wideTileData (TilePt A)).Posn x) :
    letI := tileStrR A
    ((MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn x →
        (wideTileData (TilePt A)).Start (tableCorridor g tr n 0 x)) ∧
      (¬MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn x →
        (wideTileData (TilePt A)).FirstTile x (tableCorridor g tr n 0 x))) := by
  letI := tileStrR A
  obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
  have hhead : (g 0).head = (Sum.inl fun _ : A => False) :=
    (minPos_wpLe_iff hwf.1 _).mp hinit.2.1
  rw [tableCorridor_tpCol]
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
          obtain ⟨z, hdown, -⟩ := hinp
          exact absurd ((hdown z).mpr (hwf.1.1 z)) (fun hc => hc)
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
  · -- every other column: the initial tape at the ruler
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
    by_cases hdown : ∃ x, WMDown WMLe s x
    · obtain ⟨x, hx'⟩ := hdown
      refine Or.inl ((wtpFirst_tpColR hwf.2.2.1 s _).mpr ⟨x, hx', tpDig_isDig x, hnh, ?_⟩)
      rcases hinit.2.2 (Sum.inl s) with hinp | ⟨hno, hb⟩
      · rcases h : (g 0).tape (Sum.inl s) with u | b
        · rw [h] at hinp
          exact hinp.elim
        · rw [h] at hinp
          obtain ⟨z, hdz, hz⟩ := hinp
          obtain rfl : z = x := wmDown_unique hwf.1 hdz hx'
          rw [hsym, h]
          exact Or.inl hz
      · refine Or.inr ⟨fun a ha => ?_, ?_⟩
        · exact hno (Sum.inr a) ⟨x, hx', ha⟩
        · rw [hsym]
          exact wpMark_elt hb
    · -- the column is no segment at all, so the description is silent there
      refine Or.inr ⟨fun u hu => ?_, ?_⟩
      · rcases u with v | t
        · exact hu.elim
        · obtain ⟨x, hdx, -⟩ := (wtpFirst_tpColR hwf.2.2.1 s t).mp hu
          exact hdown ⟨x, hdx⟩
      · have hbase : TPBase (tileAt g tr n 0 (Sum.inl s)) := by
          refine ⟨hnh, ?_⟩
          rcases hinit.2.2 (Sum.inl s) with hinp | ⟨-, hb⟩
          · rcases h : (g 0).tape (Sum.inl s) with u | b
            · rw [h] at hinp
              exact hinp.elim
            · rw [h] at hinp
              obtain ⟨z, hdz, -⟩ := hinp
              exact absurd ⟨z, hdz⟩ hdown
          · rw [hsym]
            exact wpMark_elt hb
        exact hbase

/-- **An accepting run in bounded space draws a corridor of the emitted
square.** Each of the conditions is the square's, with the clock taken out: the
rows are the configurations, one per time step, and there is no bound on how
many of them the run takes. -/
theorem isCorridor_tableCorridor (hwf : WideWF A)
    (hinit : (wideData A).IsInit (g 0)) (hfreeze : ∀ i, n ≤ i → g i = g n)
    (hacc : (wideData A).Acc (g n).state)
    (hstep : ∀ i, i < n → StepWith (wideData A) (g i) (g (i + 1)) (tr i)) :
    letI := tileStrR A
    (wideTileData (TilePt A)).IsCorridor n (tableCorridor g tr n) := by
  letI := tileStrR A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every cell carries a tile
    intro k x _ hx
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
    rw [tableCorridor_tpCol]
    exact tpTile_tileAt hstep k _
  · -- the bottom row is the initial tape
    exact fun x hx => first_tableCorridor hwf hstep hinit hx
  · -- the leftmost column
    intro k x _ hmin
    obtain rfl : x = Sum.inl (tpCol (fun _ : A => False)) := eq_bot_of_minPos hwf.1 hmin
    rw [tableCorridor_tpCol]
    exact tpEdgeL_tileAt hwf.1 hstep (minPos_wpLe hwf.1) _
  · -- the rightmost column
    intro k x _ hmax
    obtain rfl : x = Sum.inl (tpCol (fun _ : A => True)) := eq_top_of_maxPos hwf.1 hmax
    rw [tableCorridor_tpCol]
    exact tpEdgeR_tileAt hwf.1 hstep (maxPos_wpLe hwf.1) _
  · -- neighbors in a row agree
    intro k x x' _ hsucc
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hsucc.1
    obtain ⟨t, rfl⟩ := exists_tpCol_of_posn hsucc.2.1
    rw [tableCorridor_tpCol, tableCorridor_tpCol]
    exact tpHoriz_tileAt hwf.1 hstep
      ((succPos_wpLe_iff hwf.1 s t).mpr ((succPos_tpCol hwf.1 s t).mp hsucc)) k
  · -- one row becomes the next
    intro k x _ hx
    obtain ⟨s, rfl⟩ := exists_tpCol_of_posn hx
    rw [tableCorridor_tpCol, tableCorridor_tpCol]
    exact tpVert_tileAt hstep hfreeze k _
  · -- the accepting configuration's cell carries an accepting tile
    have hposn : (wideData A).Posn (g n).head :=
      head_posn hinit hfreeze hstep n
    obtain ⟨c, hc⟩ : ∃ c : A → Prop, (g n).head = Sum.inl c := by
      rcases h : (g n).head with u | x
      · exact ⟨u, rfl⟩
      · rw [h] at hposn
        exact hposn.elim
    refine ⟨Sum.inl (tpCol c), fun p hp => tpCol_dig_of_mem hp, ?_⟩
    rw [tableCorridor_tpCol, ← hc]
    exact tpAcc_tileAt hacc

/-- **The emitted corridor can be tiled when the machine accepts in bounded
space.** -/
theorem corridorTileable_of_acceptsSpace (hwf : WideWF A) (h : (wideData A).AcceptsSpace) :
    letI := tileStrR A
    (wideTileData (TilePt A)).WellFormed ∧
      (wideTileData (TilePt A)).CorridorTileable := by
  letI := tileStrR A
  obtain ⟨g, tr, n, hinit, hfreeze, hacc, hstep⟩ := exists_runDataSpace h
  exact ⟨wideTileData_wellFormed (isLinOrd_tpLe hwf.1),
    n, tableCorridor g tr n, isCorridor_tableCorridor hwf hinit hfreeze hacc hstep⟩

end Yes

/-! ### A corridor is an accepting run in bounded space -/

section No

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

/-- **A tiling of the emitted corridor is an accepting run of the machine.**
The columns are the machine's addresses and the rows its configurations, exactly
as for the square; what the corridor drops is the clock. -/
theorem wideAcceptSpace_of_corridorTileable
    (hwf0 : letI := tileStrR A; (wideTileData (TilePt A)).WellFormed)
    (h : letI := tileStrR A; (wideTileData (TilePt A)).CorridorTileable) :
    WideWF A ∧ (wideData A).AcceptsSpace := by
  letI := tileStrR A
  classical
  obtain ⟨hgt, τ, htiles, hfst, hel, her, hhor, hver, xa, hxa, hacc⟩ := h
  have hlin : IsLinOrd (WMLe (A := A)) := isLinOrd_of_tileWF hwf0.1
  have hposn : ∀ s : A → Prop, (wideTileData (TilePt A)).Posn (Sum.inl (tpCol s)) :=
    fun s q hq => tpCol_dig_of_mem hq
  have hcorner : (wideTileData (TilePt A)).Start (τ 0 (Sum.inl (tpCol (fun _ : A => False)))) :=
    (hfst _ (hposn _)).1 (minPos_tpCol_bot hlin)
  haveI : Nonempty (TilePt A) := by
    rcases hp : τ 0 (Sum.inl (tpCol (fun _ : A => False))) with u | t
    · rw [hp] at hcorner
      exact hcorner.elim
    · exact ⟨t⟩
  have hwf : WideWF A := (wpMark_elt hcorner).1
  refine ⟨hwf, ?_⟩
  obtain ⟨c, hc⟩ := exists_tpCol_of_posn hxa
  refine acceptsSpace_of_tileRun
    { rows := hgt + 1
      tl := fun k s => wpElt (τ (min k hgt) (Sum.inl (tpCol s)))
      tile := fun k s => wpMark_elt (htiles _ _ (Nat.min_le_right k hgt) (hposn s))
      start := ?_
      first := ?_
      edgeL := fun k =>
        wpMark_elt (hel _ _ (Nat.min_le_right k hgt) (minPos_tpCol_bot hlin))
      edgeR := fun k =>
        wpMark_elt (her _ _ (Nat.min_le_right k hgt) (maxPos_tpCol_top hlin))
      horiz := fun k s t hi =>
        wpAttr_elt (hhor _ _ _ (Nat.min_le_right k hgt) ((succPos_tpCol hlin s t).mpr hi))
      vert := ?_
      accRow := hgt
      accCol := c
      accRow_lt := Nat.lt_succ_self hgt
      acc := ?_ } hwf (fun x b hc => hc.elim) ?_
  · -- the corner carries the machine's start
    exact wpMark_elt hcorner
  · -- and every other column of the bottom row the initial tape
    intro s hs
    have hnotmin : ¬MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn
        (Sum.inl (tpCol s)) := by
      intro hmin
      exact hs (tpCol_injective (Sum.inl.inj (eq_bot_of_minPos hlin hmin)))
    have htile := htiles 0 _ (Nat.zero_le _) (hposn s)
    have heq := eq_inr_of_wpMark htile
    have hzero : min 0 hgt = 0 := Nat.min_eq_left (Nat.zero_le _)
    rw [hzero]
    rcases (hfst _ (hposn s)).2 hnotmin with hf | ⟨hno, hb⟩
    · rw [heq] at hf
      obtain ⟨x, hdown, hdig, hnh, hinp⟩ := (wtpFirst_tpColR hwf.2.2.1 s _).mp hf
      refine ⟨hnh, ?_⟩
      rcases hinp with hinp | ⟨hnoinp, hblank⟩
      · exact Or.inl ⟨x, hdown, hinp⟩
      · refine Or.inr ⟨fun b hcb => ?_, hblank⟩
        rcases b with u | y
        · exact hcb.elim
        · obtain ⟨z, hdz, hz⟩ := hcb
          exact hnoinp y ((wmDown_unique hlin hdz hdown) ▸ hz)
    · refine ⟨(wpMark_elt hb).1, Or.inr ⟨fun b hcb => ?_, (wpMark_elt hb).2⟩⟩
      rcases b with u | y
      · exact hcb.elim
      · obtain ⟨z, hdz, hz⟩ := hcb
        exact hno (Sum.inr (TileTag.sym, ![y, y, y]))
          ((wtpFirst_tpColR hwf.2.2.1 s _).mpr
            ⟨z, hdz, tpDig_isDig z, Or.inl rfl, Or.inl hz⟩)
  · -- one row becomes the next
    intro k s hk
    have hk' : k < hgt := by omega
    rw [Nat.min_eq_left (le_of_lt hk'), Nat.min_eq_left hk']
    exact wpAttr_elt (hver k _ hk' (hposn s))
  · -- the accepting cell
    rw [Nat.min_self, ← hc]
    exact wpMark_elt hacc
  · -- the empty address is no cell of the ruler
    intro b hcb
    rcases b with u | y
    · exact hcb.elim
    · obtain ⟨z, hdz, -⟩ := hcb
      exact absurd ((hdz z).mpr (hlin.1 z)) (fun hcc => hcc)

end No

end TilingHard

/-! ### The reduction and the completeness -/

section Reduction

open TilingHard

/-- **The interpreted structure is a yes-instance exactly when the emitted one
is.** -/
theorem wideCorridor_map_iff (A : Type) [Language.wide.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] :
    letI := tileStrR A
    (WideCorridor (tileInterpR.Map A) ↔ WideCorridor (TilePt A)) :=
  letI := tileStrR A
  WideCorridor.iso_invariant (tileEquivR A)

/-- **A wide machine bounded in space is drawn as a tiling of the emitted
corridor.** The drawing is the square's; what the corridor drops is the clock,
which is the one thing a space-bounded machine does not have. -/
noncomputable def wideAcceptSpace_ordered_fo_reduction_wideCorridor :
    WideAcceptSpace ≤ᶠᵒ[≤] WideCorridor where
  Tag := TileTag
  dim := 3
  toInterpretation := tileInterpR
  correct := fun A _ _ _ _ => by
    letI := tileStrR A
    haveI : Finite (TilePt A) := inferInstance
    haveI : Nonempty (TilePt A) := ⟨(TileTag.dig, fun _ => Classical.arbitrary A)⟩
    refine Iff.trans ?_ (wideCorridor_map_iff A).symm
    constructor
    · rintro ⟨hwf, hacc⟩
      exact corridorTileable_of_acceptsSpace (wideData_wellFormed_iff.mp hwf) hacc
    · intro h
      obtain ⟨hwf, hacc⟩ := wideAcceptSpace_of_corridorTileable h.1 h.2
      exact ⟨wideData_wellFormed_iff.mpr hwf, hacc⟩

/-- **Tiling a wide corridor is EXPSPACE-hard**: the space-bounded wide machine
is, and it is drawn as one. -/
theorem wideCorridor_EXPSPACE_hard : EXPSPACE.Hard WideCorridor :=
  EXPSPACE.hard_of_orderedReduction wideAcceptSpace_ordered_fo_reduction_wideCorridor
    wideAcceptSpace_EXPSPACE_hard

/-- **Tiling a wide corridor is EXPSPACE-complete.** The membership half is
`DescriptiveComplexity.wideCorridor_mem_EXPSPACE`: a wide corridor is an
ordinary corridor of an exponential expansion, and that problem is a walk on
rows, hence in PSPACE. -/
theorem wideCorridor_EXPSPACE_complete : EXPSPACE.Complete WideCorridor :=
  ⟨wideCorridor_mem_EXPSPACE, wideCorridor_EXPSPACE_hard⟩

end Reduction

end DescriptiveComplexity
