/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingHard.Yes

/-!
# A tiling of the emitted square is an accepting run

The backward half of the hardness. A tiling is read row by row: the row of rank
`k` is the configuration at time `k`, and the whole argument is that **each row
holds at most one head, and the row above it is the step that head takes**.

## Why a row holds at most one head

A head in a row is either a head that halted below it, or one a neighbor sent:
the vertical rule lets nothing else stand above a symbol. A neighbor that sends
one is a head *moving that way*, by the horizontal rule, so the head of a row is
determined by the head of the row below it and the transition that head fires –
which is why a tile carries the transition and an arrival is a tile of its own.

The two **edge columns** are where this argument would otherwise fail, and why
`DescriptiveComplexity.TileData.EdgeL` and `EdgeR` are part of a tiling: an
arrival at the leftmost column is sent by nothing, so without a border condition
a head would appear there out of nowhere, carrying whatever state it liked.

## What is read off a row

The drawing is packaged as `DescriptiveComplexity.TilingHard.TileRun` – rows
numbered by the clock, columns the machine's addresses – so the coordinates of
the emitted square are translated once and the argument itself is a plain
induction on the row number.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace TilingHard

section Draw

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

/-- **A cell holding a head**, halted or not: the two tags an accepting tile may
carry, and the two a tiling never puts side by side. -/
def IsHeadTile (p : TilePt A) : Prop := p.1 = TileTag.head ∨ p.1 = TileTag.halt

variable (A) in
/-- **The wide machine an instance describes, at a given input description**:
the machine of `DescriptiveComplexity.wideData` with its tape described by the
given relation, which is the one thing the clocked machine and the
space-bounded one disagree on. -/
def wideDataOf (Inp : WPoint A → WPoint A → Prop) : TMData (WPoint A) :=
  { wideData A with Inp := Inp }

/-- **A drawing of a run, read at the machine's own coordinates**: the rows
numbered by time, the columns the addresses of the machine, and every condition
a tiling puts on them. The bottom row is stated as the machine's *initial
tape*, so the same drawing serves whichever way that tape is described. -/
structure TileRun (A : Type) [LinearOrder A] [Finite A] [Language.wide.Structure A]
    (Inp : WPoint A → WPoint A → Prop) where
  /-- The number of rows. -/
  rows : ℕ
  /-- The tile in a column of a row. -/
  tl : ℕ → (A → Prop) → TilePt A
  /-- Every cell carries a tile. -/
  tile : ∀ k s, TPTile (tl k s)
  /-- The corner carries the machine's start. -/
  start : TPStart (tl 0 (fun _ : A => False))
  /-- Every other column of the bottom row holds no head, and holds what the
  machine's initial tape holds there. -/
  first : ∀ s, s ≠ (fun _ : A => False) →
    TPNoHead (tl 0 s) ∧
      (Inp (Sum.inl s) (Sum.inr (tpSym (tl 0 s))) ∨
        ((∀ b, ¬Inp (Sum.inl s) b) ∧ WMBlank (tpSym (tl 0 s))))
  /-- The leftmost column carries no arrival from the left. -/
  edgeL : ∀ k, TPEdgeL (tl k (fun _ : A => False))
  /-- Nor the rightmost one an arrival from the right. -/
  edgeR : ∀ k, TPEdgeR (tl k (fun _ : A => True))
  /-- Neighbors in a row agree. -/
  horiz : ∀ k s t, WMIncr WMLe s t → TPHoriz (tl k s) (tl k t)
  /-- And one row becomes the next. -/
  vert : ∀ k s, k + 1 < rows → TPVert (tl k s) (tl (k + 1) s)
  /-- The row of the accepting cell. -/
  accRow : ℕ
  /-- And its column. -/
  accCol : A → Prop
  /-- The accepting cell is inside the square. -/
  accRow_lt : accRow < rows
  /-- And it carries an accepting tile. -/
  acc : TPAcc (tl accRow accCol)

end Draw

/-! ### Neighboring columns -/

section Columns

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable (hlin : IsLinOrd (WMLe (A := A)))

include hlin

omit [LinearOrder A] in
/-- **Every column but the last has one to its right.** -/
theorem exists_wmIncr_of_ne_top {s : A → Prop} (hs : s ≠ fun _ : A => True) :
    ∃ t, WMIncr WMLe s t := by
  classical
  refine exists_wmIncr hlin ?_
  by_contra hc
  exact hs (funext fun x => propext ⟨fun _ => trivial, fun _ => not_not.mp fun h => hc ⟨x, h⟩⟩)

omit [LinearOrder A] in
/-- **And every column but the first one to its left**, which is what justifies
an arrival that is not at the edge. -/
theorem exists_wmIncr_of_ne_bot {t : A → Prop} (ht : t ≠ fun _ : A => False) :
    ∃ s, WMIncr WMLe s t := by
  have h0 : wideRank t ≠ 0 := fun hc =>
    ht (wideRank_injective hlin (hc.trans (wideRank_bot hlin).symm))
  obtain ⟨s, hs⟩ := exists_wideRank_eq (A := A) hlin (k := wideRank t - 1)
    (lt_of_le_of_lt (Nat.sub_le _ _) (wideRank_lt_card t))
  have hne : s ≠ fun _ : A => True := by
    intro hc
    have hle : WMSetLe (WMLe (A := A)) t s := by
      rw [hc]
      exact wmSetLe_of_full hlin (fun _ => trivial) t
    have := wideRank_mono hlin hle
    omega
  obtain ⟨u, hu⟩ := exists_wmIncr_of_ne_top hlin hne
  have : wideRank u = wideRank t := by rw [wideRank_incr hlin hu, hs]; omega
  exact ⟨s, (wideRank_injective hlin this) ▸ hu⟩

omit [LinearOrder A] in
/-- **A column has one column to its left at most.** -/
theorem wmIncr_left_unique {s s' t : A → Prop} (h : WMIncr WMLe s t)
    (h' : WMIncr WMLe s' t) : s = s' := by
  refine wideRank_injective hlin ?_
  have h1 := wideRank_incr hlin h
  have h2 := wideRank_incr hlin h'
  omega

end Columns

/-! ### What stands above a cell -/

section Above

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

omit [LinearOrder A] [Finite A] in
/-- A cell holds a head or holds none. -/
theorem isHeadTile_or_noHead {p : TilePt A} (h : TPTile p) : IsHeadTile p ∨ TPNoHead p := by
  rcases hp : p.1 with _ | _ | _ | _ | _ | _
  · rw [TPTile, hp] at h
    exact h.elim
  · exact Or.inr (Or.inl hp)
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr hp)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hp))

omit [LinearOrder A] [Finite A] [Language.wide.Structure A] in
/-- And not both. -/
theorem not_isHeadTile_of_noHead {p : TilePt A} (h : TPNoHead p) : ¬IsHeadTile p := by
  rintro (hc | hc) <;> rcases h with h | h | h <;> rw [h] at hc <;>
    exact TileTag.noConfusion hc

omit [LinearOrder A] [Finite A] in
/-- **A cell that holds no head keeps its symbol**, whatever stands above it. -/
theorem tpSym_vert {p q : TilePt A} (h : TPVert p q) (hp : TPNoHead p ∨ p.1 = TileTag.halt) :
    tpSym q = tpSym p := by
  rcases hp with (hp | hp | hp) | hp <;> rw [TPVert, hp] at h
  · exact h.2
  · exact h.2.1
  · exact h.2.1
  · exact h.2.1

omit [LinearOrder A] [Finite A] in
/-- **Nothing but a head or an arrival puts a head above it**: above a symbol
stands a cell with no head, and above a head the cell the head has left. -/
theorem tag_of_head_above {p q : TilePt A} (hp : TPTile p) (h : TPVert p q)
    (hq : IsHeadTile q) :
    p.1 = TileTag.halt ∨ p.1 = TileTag.arrL ∨ p.1 = TileTag.arrR := by
  rcases hp' : p.1 with _ | _ | _ | _ | _ | _
  · rw [TPTile, hp'] at hp
    exact hp.elim
  · rw [TPVert, hp'] at h
    exact absurd hq (not_isHeadTile_of_noHead h.1)
  · rw [TPVert, hp'] at h
    exact absurd hq (not_isHeadTile_of_noHead h.1)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Above

/-! ### The head of a row comes from the row below -/

section Head

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable {Inp : WPoint A → WPoint A → Prop} (R : TileRun A Inp)
variable (hlin : IsLinOrd (WMLe (A := A)))

include hlin

/-- **Where a head comes from**: either it stood in the same column and halted,
or the head of a neighboring column moved into it – and then that head's
transition names the state it arrives in and the direction it came from. -/
theorem head_from {k : ℕ} {s : A → Prop} (hk : k + 1 < R.rows)
    (h : IsHeadTile (R.tl (k + 1) s)) :
    ((R.tl k s).1 = TileTag.halt ∧ tpState (R.tl (k + 1) s) = tpState (R.tl k s)) ∨
      (∃ e, (R.tl k e).1 = TileTag.head ∧
        ((WMRight (tpTr (R.tl k e)) ∧ WMIncr WMLe e s) ∨
          (¬WMRight (tpTr (R.tl k e)) ∧ WMIncr WMLe s e)) ∧
        WMDst (tpTr (R.tl k e)) (tpState (R.tl (k + 1) s))) := by
  have hv := R.vert k s hk
  rcases tag_of_head_above (R.tile k s) hv h with hp | hp | hp
  · rw [TPVert, hp] at hv
    exact Or.inl ⟨hp, hv.2.2⟩
  · -- an arrival from the left: the column to the left holds the head
    have hne : s ≠ fun _ : A => False := by
      intro hc
      exact R.edgeL k (hc ▸ hp)
    obtain ⟨e, he⟩ := exists_wmIncr_of_ne_bot hlin hne
    obtain ⟨-, -, -, -, harr, -, -⟩ := R.horiz k e s he
    obtain ⟨hhead, hright, hdst⟩ := harr hp
    rw [TPVert, hp] at hv
    exact Or.inr ⟨e, hhead, Or.inl ⟨hright, he⟩, hv.2.2 ▸ hdst⟩
  · -- an arrival from the right: the column to the right holds the head
    have hne : s ≠ fun _ : A => True := by
      intro hc
      exact R.edgeR k (hc ▸ hp)
    obtain ⟨e, he⟩ := exists_wmIncr_of_ne_top hlin hne
    obtain ⟨-, -, -, -, -, harr, -⟩ := R.horiz k s e he
    obtain ⟨hhead, hleft, hdst⟩ := harr hp
    rw [TPVert, hp] at hv
    exact Or.inr ⟨e, hhead, Or.inr ⟨hleft, he⟩, hv.2.2 ▸ hdst⟩

omit hlin in
/-- **The bottom row holds one head, at the corner**: the corner carries the
machine's start, and every other column the initial tape, which holds none. -/
theorem head_zero : IsHeadTile (R.tl 0 (fun _ : A => False)) := by
  rcases R.start.2.1 with ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr h

omit hlin in
/-- And it is the only one. -/
theorem eq_bot_of_head_zero {s : A → Prop} (h : IsHeadTile (R.tl 0 s)) :
    s = fun _ : A => False := by
  by_contra hs
  exact not_isHeadTile_of_noHead (R.first s hs).1 h

/-- **A row holds one head at most.** A head is either one that halted below it
or one a neighbor sent, and the neighbor that sends one is the head of the row
below moving that way; so the head of a row is determined by the head of the row
below and the transition it fires. -/
theorem head_unique : ∀ {k : ℕ}, k < R.rows → ∀ {s t : A → Prop},
    IsHeadTile (R.tl k s) → IsHeadTile (R.tl k t) → s = t := by
  intro k
  induction k with
  | zero =>
    intro _ s t hs ht
    rw [eq_bot_of_head_zero R hs, eq_bot_of_head_zero R ht]
  | succ m ih =>
    intro hm s t hs ht
    rcases head_from R hlin hm hs with ⟨hhalt, -⟩ | ⟨e, hhead, hmove, -⟩ <;>
      rcases head_from R hlin hm ht with ⟨hhalt', -⟩ | ⟨e', hhead', hmove', -⟩
    · exact ih (by omega) (Or.inr hhalt) (Or.inr hhalt')
    · -- one halted, the other was sent: the sending cell is that halt
      have hse : s = e' := ih (by omega) (Or.inr hhalt) (Or.inl hhead')
      rw [← hse, hhalt] at hhead'
      exact TileTag.noConfusion hhead'
    · have hte : t = e := ih (by omega) (Or.inr hhalt') (Or.inl hhead)
      rw [← hte, hhalt'] at hhead
      exact TileTag.noConfusion hhead
    · -- both were sent, and by the same head
      have hee : e = e' := ih (by omega) (Or.inl hhead) (Or.inl hhead')
      subst hee
      rcases hmove with ⟨hr, hi⟩ | ⟨hr, hi⟩ <;> rcases hmove' with ⟨hr', hi'⟩ | ⟨hr', hi'⟩
      · exact wmIncr_functional hlin hi hi'
      · exact absurd hr hr'
      · exact absurd hr' hr
      · exact wmIncr_left_unique hlin hi hi'

/-- **A row with a head stands on one below it**: nothing sends a head into a
row whose own row below has none. -/
theorem exists_head_below {k : ℕ} (hk : k + 1 < R.rows)
    (h : ∃ s, IsHeadTile (R.tl (k + 1) s)) : ∃ e, IsHeadTile (R.tl k e) := by
  obtain ⟨s, hs⟩ := h
  rcases head_from R hlin hk hs with ⟨hhalt, -⟩ | ⟨e, hhead, -, -⟩
  · exact ⟨s, Or.inr hhalt⟩
  · exact ⟨e, Or.inl hhead⟩

end Head

/-! ### The run a tiling draws -/

section Run

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable {Inp : WPoint A → WPoint A → Prop} (R : TileRun A Inp)
variable (hlin : IsLinOrd (WMLe (A := A)))

open Classical in
/-- **The column the head of a row stands in**, arbitrary in a row with no
head. -/
noncomputable def headCol (k : ℕ) : A → Prop :=
  if h : ∃ s, IsHeadTile (R.tl k s) then h.choose else fun _ => False

omit hlin in
/-- **A square has a row**: the accepting cell stands in one. -/
theorem rows_pos : 0 < R.rows := lt_of_le_of_lt (Nat.zero_le _) R.accRow_lt

omit hlin in
theorem headCol_spec {k : ℕ} (h : ∃ s, IsHeadTile (R.tl k s)) :
    IsHeadTile (R.tl k (headCol R k)) := by
  classical
  rw [headCol, dif_pos h]
  exact h.choose_spec

include hlin in
/-- And it is *the* column of the head. -/
theorem headCol_eq {k : ℕ} (hk : k < R.rows) {s : A → Prop}
    (hs : IsHeadTile (R.tl k s)) : headCol R k = s :=
  head_unique R hlin hk (headCol_spec R ⟨s, hs⟩) hs

include hlin in
/-- **Every other column of a row holds no head**, the head being unique. -/
theorem noHead_of_ne {k : ℕ} (hk : k < R.rows) {d : A → Prop}
    (hd : d ≠ headCol R k) : TPNoHead (R.tl k d) := by
  rcases isHeadTile_or_noHead (R.tile k d) with h | h
  · exact absurd (headCol_eq R hlin hk h).symm hd
  · exact h

variable (b₀ : A)

/-- **The configuration a row is**: the head in its column, the state that head
carries, and the symbols of the row on the tape. The control points hold a
blank, which is what the machine's initial tape asks of them. -/
noncomputable def cfgAt (k : ℕ) : Config (WPoint A) where
  state := Sum.inr (tpState (R.tl k (headCol R k)))
  head := Sum.inl (headCol R k)
  tape := fun p =>
    match p with
    | Sum.inl s => Sum.inr (tpSym (R.tl k s))
    | Sum.inr _ => Sum.inr b₀

include hlin in
/-- **The bottom row is an initial configuration**: the head at the corner in a
start state, the cell of an element carrying its input symbol and every other
cell a blank. -/
theorem isInit_cfgAt (hb : WMBlank b₀)
    (hctrl : ∀ (x : A) b, ¬Inp (Sum.inr x) b)
    (hbot : ∀ b, ¬Inp (Sum.inl fun _ : A => False) b) :
    (wideDataOf A Inp).IsInit (cfgAt R b₀ 0) := by
  have hc0 : headCol R 0 = fun _ : A => False :=
    headCol_eq R hlin (rows_pos R) (head_zero R)
  refine ⟨?_, ?_, ?_⟩
  · change WMStart (tpState (R.tl 0 (headCol R 0)))
    rw [hc0]
    exact R.start.2.2.1
  · change MinPos (wideData A).Le (wideData A).Posn (Sum.inl (headCol R 0))
    rw [hc0]
    exact minPos_wpLe hlin
  · rintro (s | x)
    · by_cases hs : s = fun _ : A => False
      · subst hs
        refine Or.inr ⟨hbot, ?_⟩
        change WMBlank (tpSym (R.tl 0 (fun _ : A => False)))
        exact R.start.2.2.2
      · exact (R.first s hs).2
    · exact Or.inr ⟨fun b hc => hctrl x b hc, hb⟩

include hlin in
/-- **The row above is the step the head takes**, or the same configuration
again where the head has halted. -/
theorem step_or_eq {k : ℕ} (hk : k + 1 < R.rows)
    (hup : ∃ s, IsHeadTile (R.tl (k + 1) s)) :
    (wideDataOf A Inp).Step (cfgAt R b₀ k) (cfgAt R b₀ (k + 1)) ∨
      cfgAt R b₀ (k + 1) = cfgAt R b₀ k := by
  obtain ⟨s, hs⟩ := hup
  have hcs : headCol R (k + 1) = s := headCol_eq R hlin hk hs
  have hsym : ∀ d : A → Prop, d ≠ headCol R k →
      tpSym (R.tl (k + 1) d) = tpSym (R.tl k d) := fun d hd =>
    tpSym_vert (R.vert k d hk) (Or.inl (noHead_of_ne R hlin (by omega) hd))
  rcases head_from R hlin hk hs with ⟨hhalt, hstate⟩ | ⟨e, hhead, hmove, hdst⟩
  · -- the head halted: the row above repeats
    right
    have hce : headCol R k = s := headCol_eq R hlin (by omega) (Or.inr hhalt)
    have hsymhalt : tpSym (R.tl (k + 1) s) = tpSym (R.tl k s) :=
      tpSym_vert (R.vert k s hk) (Or.inr hhalt)
    refine Config.ext ?_ ?_ (funext fun p => ?_)
    · change Sum.inr (tpState (R.tl (k + 1) (headCol R (k + 1)))) =
        Sum.inr (tpState (R.tl k (headCol R k)))
      rw [hcs, hce, hstate]
    · change Sum.inl (headCol R (k + 1)) = Sum.inl (headCol R k)
      rw [hcs, hce]
    · rcases p with d | y
      · change Sum.inr (tpSym (R.tl (k + 1) d)) = Sum.inr (tpSym (R.tl k d))
        by_cases hd : d = headCol R k
        · rw [hd, hce, hsymhalt]
        · rw [hsym d hd]
      · rfl
  · -- the head moved, firing the transition its tile carries
    left
    have hce : headCol R k = e := headCol_eq R hlin (by omega) (Or.inl hhead)
    have htile := R.tile k e
    rw [TPTile, hhead] at htile
    have hv := R.vert k e hk
    rw [TPVert, hhead] at hv
    refine ⟨Sum.inr (tpTr (R.tl k e)), htile.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change WMSrc (tpTr (R.tl k e)) (tpState (R.tl k (headCol R k)))
      rw [hce]
      exact htile.2.1
    · change WMRead (tpTr (R.tl k e)) (tpSym (R.tl k (headCol R k)))
      rw [hce]
      exact htile.2.2
    · change WMDst (tpTr (R.tl k e)) (tpState (R.tl (k + 1) (headCol R (k + 1))))
      rw [hcs]
      exact hdst
    · change WMWrite (tpTr (R.tl k e)) (tpSym (R.tl (k + 1) (headCol R k)))
      rw [hce]
      exact hv.2
    · rintro (d | y) hd
      · have hne : d ≠ headCol R k := by
          rw [hce]
          exact fun hc => hd (congrArg Sum.inl (hc.trans hce.symm))
        change Sum.inr (tpSym (R.tl (k + 1) d)) = Sum.inr (tpSym (R.tl k d))
        rw [hsym d hne]
      · rfl
    · rcases hmove with ⟨hr, hi⟩ | ⟨hr, hi⟩
      · refine Or.inl ⟨hr, ?_⟩
        change SuccPos (wideData A).Le (wideData A).Posn
          (Sum.inl (headCol R k)) (Sum.inl (headCol R (k + 1)))
        rw [hce, hcs]
        exact (succPos_wpLe_iff hlin e s).mpr hi
      · refine Or.inr ⟨hr, ?_⟩
        change SuccPos (wideData A).Le (wideData A).Posn
          (Sum.inl (headCol R (k + 1))) (Sum.inl (headCol R k))
        rw [hce, hcs]
        exact (succPos_wpLe_iff hlin s e).mpr hi

end Run

/-! ### The run reaches the accepting row -/

section Accepts

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]
variable {Inp : WPoint A → WPoint A → Prop} (R : TileRun A Inp)
variable (hlin : IsLinOrd (WMLe (A := A))) (b₀ : A)

include hlin

/-- **A row with a head stands a bounded number of steps above the bottom
row**: each row below it is either the step its head takes or the same
configuration again, where that head has halted. -/
theorem stepsIn_cfgAt : ∀ {k : ℕ}, k < R.rows → (∃ s, IsHeadTile (R.tl k s)) →
    ∃ j ≤ k, (wideDataOf A Inp).StepsIn j (cfgAt R b₀ 0) (cfgAt R b₀ k) := by
  intro k
  induction k with
  | zero => exact fun _ _ => ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    intro hk hup
    obtain ⟨j, hj, hrun⟩ := ih (by omega) (exists_head_below R hlin hk hup)
    rcases step_or_eq R hlin b₀ hk hup with hstep | heq
    · exact ⟨j + 1, by omega, TMData.stepsIn_succ_iff.mpr ⟨_, hrun, hstep⟩⟩
    · refine ⟨j, by omega, ?_⟩
      rw [heq]
      exact hrun

omit hlin in
include R in
/-- **A drawing is an accepting run of the machine**: the accepting cell holds a
head, so the row it stands in is a configuration the run reaches, in fewer steps
than there are addresses. -/
theorem accepts_of_tileRun (hwf : WideWF A)
    (hctrl : ∀ (x : A) b, ¬Inp (Sum.inr x) b)
    (hbot : ∀ b, ¬Inp (Sum.inl fun _ : A => False) b)
    (hrows : R.rows ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) :
    (wideDataOf A Inp).Accepts := by
  obtain ⟨b₀, hb⟩ := hwf.2.2.1
  have hhead : IsHeadTile (R.tl R.accRow R.accCol) := R.acc.1
  obtain ⟨j, hj, hrun⟩ :=
    stepsIn_cfgAt R hwf.1 b₀ R.accRow_lt ⟨R.accCol, hhead⟩
  refine ⟨cfgAt R b₀ 0, cfgAt R b₀ R.accRow, j,
    isInit_cfgAt R hwf.1 b₀ hb hctrl hbot, ?_, hrun, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt hj R.accRow_lt) hrows
  · change WMAcc (tpState (R.tl R.accRow (headCol R R.accRow)))
    rw [headCol_eq R hwf.1 R.accRow_lt hhead]
    exact R.acc.2

omit hlin in
include R in
/-- **And an accepting run in bounded space**, where the drawing has no clock to
answer to: the same run, with its length forgotten. -/
theorem acceptsSpace_of_tileRun (hwf : WideWF A)
    (hctrl : ∀ (x : A) b, ¬Inp (Sum.inr x) b)
    (hbot : ∀ b, ¬Inp (Sum.inl fun _ : A => False) b) :
    (wideDataOf A Inp).AcceptsSpace := by
  obtain ⟨b₀, hb⟩ := hwf.2.2.1
  have hhead : IsHeadTile (R.tl R.accRow R.accCol) := R.acc.1
  obtain ⟨j, -, hrun⟩ :=
    stepsIn_cfgAt R hwf.1 b₀ R.accRow_lt ⟨R.accCol, hhead⟩
  refine ⟨cfgAt R b₀ 0, cfgAt R b₀ R.accRow,
    isInit_cfgAt R hwf.1 b₀ hb hctrl hbot, TMData.reflTransGen_of_stepsIn hrun, ?_⟩
  change WMAcc (tpState (R.tl R.accRow (headCol R R.accRow)))
  rw [headCol_eq R hwf.1 R.accRow_lt hhead]
  exact R.acc.2

end Accepts

/-! ### A tiling of the emitted square, read at the machine's coordinates -/

section Translate

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

omit [Finite A] in
/-- **The order a tiling promises is the machine's own**, read at the digits:
they are one per element, and the emitted order between two of them is the
instance's. -/
theorem isLinOrd_of_tileWF
    (h : letI := tileStr A; IsLinOrd (wideTileData (TilePt A)).Le) :
    IsLinOrd (WMLe (A := A)) := by
  letI := tileStr A
  have key : ∀ x y : A, WMLe x y ↔
      (wideTileData (TilePt A)).Le (Sum.inr (tpDig x)) (Sum.inr (tpDig y)) :=
    fun x y => (tpLe_dig x y).symm
  refine ⟨fun x => (key x x).mpr (h.1 _), fun x y z h1 h2 => (key x z).mpr ?_,
    fun x y h1 h2 => ?_, fun x y => ?_⟩
  · exact h.2.1 _ _ _ ((key x y).mp h1) ((key y z).mp h2)
  · exact tpDig_injective
      (Sum.inr.inj (h.2.2.1 _ _ ((key x y).mp h1) ((key y x).mp h2)))
  · rcases h.2.2.2 (Sum.inr (tpDig x)) (Sum.inr (tpDig y)) with hc | hc
    · exact Or.inl ((key x y).mpr hc)
    · exact Or.inr ((key y x).mpr hc)

open Classical in
/-- **The address of a given rank**, which is how the rows of the square are
numbered by the clock. -/
noncomputable def rowAt (k : ℕ) : A → Prop :=
  if h : ∃ s : A → Prop, wideRank s = k then h.choose else fun _ => False

variable (hlin : IsLinOrd (WMLe (A := A)))

include hlin

omit [LinearOrder A] in
theorem wideRank_rowAt {k : ℕ} (hk : k < Nat.card {p : WPoint A // (wideData A).Posn p}) :
    wideRank (rowAt (A := A) k) = k := by
  classical
  have hex : ∃ s : A → Prop, wideRank s = k := exists_wideRank_eq hlin hk
  rw [rowAt, dif_pos hex]
  exact hex.choose_spec

omit [LinearOrder A] in
/-- The bottom row is the empty address, where the machine's head starts. -/
theorem rowAt_zero : rowAt (A := A) 0 = fun _ : A => False := by
  classical
  have hex : ∃ s : A → Prop, wideRank s = 0 := ⟨fun _ => False, wideRank_bot hlin⟩
  rw [rowAt, dif_pos hex]
  exact wideRank_injective hlin (hex.choose_spec.trans (wideRank_bot hlin).symm)

omit [LinearOrder A] in
/-- And one row above another is the increment of its address. -/
theorem wmIncr_rowAt {k : ℕ}
    (hk : k + 1 < Nat.card {p : WPoint A // (wideData A).Posn p}) :
    WMIncr WMLe (rowAt (A := A) k) (rowAt (A := A) (k + 1)) := by
  have hk' : k < Nat.card {p : WPoint A // (wideData A).Posn p} := by omega
  have hr := wideRank_rowAt hlin hk'
  have hr' := wideRank_rowAt hlin hk
  have hne : rowAt (A := A) k ≠ fun _ : A => True := by
    intro hc
    have hle : WMSetLe (WMLe (A := A)) (rowAt (A := A) (k + 1)) (rowAt (A := A) k) := by
      rw [hc]
      exact wmSetLe_of_full hlin (fun _ => trivial) _
    have := wideRank_mono hlin hle
    omega
  obtain ⟨u, hu⟩ := exists_wmIncr_of_ne_top hlin hne
  have : wideRank u = wideRank (rowAt (A := A) (k + 1)) := by
    rw [wideRank_incr hlin hu, hr, hr']
  exact (wideRank_injective hlin this) ▸ hu

end Translate

/-! ### The backward half -/

section Backward

variable {A : Type} [LinearOrder A] [Finite A] [Language.wide.Structure A]

/-- **A tiling of the emitted square is an accepting run of the machine.** The
square's coordinates are the machine's addresses, so a row is a configuration
and the row above it the step its head takes; the promises the machine owes are
carried by the start tile at the corner. -/
theorem wideRegAccept_of_tileable
    (hwf0 : letI := tileStr A; (wideTileData (TilePt A)).WellFormed)
    (h : letI := tileStr A; (wideTileData (TilePt A)).Tileable) :
    WideWF A ∧ (wideRegData A).Accepts := by
  letI := tileStr A
  classical
  obtain ⟨τ, htiles, hfst, hel, her, hhor, hver, x₀, y₀, hx₀, hy₀, hacc⟩ := h
  have hlin : IsLinOrd (WMLe (A := A)) := isLinOrd_of_tileWF hwf0.1
  have hposn : ∀ s : A → Prop, (wideTileData (TilePt A)).Posn (Sum.inl (tpCol s)) :=
    fun s q hq => tpCol_dig_of_mem hq
  have hbot : (Sum.inl (tpCol (fun _ : A => False)) : WPoint (TilePt A)) =
      Sum.inl (tpCol (rowAt (A := A) 0)) := by rw [rowAt_zero hlin]
  -- the corner carries a start tile, so the emitted instance has tiles at all
  have hcorner : (wideTileData (TilePt A)).Start
      (τ (Sum.inl (tpCol (fun _ : A => False))) (Sum.inl (tpCol (fun _ : A => False)))) :=
    (hfst _ _ (hposn _) (minPos_tpCol_bot hlin)).1 (minPos_tpCol_bot hlin)
  haveI : Nonempty (TilePt A) := by
    rcases hp : τ (Sum.inl (tpCol (fun _ : A => False)))
      (Sum.inl (tpCol (fun _ : A => False))) with u | t
    · rw [hp] at hcorner
      exact hcorner.elim
    · exact ⟨t⟩
  have hwf : WideWF A := (wpMark_elt hcorner).1
  refine ⟨hwf, ?_⟩
  -- the drawing, at the machine's own coordinates
  obtain ⟨c, hc⟩ := exists_tpCol_of_posn hx₀
  obtain ⟨r, hr⟩ := exists_tpCol_of_posn hy₀
  have hrow : rowAt (A := A) (wideRank r) = r :=
    wideRank_injective hlin (wideRank_rowAt hlin (wideRank_lt_card r))
  refine accepts_of_tileRun
    { rows := Nat.card {p : WPoint A // (wideData A).Posn p}
      tl := fun k s => wpElt (τ (Sum.inl (tpCol s)) (Sum.inl (tpCol (rowAt (A := A) k))))
      tile := fun k s => wpMark_elt (htiles _ _ (hposn s) (hposn _))
      start := ?_
      first := ?_
      edgeL := fun k => wpMark_elt (hel _ _ (hposn _) (minPos_tpCol_bot hlin))
      edgeR := fun k => wpMark_elt (her _ _ (hposn _) (maxPos_tpCol_top hlin))
      horiz := fun k s t hi =>
        wpAttr_elt (hhor _ _ _ ((succPos_tpCol hlin s t).mpr hi) (hposn _))
      vert := fun k s hk =>
        wpAttr_elt (hver _ _ _ (hposn s)
          ((succPos_tpCol hlin _ _).mpr (wmIncr_rowAt hlin hk)))
      accRow := wideRank r
      accCol := c
      accRow_lt := wideRank_lt_card r
      acc := ?_ } hwf (fun x b hc => hc.elim) ?_ le_rfl
  · -- the corner carries the machine's start
    rw [← hbot]
    exact wpMark_elt hcorner
  · -- and every other column of the bottom row the initial tape
    intro s hs
    rw [← hbot]
    have hnotmin : ¬MinPos (wideTileData (TilePt A)).Le (wideTileData (TilePt A)).Posn
        (Sum.inl (tpCol s)) := by
      intro hmin
      exact hs (tpCol_injective (Sum.inl.inj (eq_bot_of_minPos hlin hmin)))
    have htile := htiles _ _ (hposn s) (hposn (fun _ : A => False))
    have heq := eq_inr_of_wpMark htile
    rcases (hfst _ _ (hposn s) (minPos_tpCol_bot hlin)).2 hnotmin with hf | ⟨hno, hb⟩
    · rw [heq] at hf
      obtain ⟨x, a, hseg, hinp, hnh, hsym⟩ := (wtpFirst_tpCol s _).mp hf
      exact ⟨hnh, Or.inl ⟨x, hseg, hsym ▸ hinp⟩⟩
    · refine ⟨(wpMark_elt hb).1, Or.inr ⟨fun b hc => ?_, (wpMark_elt hb).2⟩⟩
      rcases b with u | y
      · exact hc.elim
      · obtain ⟨x, hseg, hinp⟩ := hc
        exact hno (Sum.inr (TileTag.sym, ![y, y, y]))
          ((wtpFirst_tpCol s _).mpr ⟨x, y, hseg, hinp, Or.inl rfl, rfl⟩)
  · -- the accepting cell
    rw [hrow, ← hc, ← hr]
    exact wpMark_elt hacc
  · -- the empty address is no register cell
    intro b hc
    rcases b with u | y
    · exact hc.elim
    · obtain ⟨x, hseg, hinp⟩ := hc
      exact not_wmRegSeg_bot hlin hinp hseg

end Backward

end TilingHard

end DescriptiveComplexity
