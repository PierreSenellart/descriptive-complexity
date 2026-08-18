/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannelTape
import DescriptiveComplexity.Problems.Wide.DrawInit

/-!
# A program's run at the register channel

`DescriptiveComplexity.Draw.Prog.wideAccept_prog` turns a program's run into a
yes-instance of `DescriptiveComplexity.WideAccept`, whose channel writes for
every element. This file is the same statement at the **register channel**,
where a program writes for the elements it marks and the file it is handed has
one register per such element.

The marking is what a program says about its own channel: `Prog.marked` is a
field, `fun _ => True` by default, and the two ends of a run read it. At the
segment channel the program marks everything and the file is the ruler; at the
register channel it marks its argument elements and the file lies in the working
region (`DescriptiveComplexity.wideRank_wmRegSeg_lt`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Table

variable {A R P K : Type} {c dd : ℕ} {T : Table A R P K c dd}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The elements the channel writes for are the ones the table marks**: the
instance's input relation is the table's, and the table's holds at `x` exactly
when `x` is marked. -/
theorem wmHasInp_iff_marked (hR : T.Reads) (x : Univ A R P K dd) :
    WMHasInp x ↔ T.Marked x :=
  ⟨fun ⟨_a, ha⟩ => ((hR.inp _ _).mp ha).1,
    fun hm => ⟨symElt T.zero (T.markPl x), (hR.inp _ _).mpr ⟨hm, rfl⟩⟩⟩

/-- **The emitted machine accepts on the clock at the register channel**: the
reading of `DescriptiveComplexity.Draw.Table.accepts` whose marks sit on the file
of the elements the table writes for. -/
theorem acceptsReg (hR : T.Reads) {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, T.Marked x →
      f (wmRegSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop,
      (∀ x : Univ A R P K dd, T.Marked x → s ≠ wmRegSeg x) →
      f s = symElt T.zero T.blankPl)
    {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {w : Fin c → A} (hstate : cfg.state = Sum.inr (stateElt T.zero p w))
    (ha : T.accept p w) :
    (wideRegData (Univ A R P K dd)).Accepts :=
  accepts_of_wideRegTape_lt_two_pow (T.isLinOrd_wmLe hR) ((hR.blank _).mpr rfl)
    (fun x hx => (hR.inp x _).mpr ⟨(wmHasInp_iff_marked hR x).mp hx, rfl⟩)
    (fun x hx => hmark x ((wmHasInp_iff_marked hR x).mp hx))
    (fun s hno => hrest s fun x hx => hno x ((wmHasInp_iff_marked hR x).mpr hx))
    ((hR.start _).mpr rfl) hreach hlt hstate ((hR.acc _).mpr (T.isAcc_stateElt ha))

/-- **And backwards**: a yes-instance's accepting run starts at the *canonical*
initial configuration – the start state, the empty address, and the tape the
channel wrote – because a well-formed machine with one start state has one
initial configuration (`TMData.isInit_unique`). This is where a backward reading
of an accepting run gets the run it walks. -/
theorem exists_reachesIn_of_acceptsReg (hR : T.Reads)
    {f : (Univ A R P K dd → Prop) → Univ A R P K dd}
    (hmark : ∀ x : Univ A R P K dd, T.Marked x →
      f (wmRegSeg x) = symElt T.zero (T.markPl x))
    (hrest : ∀ s : Univ A R P K dd → Prop,
      (∀ x : Univ A R P K dd, T.Marked x → s ≠ wmRegSeg x) →
      f s = symElt T.zero T.blankPl)
    (hwf : (wideRegData (Univ A R P K dd)).WellFormed)
    (hacc : (wideRegData (Univ A R P K dd)).Accepts) :
    ∃ (n : ℕ) (cfg : Config (WPoint (Univ A R P K dd))),
      n < Nat.card {p : WPoint (Univ A R P K dd) //
        (wideData (Univ A R P K dd)).Posn p} ∧
      (wideData (Univ A R P K dd)).StepsIn n
        ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
          wideTape f (symElt T.zero T.blankPl)⟩ cfg ∧
      (wideData (Univ A R P K dd)).Acc cfg.state := by
  obtain ⟨c₀, c, n, hinit, hlt, hrun, hcacc⟩ := hacc
  -- the canonical initial configuration
  have hcanon : (wideRegData (Univ A R P K dd)).IsInit
      ⟨Sum.inr (stateElt T.zero T.startPh T.startPl), Sum.inl fun _ => False,
        wideTape f (symElt T.zero T.blankPl)⟩ :=
    isInit_wideRegTape (T.isLinOrd_wmLe hR) ((hR.blank _).mpr rfl)
      (fun x hx => (hR.inp x _).mpr ⟨(wmHasInp_iff_marked hR x).mp hx, rfl⟩)
      (fun x hx => hmark x ((wmHasInp_iff_marked hR x).mp hx))
      (fun s hno => hrest s fun x hx => hno x ((wmHasInp_iff_marked hR x).mpr hx))
      ((hR.start _).mpr rfl)
  -- there is only one, the start state being pinned by the table
  have hstart : ∀ q q' : WPoint (Univ A R P K dd),
      (wideRegData (Univ A R P K dd)).Start q →
      (wideRegData (Univ A R P K dd)).Start q' → q = q' := by
    rintro (s | q) (s' | q') h h'
    · exact h.elim
    · exact h.elim
    · exact h'.elim
    · exact congrArg Sum.inr (((hR.start q).mp h).trans ((hR.start q').mp h').symm)
  have heq : c₀ = ⟨Sum.inr (stateElt T.zero T.startPh T.startPl),
      Sum.inl fun _ => False, wideTape f (symElt T.zero T.blankPl)⟩ :=
    TMData.isInit_unique hwf hstart hinit hcanon
  rw [heq] at hrun
  exact ⟨n, c, hlt, (wideRegData_stepsIn n _ _).mp hrun, hcacc⟩

end Table

namespace Prog

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable (PR : Prog A R P Q W K dd)

open Classical in
/-- **The background at time zero, at the register channel**: the mark of the
element whose cell it is, for the elements the program writes for, and the blank
at every other address. -/
noncomputable def initBackReg : (Univ A R P K dd → Prop) → W → A := fun r s =>
  if h : ∃ x : Univ A R P K dd, PR.marked x ∧ r = wmRegSeg x then PR.mark h.choose s
  else PR.blank s

variable {PR}

omit [DecidableEq W] in
/-- On a register cell the background is that register's mark: two marked
elements with the same cell are equal (`wmRegSeg_injOn`). -/
theorem initBackReg_wmRegSeg (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (hR : PR.table.Reads) {x : Univ A R P K dd} (hx : PR.marked x) :
    PR.initBackReg (wmRegSeg x) = PR.mark x := by
  classical
  funext s
  rw [initBackReg, dif_pos ⟨x, hx, rfl⟩]
  have hspec := (⟨x, hx, rfl⟩ :
    ∃ y : Univ A R P K dd, PR.marked y ∧ wmRegSeg x = wmRegSeg y).choose_spec
  rw [show (⟨x, hx, rfl⟩ :
      ∃ y : Univ A R P K dd, PR.marked y ∧ wmRegSeg x = wmRegSeg y).choose = x from
    (_root_.DescriptiveComplexity.wmRegSeg_injOn hlin
      ((Table.wmHasInp_iff_marked hR _).mpr hspec.1)
      ((Table.wmHasInp_iff_marked hR x).mpr hx) hspec.2.symm)]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [DecidableEq W] in
/-- Off the file the background is the blank. -/
theorem initBackReg_of_not_reg {r : Univ A R P K dd → Prop}
    (hno : ∀ x : Univ A R P K dd, PR.marked x → r ≠ wmRegSeg x) :
    PR.initBackReg r = PR.blank := by
  classical
  funext s
  rw [initBackReg, dif_neg fun hc => hno _ hc.choose_spec.1 hc.choose_spec.2]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The initial tape is the pass-layer presentation**, at the register
channel: the walked track is empty, so nothing of the file is read but the cells
themselves. -/
theorem trackTape_initBackReg {t₀ : W}
    (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero) (hb : PR.blank t₀ = PR.zero) :
    PR.trackTapeAt wmRegSeg t₀ PR.initBackReg (fun _ => False) =
      fun r => PR.syElt (PR.initBackReg r) := by
  classical
  funext r
  refine congrArg PR.syElt (funext fun s => ?_)
  change (if s = t₀ then bitVal PR.zero PR.one (bitAtOf wmRegSeg (fun _ => False) r)
    else PR.initBackReg r s) = PR.initBackReg r s
  by_cases hs : s = t₀
  · subst hs
    rw [if_pos rfl, bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)]
    rw [initBackReg]
    split
    · exact (hmk _).symm
    · exact hb.symm
  · rw [if_neg hs]

/-- **A program's run accepts on the clock, at the register channel.** -/
theorem accepts_progReg (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmRegSeg t₀ PR.initBackReg fun _ => False)
          (PR.syElt PR.blank)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : (wideRegData (Univ A R P K dd)).Accepts := by
  rw [trackTape_initBackReg hmk hb] at hreach
  exact PR.table.acceptsReg hR
    (f := fun r => PR.syElt (PR.initBackReg r))
    (fun x hx => congrArg PR.syElt (initBackReg_wmRegSeg hlin hR hx))
    (fun s hno => congrArg PR.syElt (initBackReg_of_not_reg hno))
    hreach hlt hstate (accept_table ha)

/-- **And backwards, at a program**: a yes-instance of
`DescriptiveComplexity.WideRegAccept` gives a run of *this* program from the
configuration it starts in – the state it starts in, the empty address, and the
tape the channel wrote. The clock is dropped: a backward reading refutes
acceptance by determinism, and for that the length of the run does not
matter. -/
theorem exists_stepsIn_of_wideRegAccept (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero)
    (hacc : WideRegAccept (Univ A R P K dd)) :
    ∃ (n : ℕ) (cfg : Config (WPoint (Univ A R P K dd))),
      (wideData (Univ A R P K dd)).StepsIn n
        ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
          wideTape (PR.trackTapeAt wmRegSeg t₀ PR.initBackReg fun _ => False)
            (PR.syElt PR.blank)⟩ cfg ∧
      (wideData (Univ A R P K dd)).Acc cfg.state := by
  rw [trackTape_initBackReg hmk hb]
  obtain ⟨n, cfg, -, hrun, hcacc⟩ :=
    PR.table.exists_reachesIn_of_acceptsReg hR
      (f := fun r => PR.syElt (PR.initBackReg r))
      (fun x hx => congrArg PR.syElt (initBackReg_wmRegSeg hlin hR hx))
      (fun s hno => congrArg PR.syElt (initBackReg_of_not_reg hno))
      hacc.1 hacc.2
  exact ⟨n, cfg, hrun, hcacc⟩

/-- **A program's run makes its instance a yes-instance of
`DescriptiveComplexity.WideRegAccept`**: the reading a clocked reduction into
the register channel produces. -/
theorem wideRegAccept_prog (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmRegSeg t₀ PR.initBackReg fun _ => False)
          (PR.syElt PR.blank)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : WideRegAccept (Univ A R P K dd) :=
  ⟨wideRegData_wellFormed_iff.mpr
      (wideData_wellFormed_iff.mp (PR.table.wellFormed hR)),
    accepts_progReg hR hlin hmk hb hreach hlt hstate ha⟩

end Prog

end Draw

end DescriptiveComplexity
