/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSub

/-!
# The two ends of a program's run, at the pass-layer presentation

`DescriptiveComplexity.Draw.Table.isInit` and
`DescriptiveComplexity.Draw.Table.acceptsSpace` state the two ends of a run at
an arbitrary tape function; a program's phases are all stated at the
`DescriptiveComplexity.Draw.Prog.trackTapeAt` presentation. This file joins them.

`DescriptiveComplexity.Draw.Prog.initBack` is the background at time zero – the
mark of the cell's element on the register file, the blank everywhere else –
and `DescriptiveComplexity.Draw.Prog.trackTape_initBack` says the initial tape
*is* the presentation walking any track whose mark and blank digits are clear,
with the empty track: which is why the all-blank start needs no initialisation
sweep. On top of it, `DescriptiveComplexity.Draw.Prog.isInit_prog` is the
initial configuration a program's first phase starts from, and
`DescriptiveComplexity.Draw.Prog.acceptsSpace_prog` /
`DescriptiveComplexity.Draw.Prog.dwideAcceptSpace_prog` are what a finished run
delivers – for the latter, together with the separation argument
(`DescriptiveComplexity.Draw.Prog.sep_of`), the two promises of
`DescriptiveComplexity.DWideAcceptSpace`.
-/

namespace DescriptiveComplexity

namespace Draw

namespace Prog

open FirstOrder

open Language Structure

variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable (PR : Prog A R P Q W K dd)

/-! ### The background at time zero -/

open Classical in
/-- **The background at time zero**: the mark of the cell's element on the
register file, the blank everywhere else. -/
noncomputable def initBack : (Univ A R P K dd → Prop) → W → A := fun r s =>
  if h : ∃ x : Univ A R P K dd, r = wmSeg x then PR.mark h.choose s else PR.blank s

variable {PR}

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] in
/-- On a register cell the background is the mark. -/
theorem initBack_wmSeg (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (x : Univ A R P K dd) : PR.initBack (wmSeg x) = PR.mark x := by
  funext s
  rw [initBack, dif_pos ⟨x, rfl⟩]
  have hspec := (⟨x, rfl⟩ : ∃ y : Univ A R P K dd, wmSeg x = wmSeg y).choose_spec
  rw [show (⟨x, rfl⟩ : ∃ y : Univ A R P K dd, wmSeg x = wmSeg y).choose = x from
    (wmSeg_injective hlin hspec).symm]

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- Off the register file the background is the blank. -/
theorem initBack_of_not_reg {r : Univ A R P K dd → Prop}
    (hno : ∀ x : Univ A R P K dd, r ≠ wmSeg x) : PR.initBack r = PR.blank := by
  funext s
  rw [initBack, dif_neg fun hc => hno _ hc.choose_spec]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The initial tape is the pass-layer presentation**, walking any track
whose mark and blank digits are clear, with the empty track: the all-blank
start needs no initialisation sweep. -/
theorem trackTape_initBack {t₀ : W}
    (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero) (hb : PR.blank t₀ = PR.zero) :
    PR.trackTapeAt wmSeg t₀ PR.initBack (fun _ => False) =
      fun r => PR.syElt (PR.initBack r) := by
  funext r
  refine congrArg PR.syElt (funext fun s => ?_)
  change (if s = t₀ then bitVal PR.zero PR.one (regBit (fun _ => False) r)
    else PR.initBack r s) = PR.initBack r s
  by_cases hs : s = t₀
  · subst hs
    rw [if_pos rfl, bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)]
    rw [initBack]
    split
    · exact (hmk _).symm
    · exact hb.symm
  · rw [if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **The initial tape does not depend on which file presents it**: the same
statement at an arbitrary file. Nothing of the file is read – the walked track
is empty, so the only cell-dependent part of the presentation is a bit that is
`False` wherever the head is – and that is what lets a clocked program, whose
file is not the channel's and does not exist yet at time zero, start its opening
in the presentation the rest of its run is stated in. -/
theorem trackTapeAt_initBack {J : Type} (cell : J → (Univ A R P K dd → Prop))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) :
    PR.trackTapeAt cell t₀ PR.initBack (fun _ => False) =
      fun r => PR.syElt (PR.initBack r) := by
  funext r
  refine congrArg PR.syElt (funext fun s => ?_)
  change (if s = t₀ then bitVal PR.zero PR.one (bitAtOf cell (fun _ => False) r)
    else PR.initBack r s) = PR.initBack r s
  by_cases hs : s = t₀
  · subst hs
    rw [if_pos rfl, bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc)]
    rw [initBack]
    split
    · exact (hmk _).symm
    · exact hb.symm
  · rw [if_neg hs]

omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **Two files present the initial tape alike**: both are the marks over the
blank, read cell by cell. The clocked program's opening is stated at its own
file and `DescriptiveComplexity.Draw.Prog.isInit_prog` at the channel's, and this
is the one step between them. -/
theorem trackTapeAt_initBack_eq {J : Type} (cell : J → (Univ A R P K dd → Prop))
    {t₀ t₁ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero)
    (hmk₁ : ∀ x : Univ A R P K dd, PR.mark x t₁ = PR.zero)
    (hb₁ : PR.blank t₁ = PR.zero) :
    PR.trackTapeAt cell t₀ PR.initBack (fun _ => False) =
      PR.trackTapeAt wmSeg t₁ PR.initBack (fun _ => False) :=
  (trackTapeAt_initBack cell hmk hb).trans (trackTape_initBack hmk₁ hb₁).symm

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **A program may decline the input channel's marks.** What a marked cell
carries is the program's own field, so a program that wants a blank tape at time
zero takes `mark` to be the blank, and then the background at time zero is the
blank everywhere – no cell of the channel's ruler is distinguishable from any
other.

That is what a *clocked* program does. It cannot afford the ruler
(`DescriptiveComplexity.Problems.Wide.Marks`), it builds its own file low on the
tape, and if the channel's marks were still there it would have to say at every
step that it has not mistaken one for a register of its own. Declining them
removes the question. -/
theorem initBack_of_mark_blank (hmk : ∀ x : Univ A R P K dd, PR.mark x = PR.blank)
    (r : Univ A R P K dd → Prop) : PR.initBack r = PR.blank := by
  classical
  funext s
  change (if h : ∃ x : Univ A R P K dd, r = wmSeg x then PR.mark h.choose s
    else PR.blank s) = PR.blank s
  split
  · exact congrFun (hmk _) s
  · rfl

/-! ### The two ends of a run -/

/-- **The initial configuration of a program**: its start phase and pointer,
the head on the empty address, the tape presenting the marks with any clear
track walked. -/
theorem isInit_prog (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) :
    (wideData (Univ A R P K dd)).IsInit
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ := by
  rw [trackTape_initBack hmk hb]
  exact PR.table.isInit hR hall
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- A program's accepting states are the table's. -/
theorem accept_table {p : P} {f : Q → A} (h : PR.accept p f) :
    PR.table.accept p (stPl (W := W) PR.zero f) := by
  have he : (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) = f :=
    funext fun q => by
      rw [stPl, unslot_slotPl]
      exact stVec_inl f q
  change PR.accept p fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)
  rw [he]
  exact h

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **And conversely**: a state the table accepts is one the program accepts.
The pointer is recovered from the payload by the same equation, which is what a
*backward* reading needs – it is handed an accepting configuration and has to
say what the program decided. -/
theorem accept_of_isAcc {p : P} {f : Q → A}
    (h : PR.table.IsAcc (PR.stElt p f)) : PR.accept p f := by
  have h2 : PR.table.accept p (stPl (W := W) PR.zero f) := by
    have h3 : PR.table.accept p
        (unpad PR.table.payload_le (pad PR.zero (stPl (W := W) PR.zero f))) := h.2
    rwa [unpad_pad] at h3
  have he : (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) = f :=
    funext fun q => by
      rw [stPl, unslot_slotPl]
      exact stVec_inl f q
  change PR.accept p (fun q => unslot (stPl (W := W) PR.zero f) (Sum.inl q)) at h2
  rwa [he] at h2

/-- **A program's run accepts in bounded space**: start as
`DescriptiveComplexity.Draw.Prog.isInit_prog` says, roam, and end in a phase and
pointer the program accepts. -/
theorem acceptsSpace_prog (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : (wideData (Univ A R P K dd)).AcceptsSpace := by
  rw [trackTape_initBack hmk hb] at hreach
  exact PR.table.acceptsSpace hR hall
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))
    hreach hstate (accept_table ha)

/-- **A program's run accepts on the clock**: start as
`DescriptiveComplexity.Draw.Prog.isInit_prog` says, run for fewer steps than there
are addresses, and end in a phase and pointer the program accepts. -/
theorem accepts_prog (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : (wideData (Univ A R P K dd)).Accepts := by
  rw [trackTape_initBack hmk hb] at hreach
  exact PR.table.accepts hR hall
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))
    hreach hlt hstate (accept_table ha)

/-- **A program's run makes its instance a yes-instance of
`DescriptiveComplexity.WideAccept`**: well-formedness, which is free, and an
accepting run within the clock. A program that guesses produces this and not
`DescriptiveComplexity.Draw.Prog.dwideAcceptSpace_prog`, which asks for
determinism. -/
theorem wideAccept_prog (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {n : ℕ} {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : (wideData (Univ A R P K dd)).ReachesIn n
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    (hlt : n < 2 ^ Nat.card (Univ A R P K dd))
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : WideAccept (Univ A R P K dd) :=
  ⟨PR.table.wellFormed hR, accepts_prog hR hlin hall hmk hb hreach hlt hstate ha⟩

/-- **A program's run makes its instance a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`**: the two promises – well-formedness
for free, determinism from the separation argument – and the accepting run. -/
theorem dwideAcceptSpace_prog (hR : PR.table.Reads)
    (hall : ∀ x : Univ A R P K dd, PR.marked x)
    (hsep : ∀ (r r' : R) (f : Q → A) (g : W → A), (PR.rules r).guard f g →
      (PR.rules r').guard f g → (PR.rules r).srcPh = (PR.rules r').srcPh → r = r')
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTapeAt wmSeg t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : DWideAcceptSpace (Univ A R P K dd) :=
  ⟨PR.table.wellFormed hR, PR.table.deterministic hR (PR.sep_of hsep),
    acceptsSpace_prog hR hlin hall hmk hb hreach hstate ha⟩

end Prog

end Draw

end DescriptiveComplexity
