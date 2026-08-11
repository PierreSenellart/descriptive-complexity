/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSub

/-!
# The two ends of a program's run, at the pass-layer presentation

`DescriptiveComplexity.Pfp.Table.isInit` and
`DescriptiveComplexity.Pfp.Table.acceptsSpace` state the two ends of a run at
an arbitrary tape function; a program's phases are all stated at the
`DescriptiveComplexity.Pfp.Prog.trackTape` presentation. This file joins them.

`DescriptiveComplexity.Pfp.Prog.initBack` is the background at time zero – the
mark of the cell's element on the register file, the blank everywhere else –
and `DescriptiveComplexity.Pfp.Prog.trackTape_initBack` says the initial tape
*is* the presentation walking any track whose mark and blank digits are clear,
with the empty track: which is why the all-blank start needs no initialisation
sweep. On top of it, `DescriptiveComplexity.Pfp.Prog.isInit_prog` is the
initial configuration a program's first phase starts from, and
`DescriptiveComplexity.Pfp.Prog.acceptsSpace_prog` /
`DescriptiveComplexity.Pfp.Prog.dwideAcceptSpace_prog` are what a finished run
delivers – for the latter, together with the separation argument
(`DescriptiveComplexity.Pfp.Prog.sep_of`), the two promises of
`DescriptiveComplexity.DWideAcceptSpace`.
-/

namespace DescriptiveComplexity

namespace Pfp

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
    PR.trackTape t₀ PR.initBack (fun _ => False) =
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

/-! ### The two ends of a run -/

/-- **The initial configuration of a program**: its start phase and pointer,
the head on the empty address, the tape presenting the marks with any clear
track walked. -/
theorem isInit_prog (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) :
    (wideData (Univ A R P K dd)).IsInit
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTape t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ := by
  rw [trackTape_initBack hmk hb]
  exact PR.table.isInit hR
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

/-- **A program's run accepts in bounded space**: start as
`DescriptiveComplexity.Pfp.Prog.isInit_prog` says, roam, and end in a phase and
pointer the program accepts. -/
theorem acceptsSpace_prog (hR : PR.table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTape t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : (wideData (Univ A R P K dd)).AcceptsSpace := by
  rw [trackTape_initBack hmk hb] at hreach
  exact PR.table.acceptsSpace hR
    (f := fun r => PR.syElt (PR.initBack r))
    (fun x => congrArg PR.syElt (initBack_wmSeg hlin x))
    (fun s hno => congrArg PR.syElt (initBack_of_not_reg hno))
    hreach hstate (accept_table ha)

/-- **A program's run makes its instance a yes-instance of
`DescriptiveComplexity.DWideAcceptSpace`**: the two promises – well-formedness
for free, determinism from the separation argument – and the accepting run. -/
theorem dwideAcceptSpace_prog (hR : PR.table.Reads)
    (hsep : ∀ (r r' : R) (f : Q → A) (g : W → A), (PR.rules r).guard f g →
      (PR.rules r').guard f g → (PR.rules r).srcPh = (PR.rules r').srcPh → r = r')
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
    {t₀ : W} (hmk : ∀ x : Univ A R P K dd, PR.mark x t₀ = PR.zero)
    (hb : PR.blank t₀ = PR.zero) {cfg : Config (WPoint (Univ A R P K dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt PR.startPh PR.startSt), Sum.inl fun _ => False,
        wideTape (PR.trackTape t₀ PR.initBack fun _ => False) (PR.syElt PR.blank)⟩ cfg)
    {p : P} {fq : Q → A} (hstate : cfg.state = Sum.inr (PR.stElt p fq))
    (ha : PR.accept p fq) : DWideAcceptSpace (Univ A R P K dd) :=
  ⟨PR.table.wellFormed hR, PR.table.deterministic hR (PR.sep_of hsep),
    acceptsSpace_prog hR hlin hmk hb hreach hstate ha⟩

end Prog

end Pfp

end DescriptiveComplexity
