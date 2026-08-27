/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawProg
import DescriptiveComplexity.Problems.Wide.DrawBack
import DescriptiveComplexity.Problems.Wide.DrawInit

/-!
# The runs: the program's rules are its kits' rules

Every composite of the layer discharges its run theorem from **one**
hypothesis about the program – `hrules : ∀ ρ, PR.rules (rEmb ρ) = κ.rule …`,
“my rules are among yours, under this injection of rule names”. For a
program assembled from sites
(`DescriptiveComplexity.Draw.Data.progAsm`) that hypothesis is
definitional: the rule names are the sigma of the sites' shapes, so a kit's
rule at site `i` is the program's rule at `⟨i, Sum.inl ρ⟩`, verbatim.

This file is that plumbing, one lemma per call site of the outer loop, all
`rfl`. With it, each composite's run theorem applies to the assembled
program by naming its site; what a leg then needs is only the *background*
equations, which `DescriptiveComplexity.Problems.Wide.DrawBack` proves once.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A Q : Type} (zero one : A)
variable [LinearOrder A] [Fintype Q] [Fintype dt.SlotIx]
variable (hzo : zero ≠ one)
variable (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v)
variable [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]
variable (hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd)

/-! ### The designated elements -/

@[simp]
theorem prog_zero : (dt.prog zero one hzo args hpl).zero = zero := rfl

@[simp]
theorem prog_one : (dt.prog zero one hzo args hpl).one = one := rfl

/-! ### The rules, site by site

Each lemma names a call site's rule-name injection: the site, and `Sum.inl`
into its kit's shape. -/

/-- The startup pattern write of TARGET. -/
theorem prog_rules_tgtTop (ρ : TrackRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.tgtTop, Sum.inl ρ⟩ =
      (dt.tgtTopKit (Q := Q) (P := dt.PF) one OuterPh.tgtTopP).rule zero one ρ :=
  rfl

/-- The startup seek of the working cell to the logical top. -/
theorem prog_rules_seek1 (ρ : SeekRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.seek1, Sum.inl ρ⟩ =
      (dt.seekKit (A := A) (Q := Q) (P := dt.PF) OuterPh.seek1P).rule zero one ρ :=
  rfl

/-- The startup reset of the marker to the bottom cell. -/
theorem prog_rules_reset1 (ρ : ResetRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.reset1, Sum.inl ρ⟩ =
      (ResetKit.mk (A := A) (Q := Q) (P := dt.PF) .mir .bot .wk
        OuterPh.reset1P).rule one ρ :=
  rfl

/-- The startup clear of the mirror. -/
theorem prog_rules_clearMir1 (ρ : TrackRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.clearMir1, Sum.inl ρ⟩ =
      (dt.clearMirKit (A := A) (Q := Q) (P := dt.PF) OuterPh.clearMir1P).rule
        zero one ρ :=
  rfl

/-- One round of the outer sweep. -/
theorem prog_rules_sweepAdv (ρ : AdvRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.sweepAdv, Sum.inl ρ⟩ =
      (dt.advKit (A := A) (Q := Q) (P := dt.PF) OuterPh.advP).rule zero one ρ :=
  rfl

/-- The post-sweep reset of the marker. -/
theorem prog_rules_reset2 (ρ : ResetRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.reset2, Sum.inl ρ⟩ =
      (ResetKit.mk (A := A) (Q := Q) (P := dt.PF) .mir .bot .wk
        OuterPh.reset2P).rule one ρ :=
  rfl

/-- The post-sweep clear of the mirror. -/
theorem prog_rules_clearMir2 (ρ : TrackRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.clearMir2, Sum.inl ρ⟩ =
      (dt.clearMirKit (A := A) (Q := Q) (P := dt.PF) OuterPh.clearMir2P).rule
        zero one ρ :=
  rfl

/-- The convergence sweep. -/
theorem prog_rules_compare (ρ : SweepRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.compare, Sum.inl ρ⟩ =
      (dt.compareKit (Q := Q) (P := dt.PF) one OuterPh.cmpP).rule one ρ :=
  rfl

/-- The walk home after a failed convergence sweep. -/
theorem prog_rules_homeCmp (ρ : HomeKit.HomeRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.homeCmp, Sum.inl ρ⟩ =
      (HomeKit.mk (A := A) (Q := Q) (P := dt.PF) .mir .wk
        OuterPh.homeCmpP).rule one ρ :=
  rfl

/-- The copy-back sweep. -/
theorem prog_rules_copy (ρ : WSweepRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.copy, Sum.inl ρ⟩ =
      (dt.copyKit (A := A) (Q := Q) (P := dt.PF) OuterPh.copyP).rule one ρ :=
  rfl

/-- The walk home after the copy-back. -/
theorem prog_rules_homeCopy (ρ : HomeKit.HomeRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.homeCopy, Sum.inl ρ⟩ =
      (HomeKit.mk (A := A) (Q := Q) (P := dt.PF) .mir .wk
        OuterPh.homeCopyP).rule one ρ :=
  rfl

/-- The walk home before the output evaluation. -/
theorem prog_rules_homeOut (ρ : HomeKit.HomeRule) :
    (dt.prog zero one hzo args hpl).rules ⟨.homeOut, Sum.inl ρ⟩ =
      (HomeKit.mk (A := A) (Q := Q) (P := dt.PF) .mir .wk
        OuterPh.homeOutP).rule one ρ :=
  rfl

/-! ### A rule of the assembly drives a step

The kits' discharges wrap this for their own rules; the program's bespoke
rules – the startup step, the sites' exits – cite it directly. -/

/-- **A rightward rule of the assembly is a `HasRight` witness**, at its own
destination data. -/
theorem prog_hasRight (i : dt.SF) (ρ : (dt.progAsm zero one hzo args).Sh i)
    {f : Q → A} {g : dt.SlotIx → A}
    (hg : ((dt.progAsm zero one hzo args).rule i ρ).guard f g)
    (hmr : ((dt.progAsm zero one hzo args).rule i ρ).moveRight) :
    (dt.prog zero one hzo args hpl).HasRight
      ((dt.progAsm zero one hzo args).rule i ρ).srcPh f g
      ((dt.progAsm zero one hzo args).rule i ρ).dstPh
      (((dt.progAsm zero one hzo args).rule i ρ).dstSt f g)
      (((dt.progAsm zero one hzo args).rule i ρ).wr f g) :=
  ⟨⟨i, ρ⟩, hg, rfl, rfl, rfl, rfl, hmr⟩

/-- **A leftward rule of the assembly is a `HasLeft` witness.** -/
theorem prog_hasLeft (i : dt.SF) (ρ : (dt.progAsm zero one hzo args).Sh i)
    {f : Q → A} {g : dt.SlotIx → A}
    (hg : ((dt.progAsm zero one hzo args).rule i ρ).guard f g)
    (hml : ¬((dt.progAsm zero one hzo args).rule i ρ).moveRight) :
    (dt.prog zero one hzo args hpl).HasLeft
      ((dt.progAsm zero one hzo args).rule i ρ).srcPh f g
      ((dt.progAsm zero one hzo args).rule i ρ).dstPh
      (((dt.progAsm zero one hzo args).rule i ρ).dstSt f g)
      (((dt.progAsm zero one hzo args).rule i ρ).wr f g) :=
  ⟨⟨i, ρ⟩, hg, rfl, rfl, rfl, rfl, hml⟩

/-! ### Time zero: the initial tape is the empty state's background

The pass layer walks the background of
`DescriptiveComplexity.Draw.Data.back`; the initial tape is
`DescriptiveComplexity.Draw.Prog.initBack`, the marks over the blank. They are
the same function, at the state where every register and marker is clear –
which is why the all-blank start needs no initialization sweep, and what lets
the first leg of the run be stated in the presentation all the others use. -/

/-- **The machine's state at time zero**: every register, stage track and
marker clear. -/
noncomputable def emptySt {R' P' : Type} : TapeStD dt A R' P' where
  mir := fun _ => False
  tgt := fun _ => False
  sav := fun _ => False
  val := fun _ => False
  old := fun _ _ => False
  new := fun _ _ => False
  wk := fun _ => False
  bot := fun _ => False
  ltp := fun _ => False

variable [Language.wide.Structure
  (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)]
variable [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
variable [Finite dt.KIx]

/-- **The initial tape is the empty state's background.** -/
theorem initBack_eq_back
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd))) :
    (dt.prog zero one hzo args hpl).initBack =
      dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
        (R' := dt.RIx zero one hzo args) (P' := dt.PF)) := by
  funext r s
  by_cases hr : ∃ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      r = wmSeg u
  · obtain ⟨u, rfl⟩ := hr
    rw [Prog.initBack_wmSeg hlin]
    have hbit : ∀ p : Prop, ¬p → bitVal zero one p = zero := fun _ h => bitVal_neg h
    match s with
    | .reg => exact (bitVal_pos ⟨u, rfl⟩).symm
    | .regFirst =>
      refine bitVal_congr ⟨fun h => ⟨u, rfl, h⟩, ?_⟩
      rintro ⟨v, hv, hvy⟩
      rw [wmSeg_injective hlin hv]
      exact hvy
    | .regLast =>
      refine bitVal_congr ⟨fun h => ⟨u, rfl, h⟩, ?_⟩
      rintro ⟨v, hv, hvy⟩
      rw [wmSeg_injective hlin hv]
      exact hvy
    | .blk b =>
      refine bitVal_congr ⟨fun h => ⟨u, rfl, h⟩, ?_⟩
      rintro ⟨v, hv, hvy⟩
      rw [wmSeg_injective hlin hv]
      exact hvy
    | .pdd =>
      refine bitVal_congr ⟨fun h => ⟨u, rfl, h⟩, ?_⟩
      rintro ⟨v, hv, hvy⟩
      rw [wmSeg_injective hlin hv]
      exact hvy
    | .name j =>
      change u.2 _ = _
      rw [back_name, dif_pos ⟨u, rfl⟩]
      have hspec :=
        (⟨u, rfl⟩ : ∃ v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
          wmSeg u = wmSeg v).choose_spec
      rw [show (⟨u, rfl⟩ : ∃ v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
        wmSeg u = wmSeg v).choose = u from (wmSeg_injective hlin hspec).symm]
    | .mir => exact (hbit _ (by rintro ⟨v, -, hc⟩; exact hc)).symm
    | .tgt => exact (hbit _ (by rintro ⟨v, -, hc⟩; exact hc)).symm
    | .sav => exact (hbit _ (by rintro ⟨v, -, hc⟩; exact hc)).symm
    | .val => exact (hbit _ (by rintro ⟨v, -, hc⟩; exact hc)).symm
    | .wk => exact (hbit _ not_false).symm
    | .bot => exact (hbit _ not_false).symm
    | .ltp => exact (hbit _ not_false).symm
    | .old i => exact (hbit _ not_false).symm
    | .new i => exact (hbit _ not_false).symm
  · rw [Prog.initBack_of_not_reg (fun x hc => hr ⟨x, hc⟩)]
    have hno : ∀ p : Prop, ¬p → bitVal zero one p = zero := fun _ h => bitVal_neg h
    match s with
    | .reg => exact (hno _ hr).symm
    | .regFirst => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .regLast => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .blk b => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .pdd => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .name j => exact (by rw [back_name, dif_neg hr] : _ = zero).symm
    | .mir => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .tgt => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .sav => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .val => exact (hno _ (fun h => hr ⟨h.choose, h.choose_spec.1⟩)).symm
    | .wk => exact (hno _ not_false).symm
    | .bot => exact (hno _ not_false).symm
    | .ltp => exact (hno _ not_false).symm
    | .old i => exact (hno _ not_false).symm
    | .new i => exact (hno _ not_false).symm

/-! ### The first leg: startup plants the two permanent markers

The one rule of the `start` site fires wherever it stands – it stands at the
empty address – writes the working-cell marker and the bottom mark there and
steps right, into the pattern write of TARGET. -/

/-- **The state after the startup step**: the marker and the bottom mark at
the empty address, everything else still clear. -/
noncomputable def startSt {R' P' : Type} : TapeStD dt A R' P' :=
  { dt.emptySt (A := A) (R' := R') (P' := P') with
    wk := fun r => r = fun _ => False
    bot := fun r => r = fun _ => False }

/-- **The startup step**: from the initial configuration to the entry of the
TARGET pattern write, with both markers planted at the empty address. -/
theorem step_start (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .start fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))) (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.tgtTopP .up) fun _ => zero),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.startSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))) (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  -- the two states agree away from the empty address
  have hframe : ∀ r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop,
      r ≠ (fun _ => False) →
      dt.back wmSeg zero one dt.dd0Le (dt.startSt (A := A)
        (R' := dt.RIx zero one hzo args) (P' := dt.PF)) r =
      dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
        (R' := dt.RIx zero one hzo args) (P' := dt.PF)) r := by
    intro r hr
    funext s
    match s with
    | .wk => exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
    | .bot => exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .ltp | .old _ | .new _ => rfl
  -- the written symbol is the new background at the empty address
  have hoth : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop)
      (s : dt.SlotIx), s ≠ Slot.wk → s ≠ Slot.bot →
      dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
        (R' := dt.RIx zero one hzo args) (P' := dt.PF)) r s =
      dt.back wmSeg zero one dt.dd0Le (dt.startSt (A := A)
        (R' := dt.RIx zero one hzo args) (P' := dt.PF)) r s := by
    intro r s hw hb
    match s with
    | .wk => exact absurd rfl hw
    | .bot => exact absurd rfl hb
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .ltp | .old _ | .new _ => rfl
  have hwr : Function.update (Function.update
        ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (fun _ => False) (fun _ => False)) Slot.wk one) Slot.bot one =
      (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le (dt.startSt (A := A)
          (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
        (fun _ => False) (fun _ => False) := by
    funext s
    by_cases hb : s = Slot.bot
    · subst hb
      rw [Function.update_self, Prog.passTracks_of_ne dt.bot_ne_mir]
      exact (bitVal_pos rfl).symm
    · rw [Function.update_of_ne hb]
      by_cases hw : s = Slot.wk
      · subst hw
        rw [Function.update_self, Prog.passTracks_of_ne dt.wk_ne_mir]
        exact (bitVal_pos rfl).symm
      · rw [Function.update_of_ne hw]
        by_cases hm : s = Slot.mir
        · subst hm
          change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
            (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
          rw [if_pos rfl, if_pos rfl]
        · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
          exact hoth _ s hw hb
  refine Prog.step_move hR hlin hi hframe ?_
  have h : (dt.prog zero one hzo args hpl).HasRight OuterPh.start (fun _ => zero)
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
          (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
        (fun _ => False) (fun _ => False))
      (OuterPh.tgtTopP .up) (fun _ => zero)
      (Function.update (Function.update
        ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (fun _ => False) (fun _ => False)) Slot.wk one) Slot.bot one) :=
    dt.prog_hasRight zero one hzo args hpl .start () trivial trivial
  rw [hwr] at h
  exact h

/-! ### The glue between legs

A pass presents the tape as `DescriptiveComplexity.Draw.Prog.trackTapeAt`: the
walked track's digits computed from a set, every other slot read off the
background. Since the background of
`DescriptiveComplexity.Draw.Data.back` already carries each register's
digits at its own slot, that presentation **is** the background – which is
what lets one leg's conclusion be the next leg's hypothesis, whichever track
each of them walks. -/

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- **A pass's presentation is the background it walks**, once the walked
slot's state agrees with the set the pass carries. Stated with the state
*after* the pass, so it also reads a pass's result back into the state. -/
theorem trackTape_back {st st' : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {t : dt.SlotIx} {m : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hagree : ∀ r s, s ≠ t →
      dt.back wmSeg zero one dt.dd0Le st r s = dt.back wmSeg zero one dt.dd0Le st' r s)
    (ht : ∀ r, dt.back wmSeg zero one dt.dd0Le st' r t =
      bitVal zero one (regBit m r)) :
    (dt.prog zero one hzo args hpl).trackTapeAt wmSeg t
        (dt.back wmSeg zero one dt.dd0Le st) m =
      fun r => (dt.prog zero one hzo args hpl).syElt
        (dt.back wmSeg zero one dt.dd0Le st' r) := by
  classical
  refine funext fun r =>
    congrArg (dt.prog zero one hzo args hpl).syElt (funext fun s => ?_)
  change (if s = t then bitVal zero one (regBit m r) else _) = _
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl]
    exact (ht r).symm
  · rw [if_neg hs]
    exact hagree r s hs

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- **Handing the walk between tracks costs nothing**: two passes walking
different registers of the same state present the same tape. -/
theorem trackTape_back_swap {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {t t' : dt.SlotIx}
    {m m' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (ht : ∀ r, dt.back wmSeg zero one dt.dd0Le st r t = bitVal zero one (regBit m r))
    (ht' : ∀ r, dt.back wmSeg zero one dt.dd0Le st r t' =
      bitVal zero one (regBit m' r)) :
    (dt.prog zero one hzo args hpl).trackTapeAt wmSeg t
        (dt.back wmSeg zero one dt.dd0Le st) m =
      (dt.prog zero one hzo args hpl).trackTapeAt wmSeg t'
        (dt.back wmSeg zero one dt.dd0Le st) m' :=
  (dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl) ht).trans
    (dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl) ht').symm

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
/-- The four machine registers carry their track's digits at their own slot,
which is the hypothesis both glue lemmas ask for. -/
theorem back_mir (st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF) :
    ∀ r, dt.back wmSeg zero one dt.dd0Le st r .mir = bitVal zero one (regBit st.mir r) :=
  fun _ => rfl

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
theorem back_tgt (st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF) :
    ∀ r, dt.back wmSeg zero one dt.dd0Le st r .tgt = bitVal zero one (regBit st.tgt r) :=
  fun _ => rfl

omit [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF]
  [Finite dt.KIx] in
theorem back_val (st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF) :
    ∀ r, dt.back wmSeg zero one dt.dd0Le st r .val = bitVal zero one (regBit st.val r) :=
  fun _ => rfl

/-! ### The second leg: startup writes the logical top into TARGET

The pattern write of `DescriptiveComplexity.Draw.MapKit`: a round trip up the
register file writing, at each cell, the digit its *other* tracks decide –
here “this cell's element carries an argument tag”, read off the one-hot
`blk` marks. The result is the address of the logical top, which the seek
that follows takes the working cell to. -/

/-- **The state after startup's pattern write**: TARGET holds the logical
top – the cells of the argument-tagged elements. -/
noncomputable def tgtTopSt {R' P' : Type} : TapeStD dt A R' P' :=
  { dt.startSt (A := A) (R' := R') (P' := P') with
    tgt := fun u => ∃ b : Fin dt.ko ⊕ Fin dt.ki, tagBlk u.1 = some b }

/-- **The pattern write's leg**: from the entry of the trip to its return at
the marker, with TARGET holding the logical top. -/
theorem reaches_tgtTop (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {fc : Q → A}
    {s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop} :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.tgtTopP .up) fc),
        Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.startSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (dt.startSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.tgtTopP .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  set st := dt.startSt (A := A) (R' := dt.RIx zero one hzo args) (P' := dt.PF)
    with hst
  set st' := dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args) (P' := dt.PF)
    with hst'
  -- the trip walks TARGET; the presentation does not care which register it walks
  have hswapIn : (dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
      (dt.back wmSeg zero one dt.dd0Le st) st.mir =
      (dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.tgt
        (dt.back wmSeg zero one dt.dd0Le st) st.tgt :=
    dt.trackTape_back_swap zero one hzo args hpl (dt.back_mir zero one hzo args st)
      (dt.back_tgt zero one hzo args st)
  rw [hswapIn]
  -- the trip's own hypotheses, off the background equations
  have htrip := MapKit.reaches
    (F := (wmSegFile hlin).toIx)
    (hsle := wmSetLe_of_full hlin (fun y => htop y) _) (PR := dt.prog zero one hzo args hpl)
    (κ := dt.tgtTopKit (A := A) (Q := Q) (P := dt.PF) one OuterPh.tgtTopP)
    (rEmb := fun ρ => ⟨OuterSite.tgtTop, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_tgtTop zero one hzo args hpl ρ)
    hR hlin hlin dt.tgt_ne_reg dt.regLast_ne_tgt dt.wk_ne_tgt htop hbot
    (rest := dt.back wmSeg zero one dt.dd0Le st) (m := st.tgt)
    (wkAddr := fun _ => False) (wmSetLt_empty_wmSeg hlin gbot)
    (dt.back_reg (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st))
    (dt.back_regLast (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st)
      hlin htop hord)
    (fun r => rfl)
    (fun g g' hgg => by
      simp only [tgtTopKit]
      refine exists_congr fun b => ?_
      rw [hgg (Slot.blk (some b))
        (show (Slot.blk (some b) : dt.SlotIx) ≠ Slot.tgt from fun h => nomatch h)])
    (fc := fc) (s := s)
  simp only [tgtTopKit] at htrip
  refine htrip.trans ?_
  -- read the trip's result back into the state
  have hset : (fun u => ∃ b : Fin dt.ko ⊕ Fin dt.ki,
      (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.tgt
        (dt.back wmSeg zero one dt.dd0Le st) st.tgt (wmSeg u) (Slot.blk (some b)) = one) =
      st'.tgt := by
    funext u
    refine propext ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [Prog.passTracks_of_ne (show (Slot.blk (some b) : dt.SlotIx) ≠ Slot.tgt
        from fun h => nomatch h)] at hb
      obtain ⟨v, hv, hvb⟩ := (bitVal_iff hzo).mp hb
      rw [wmSeg_injective hlin hv]
      exact hvb
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [Prog.passTracks_of_ne (show (Slot.blk (some b) : dt.SlotIx) ≠ Slot.tgt
        from fun h => nomatch h)]
      exact bitVal_pos ⟨u, rfl, hb⟩
  rw [hset]
  have hagree : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop)
      (sl : dt.SlotIx), sl ≠ Slot.tgt →
      dt.back wmSeg zero one dt.dd0Le st r sl = dt.back wmSeg zero one dt.dd0Le st' r sl := by
    intro r sl hsl
    match sl with
    | .tgt => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir
    | .sav | .val | .wk | .bot | .ltp | .old _ | .new _ => rfl
  rw [dt.trackTape_back zero one hzo args hpl hagree
    (dt.back_tgt zero one hzo args st'),
    ← dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl)
      (dt.back_mir zero one hzo args st')]

/-- **The run so far, chained**: from the initial configuration – the marks
over the blank, the head on the empty address – to the return of the pattern
write, with both markers planted and TARGET holding the logical top. -/
theorem reaches_startup₁ (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .start fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))) (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.tgtTopP .run)
          fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ :=
  (Relation.ReflTransGen.single
      (dt.step_start zero one hzo args hpl hR hlin hi)).trans
    (dt.reaches_tgtTop zero one hzo args hpl hR hlin hord htop hbot)

/-! ### The third leg: the working cell seeks the logical top

The random access of `DescriptiveComplexity.Draw.SeekKit`, at the target
TARGET now holds. Two single steps bracket it: the pattern write's exit
steps *right* off the marker into the seek's loop head (as every exit into a
loop head does), and the loop head's stay rule walks straight back down to
it. -/

/-- The state with the working-cell marker at a given address. -/
noncomputable def atSt {R' P' I : Type} (st : TapeSt dt A R' P' I)
    (v : Univ A R' P' dt.KIx dt.dd → Prop) : TapeSt dt A R' P' I :=
  { st with wk := fun r => r = v }

/-- The state after the seek: the marker and the mirror both at the target. -/
noncomputable def seekEndSt {R' P' : Type} (st : TapeStD dt A R' P')
    (v : Univ A R' P' dt.KIx dt.dd → Prop) : TapeStD dt A R' P' :=
  { st with wk := fun r => r = v, mir := v }

omit [LinearOrder A] [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]
  [Finite A] [Finite (dt.RIx zero one hzo args)] [Finite dt.PF] [Finite dt.KIx] in
/-- The successor of the empty address is not empty: it holds the greatest
element. -/
theorem ne_empty_of_wmIncr
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') : v' ≠ fun _ => False := by
  obtain ⟨u, -, -, ht⟩ := hi
  intro hc
  have hu : v' u := (ht u).mpr (Or.inl rfl)
  rw [hc] at hu
  exact hu

/-- **The pattern write's exit**: off the marker, rightwards, into the seek's
loop head. -/
theorem step_tgtTop_exit (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : Q → A}
    {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False) (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.tgtTopP .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .chk) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.tgtTop
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir]
      change dt.back wmSeg zero one dt.dd0Le st (fun _ => False) Slot.wk = one
      rw [back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm]
      change dt.back wmSeg zero one dt.dd0Le st (fun _ => False) Slot.reg ≠ one
      rw [back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo args hpl .tgtTop (Sum.inr ()) hg trivial

/-- **The seek's loop head walks back to the marker**: the one step the
rightward exit above owes. -/
theorem step_seek1_home (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : Q → A}
    {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .chk) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .chk) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_moveBack hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.seek1
      (Sum.inl SeekRule.stayChk)).guard fc
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir v') := by
    refine Or.inr ?_
    change (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
      (dt.back wmSeg zero one dt.dd0Le st) st.mir v' Slot.wk ≠ one
    rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk,
      bitVal_neg (dt.ne_empty_of_wmIncr zero one hzo args hi)]
    exact hzo
  exact dt.prog_hasLeft zero one hzo args hpl .seek1 (Sum.inl SeekRule.stayChk)
    hg not_false

/-- **The seek's leg**: from the loop head at the empty address to the
passing verdict on the target's cell, marker and mirror in tow. -/
theorem reaches_seek1 (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) {fc : Q → A} :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .chk) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .ty) fc),
        Sum.inl (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
          (P' := dt.PF)).tgt,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.seekEndSt (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))
            (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
              (P' := dt.PF)).tgt))
          (dt.seekEndSt (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)) (dt.tgtTopSt (A := A)
              (R' := dt.RIx zero one hzo args) (P' := dt.PF)).tgt).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  set st := dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args) (P' := dt.PF)
    with hst
  -- the target address is a logical one, hence strictly below the file
  have hTlt : WMSetLt WMLe st.tgt
      (wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) gbot) := by
    refine wmSetLt_wmSeg_of_not_bot hbot ?_ gbot
    rintro ⟨b, hb⟩
    rw [tagBlk_eq_none_of_least (fun y => (hord gbot y).mp (hbot y))] at hb
    exact nomatch hb
  have htrip := SeekKit.reaches (F := (wmSegFile hlin).toIx)
    (PR := dt.prog zero one hzo args hpl)
    (κ := dt.seekKit (A := A) (Q := Q) (P := dt.PF) OuterPh.seek1P)
    (rEmb := fun ρ => ⟨OuterSite.seek1, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_seek1 zero one hzo args hpl ρ)
    hR hlin hlin (elt := id) (Use := fun _ => True)
    (fun _ _ h => h) (fun _ _ => Iff.rfl) (fun _ x _ _ => ⟨x, trivial, rfl⟩)
    dt.mir_ne_reg dt.regLast_ne_mir dt.wk_ne_mir dt.tgt_ne_mir
    htop hbot (T := st.tgt) (fun x _ => ⟨x, trivial, rfl⟩) hTlt
    (bg := fun v => dt.back wmSeg zero one dt.dd0Le (dt.atSt st v))
    (bgN := dt.back wmSeg zero one dt.dd0Le { st with wk := fun _ => False })
    (fun _ _ => rfl) (fun _ => bitVal_neg not_false)
    (fun v r s hs => by
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fun _ => dt.back_reg (zero := zero) (one := one) (hdd := dt.dd0Le))
    (fun v => dt.back_regLast (zero := zero) (one := one) (hdd := dt.dd0Le)
      (st := dt.atSt st v) hlin htop hord)
    (fun v u => bitVal_congr (regBit_wmSeg hlin st.tgt u))
    (fc := fc)
  simp only [seekKit] at htrip
  refine htrip.trans ?_
  have hagree : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop)
      (sl : dt.SlotIx), sl ≠ Slot.mir →
      dt.back wmSeg zero one dt.dd0Le (dt.atSt st st.tgt) r sl =
        dt.back wmSeg zero one dt.dd0Le (dt.seekEndSt st st.tgt) r sl := by
    intro r sl hsl
    match sl with
    | .mir => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
    | .sav | .val | .wk | .bot | .ltp | .old _ | .new _ => rfl
  have hmir : ∀ r, dt.back wmSeg zero one dt.dd0Le (dt.seekEndSt st st.tgt) r Slot.mir =
      bitVal zero one (regBit st.tgt r) := fun _ => rfl
  rw [ixMark_id]
  rw [dt.trackTape_back zero one hzo args hpl hagree hmir,
    ← dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl)
      (dt.back_mir zero one hzo args (dt.seekEndSt st st.tgt))]

/-- **Startup, up to the logical top**: from the initial configuration to the
verdict of the seek – the marker and the mirror on the last logical address,
where the end marker is about to be planted. -/
theorem reaches_startup₂ (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .start fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))) (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .ty)
          fun _ => zero),
        Sum.inl (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
          (P' := dt.PF)).tgt,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.seekEndSt (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))
            (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
              (P' := dt.PF)).tgt))
          (dt.seekEndSt (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)) (dt.tgtTopSt (A := A)
              (R' := dt.RIx zero one hzo args) (P' := dt.PF)).tgt).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  obtain ⟨v', hi⟩ := exists_wmIncr (Le := WMLe
    (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)) hlin
    (s := fun _ => False) ⟨gbot, not_false⟩
  have hreg : ¬∃ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have h := wmSetLt_empty_wmSeg (A := Univ A (dt.RIx zero one hzo args)
      dt.PF dt.KIx dt.dd) hlin u
    rw [hu] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  refine (dt.reaches_startup₁ zero one hzo args hpl hR hlin hord htop hbot hi).trans ?_
  refine (Relation.ReflTransGen.single
    (dt.step_tgtTop_exit zero one hzo args hpl hR hlin hi rfl hreg)).trans ?_
  refine (Relation.ReflTransGen.single
    (dt.step_seek1_home zero one hzo args hpl hR hlin hi rfl)).trans ?_
  exact dt.reaches_seek1 zero one hzo args hpl hR hlin hord htop hbot

/-! ### The fourth leg: the end marker is planted and the marker goes home

The seek's exit is the erasing step the reset asks for as its one hypothesis:
at the logical top it clears the working-cell marker, plants the permanent
`ltp` end marker there and steps right; the reset then scans down to the
`bot` cell, writes the marker and bounces back. -/

/-- The state after the seek's exit: the marker erased, the end marker
planted at the last logical address. -/
noncomputable def ltpSt {R' P' : Type} (st : TapeStD dt A R' P')
    (v : Univ A R' P' dt.KIx dt.dd → Prop) : TapeStD dt A R' P' :=
  { st with wk := fun _ => False, ltp := fun r => r = v }

/-- **The reset's leg**, the seek's exit included: from the passing verdict
at the logical top to the reset's landing phase on the empty address, with
the end marker planted. -/
theorem reaches_reset1 (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (hbot : ∀ y, WMLe gbot y) {fc : Q → A} :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.seek1P .ty) fc),
        Sum.inl (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
          (P' := dt.PF)).tgt,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.seekEndSt (dt.tgtTopSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))
            (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
              (P' := dt.PF)).tgt))
          (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).tgt)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.reset1P .done) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.atSt (dt.ltpSt (dt.seekEndSt
            (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
              (P' := dt.PF)) (dt.tgtTopSt (A := A)
                (R' := dt.RIx zero one hzo args) (P' := dt.PF)).tgt)
            (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
              (P' := dt.PF)).tgt) (fun _ => False)))
          (dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).tgt)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  set st := dt.tgtTopSt (A := A) (R' := dt.RIx zero one hzo args) (P' := dt.PF)
    with hst
  set stA := dt.seekEndSt st st.tgt with hstA
  set stN := dt.ltpSt stA st.tgt with hstN
  set stB := dt.atSt stN (fun _ => False) with hstB
  -- the logical top is not a register cell
  have hTlt : WMSetLt WMLe st.tgt
      (wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) gbot) := by
    refine wmSetLt_wmSeg_of_not_bot hbot ?_ gbot
    rintro ⟨b, hb⟩
    rw [tagBlk_eq_none_of_least (fun y => (hord gbot y).mp (hbot y))] at hb
    exact nomatch hb
  have hnonreg : ∀ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      st.tgt ≠ wmSeg u := by
    intro u hu
    rw [hu] at hTlt
    exact ((wmSetLt_wmSeg_iff hlin u gbot).mp hTlt).2 (hbot u)
  -- the two states around the erasing step agree away from the top cell
  have hAN : ∀ r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop,
      r ≠ st.tgt → dt.back wmSeg zero one dt.dd0Le stN r =
        dt.back wmSeg zero one dt.dd0Le stA r := by
    intro r hr
    funext s
    match s with
    | .wk => exact bitVal_congr ⟨False.elim, fun hc => absurd hc hr⟩
    | .ltp => exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .bot | .old _ | .new _ => rfl
  have hNB : ∀ r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop,
      r ≠ (fun _ => False) → dt.back wmSeg zero one dt.dd0Le stB r =
        dt.back wmSeg zero one dt.dd0Le stN r := by
    intro r hr
    funext s
    match s with
    | .wk => exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
  -- the erasing step: the seek's exit rule
  have hwr : Function.update (Function.update
        ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le stA) st.tgt st.tgt) Slot.wk zero)
        Slot.ltp one =
      (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le stN) st.tgt st.tgt := by
    funext s
    by_cases hl : s = Slot.ltp
    · subst hl
      rw [Function.update_self, Prog.passTracks_of_ne dt.ltp_ne_mir]
      exact (bitVal_pos rfl).symm
    · rw [Function.update_of_ne hl]
      by_cases hw : s = Slot.wk
      · subst hw
        rw [Function.update_self, Prog.passTracks_of_ne dt.wk_ne_mir]
        exact (bitVal_neg not_false).symm
      · rw [Function.update_of_ne hw]
        by_cases hm : s = Slot.mir
        · subst hm
          change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
            (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
          rw [if_pos rfl, if_pos rfl]
        · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
          match s with
          | .wk => exact absurd rfl hw
          | .ltp => exact absurd rfl hl
          | .mir => exact absurd rfl hm
          | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
          | .sav | .val | .bot | .old _ | .new _ => rfl
  have h₀ : (dt.prog zero one hzo args hpl).HasRight (OuterPh.seek1P .ty) fc
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le stA) st.tgt st.tgt)
      (OuterPh.reset1P .scan) fc
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le stN) st.tgt st.tgt) := by
    have hg : ((dt.progAsm zero one hzo args).rule OuterSite.seek1
        (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracksAt wmSeg
          Slot.mir (dt.back wmSeg zero one dt.dd0Le stA) st.tgt st.tgt) := by
      refine ⟨?_, ?_⟩
      · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk]
        exact bitVal_pos rfl
      · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
        refine fun hc => ?_
        obtain ⟨u, hu⟩ := (bitVal_iff hzo).mp hc
        exact hnonreg u hu
    have h : (dt.prog zero one hzo args hpl).HasRight (OuterPh.seek1P .ty) fc
        ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le stA) st.tgt st.tgt)
        (OuterPh.reset1P .scan) fc
        (Function.update (Function.update
          ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
            (dt.back wmSeg zero one dt.dd0Le stA) st.tgt st.tgt) Slot.wk zero)
          Slot.ltp one) :=
      dt.prog_hasRight zero one hzo args hpl .seek1 (Sum.inr ()) hg trivial
    rw [hwr] at h
    exact h
  exact ResetKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := ResetKit.mk (A := A) (Q := Q) (P := dt.PF) Slot.mir Slot.bot Slot.wk
      OuterPh.reset1P)
    (rEmb := fun ρ => ⟨OuterSite.reset1, Sum.inl ρ⟩)
    (wmSegFile hlin).toIx (fun ρ => dt.prog_rules_reset1 zero one hzo args hpl ρ)
    hR hlin dt.bot_ne_mir dt.wk_ne_mir
    (v := st.tgt) ⟨gbot, fun hc => by
      obtain ⟨b, hb⟩ := hc
      rw [tagBlk_eq_none_of_least (fun y => (hord gbot y).mp (hbot y))] at hb
      exact nomatch hb⟩
    (m := st.tgt) hAN hNB (fun _ => rfl) (fun _ => rfl)
    (fun s hs => by
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fc := fc) h₀

/-! ### The last leg of startup: the mirror is cleared

The reset left the mirror holding the logical top; the evaluation wants it
at the empty address, matching the marker. One `DescriptiveComplexity.Draw.ClearKit`
trip does it, entered by the reset's exit. -/

/-- **The reset's exit**: off the marker, rightwards, into the mirror
clear. -/
theorem step_reset1_exit (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {v' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe (fun _ => False) v') {fc : Q → A}
    {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    (hreg : ¬∃ u, (fun _ => False) =
      wmSeg (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd) u) :
    (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.reset1P .done) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir1P .up) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  refine Prog.step_move hR hlin hi (fun _ _ => rfl) ?_
  have hg : ((dt.progAsm zero one hzo args).rule OuterSite.reset1
      (Sum.inr ())).guard fc ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir (fun _ => False)) := by
    refine ⟨?_, ?_⟩
    · rw [Prog.passTracks_of_ne dt.wk_ne_mir, back_wk, hwk]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne dt.mir_ne_reg.symm, back_reg]
      exact fun hc => hreg ((bitVal_iff hzo).mp hc)
  exact dt.prog_hasRight zero one hzo args hpl .reset1 (Sum.inr ()) hg trivial

/-- **The mirror clear's leg**: the trip that empties the mirror register,
returning to the marker at the empty address. -/
theorem reaches_clearMir1 (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) {fc : Q → A}
    {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    (hwk : st.wk = fun r => r = fun _ => False)
    {s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop} :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir1P .up) fc),
        Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir1P .run) fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le { st with mir := fun _ => False })
          (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have htrip := ClearKit.reaches
    (F := (wmSegFile hlin).toIx)
    (hsle := wmSetLe_of_full hlin (fun y => htop y) _) (PR := dt.prog zero one hzo args hpl)
    (κ := dt.clearMirKit (A := A) (Q := Q) (P := dt.PF) OuterPh.clearMir1P)
    (rEmb := fun ρ => ⟨OuterSite.clearMir1, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_clearMir1 zero one hzo args hpl ρ)
    hR hlin hlin dt.mir_ne_reg dt.regLast_ne_mir dt.wk_ne_mir htop hbot
    (rest := dt.back wmSeg zero one dt.dd0Le st) (m := st.mir)
    (wkAddr := fun _ => False) (wmSetLt_empty_wmSeg hlin gbot)
    (dt.back_reg (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st))
    (dt.back_regLast (zero := zero) (one := one) (hdd := dt.dd0Le) (st := st)
      hlin htop hord)
    (fun r => by
      simp only [clearMirKit]
      rw [back_wk, hwk]
      rfl)
    (fc := fc) (s := s)
  simp only [clearMirKit] at htrip
  refine htrip.trans ?_
  have hagree : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop)
      (sl : dt.SlotIx), sl ≠ Slot.mir →
      dt.back wmSeg zero one dt.dd0Le st r sl =
        dt.back wmSeg zero one dt.dd0Le { st with mir := fun _ => False } r sl := by
    intro r sl hsl
    match sl with
    | .mir => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
    | .sav | .val | .wk | .bot | .ltp | .old _ | .new _ => rfl
  have hmir : ∀ r, dt.back wmSeg zero one dt.dd0Le
      { st with mir := fun _ => False } r Slot.mir =
      bitVal zero one (regBit (fun _ => False) r) := fun _ => rfl
  rw [dt.trackTape_back zero one hzo args hpl hagree hmir,
    ← dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl)
      (dt.back_mir zero one hzo args { st with mir := fun _ => False })]

/-- **The state startup leaves behind**: the bottom mark at the empty
address, the end marker at the logical top, TARGET holding that address, the
mirror and the working-cell marker home at the empty address, every stage
track still clear – which is stage zero of the iteration. -/
noncomputable def startupSt {R' P' : Type} : TapeStD dt A R' P' :=
  { dt.atSt (dt.ltpSt (dt.seekEndSt (dt.tgtTopSt (A := A) (R' := R') (P' := P'))
      (dt.tgtTopSt (A := A) (R' := R') (P' := P')).tgt)
      (dt.tgtTopSt (A := A) (R' := R') (P' := P')).tgt) (fun _ => False) with
    mir := fun _ => False }

/-- **STARTUP, proved**: from the initial configuration – the marks over the
blank – to the entry of the per-address evaluation, with the machine's two
permanent markers planted and every register where the loop expects it. -/
theorem reaches_startup (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .start fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.emptySt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF))) (fun _ => False))
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.clearMir1P .run)
          fun _ => zero),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.startupSt (A := A)
            (R' := dt.RIx zero one hzo args) (P' := dt.PF)))
          (dt.startupSt (A := A) (R' := dt.RIx zero one hzo args)
            (P' := dt.PF)).mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  obtain ⟨v', hi⟩ := exists_wmIncr (Le := WMLe
    (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)) hlin
    (s := fun _ => False) ⟨gbot, not_false⟩
  have hreg : ¬∃ u : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      (fun _ => False) = wmSeg u := by
    rintro ⟨u, hu⟩
    have h := wmSetLt_empty_wmSeg (A := Univ A (dt.RIx zero one hzo args)
      dt.PF dt.KIx dt.dd) hlin u
    rw [hu] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  refine (dt.reaches_startup₂ zero one hzo args hpl hR hlin hord htop hbot).trans ?_
  refine (dt.reaches_reset1 zero one hzo args hpl hR hlin hord hbot).trans ?_
  refine (Relation.ReflTransGen.single
    (dt.step_reset1_exit zero one hzo args hpl hR hlin hi rfl hreg)).trans ?_
  exact dt.reaches_clearMir1 zero one hzo args hpl hR hlin hord htop hbot rfl

/-! ### The convergence sweep

COMPARE is a *plain* sweep – one step per address, no register visit – whose
verdict rides in the state (`DescriptiveComplexity.sweepState`): the passing
phase exactly while every address below has agreed. Its per-cell question is
read off the stage tracks, which is what
`DescriptiveComplexity.Draw.Data.compareKit` fixes. -/

/-- **The convergence sweep's leg**: from the empty address to the
end-marked one, the verdict accumulated in the phase. -/
theorem reaches_compare (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc)
          (fun _ => False)),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr (sweepState (fun r => ∀ i, (st.old i r ↔ st.new i r))
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .py) fc)
          ((dt.prog zero one hzo args hpl).stElt (.cmpP .pn) fc) ltpAddr),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  refine FlagSweepKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := dt.compareKit (Q := Q) (P := dt.PF) one OuterPh.cmpP)
    (rEmb := fun ρ => ⟨OuterSite.compare, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_compare zero one hzo args hpl ρ)
    hR hlin dt.ltp_ne_mir (rest := dt.back wmSeg zero one dt.dd0Le st) (m := st.mir)
    (ltpAddr := ltpAddr)
    (fun r => by
      simp only [compareKit]
      rw [back_ltp, hltp]
      rfl)
    (Test := fun r => ∀ i, (st.old i r ↔ st.new i r))
    (fun r => by
      simp only [compareKit]
      refine forall_congr' fun i => ?_
      rw [Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h),
        Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h), back_old, back_new]
      exact iff_congr (bitVal_iff hzo) (bitVal_iff hzo))
    (fc := fc) (wmSetLe_of_empty hlin (fun _ hc => hc) ltpAddr)
    ((isLinOrd_wmSetLe hlin).1 ltpAddr)

/-! ### The copy-back sweep

COPY is the other plain sweep: one rewrite per address, every stage track
taking its successor's digit, so that the next round's `old` is this round's
`new`. Its background is a family indexed by the sweep's frontier – the
addresses already passed hold the new stage, the others the old one. -/

open Classical in
/-- **The state during the copy-back**, at frontier `s`: the addresses
strictly below `s` have taken their next-stage digits. -/
noncomputable def copySt (st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF)
    (s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop) :
    TapeStD dt A (dt.RIx zero one hzo args) dt.PF :=
  { st with
    old := fun i r => if WMSetLt WMLe r s then st.new i r else st.old i r }

/-- **The copy-back's leg**: from the empty address to the end-marked one,
every stage track rewritten on the way. -/
theorem reaches_copy (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {ltpAddr : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hltp : st.ltp = fun r => r = ltpAddr) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl (fun _ => False),
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le
            (dt.copySt zero one hzo args st (fun _ => False))) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .copyP fc),
        Sum.inl ltpAddr,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st ltpAddr)) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  refine WriteSweepKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := dt.copyKit (A := A) (Q := Q) (P := dt.PF) OuterPh.copyP)
    (rEmb := fun ρ => ⟨OuterSite.copy, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_copy zero one hzo args hpl ρ)
    hR hlin dt.ltp_ne_mir (m := st.mir)
    (restAt := fun s => dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st s))
    (ltpAddr := ltpAddr)
    (fun k r => by
      simp only [copyKit]
      rw [back_ltp]
      simp only [copySt, hltp]
      rfl)
    (fc := fc) (wmSetLe_of_empty hlin (fun _ hc => hc) ltpAddr)
    ((isLinOrd_wmSetLe hlin).1 ltpAddr) ?_ ?_
  · -- the frontier's move changes the background only at the cell left behind
    intro s u hi _ _ r hr
    funext sl
    match sl with
    | .old i =>
      change bitVal zero one ((dt.copySt zero one hzo args st u).old i r) =
        bitVal zero one ((dt.copySt zero one hzo args st s).old i r)
      simp only [copySt]
      have hiff : WMSetLt WMLe r u ↔ WMSetLt WMLe r s := by
        rw [wmSetLt_iff_of_wmIncr hlin hi r, wmSetLt_iff r s]
        exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩
      by_cases hc : WMSetLt WMLe r s
      · rw [if_pos (hiff.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
    | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
  · -- the rewrite at the frontier's own cell
    intro s u hi _ _
    have hsu : WMSetLt WMLe s u :=
      (wmSetLt_iff s u).mpr ⟨wmSetLe_of_wmIncr hi, ne_of_wmIncr hi⟩
    funext sl
    rw [show (dt.copyKit (A := A) (Q := Q) (P := dt.PF) OuterPh.copyP).t =
      (Slot.mir : dt.SlotIx) from rfl]
    by_cases ho : ∃ i, sl = Slot.old i
    · obtain ⟨i, rfl⟩ := ho
      have hL : (dt.copyKit (A := A) (Q := Q) (P := dt.PF) OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
            (dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s) (Slot.old i) =
          (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
            (dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s (Slot.new i) := rfl
      rw [hL, Prog.passTracks_of_ne (show (Slot.new i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h),
        Prog.passTracks_of_ne (show (Slot.old i : dt.SlotIx) ≠ Slot.mir from
          fun h => nomatch h)]
      change bitVal zero one ((dt.copySt zero one hzo args st s).new i s) =
        bitVal zero one ((dt.copySt zero one hzo args st u).old i s)
      simp only [copySt, if_pos hsu]
    · have hL : (dt.copyKit (A := A) (Q := Q) (P := dt.PF) OuterPh.copyP).wrG
          ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
            (dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s) sl =
          (dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
            (dt.back wmSeg zero one dt.dd0Le (dt.copySt zero one hzo args st s))
            st.mir s sl := by
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl
      rw [hL]
      by_cases hm : sl = Slot.mir
      · subst hm
        change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
          (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
        match sl with
        | .old i => exact absurd ⟨i, rfl⟩ ho
        | .mir => exact absurd rfl hm
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
        | .sav | .val | .wk | .bot | .ltp | .new _ => rfl

/-! ### The walks home

A plain sweep leaves the machine at the top of the stretch while the marker
never moved, so getting back is a scan: one phase, one rule. The outer
program does it three times – after the convergence sweep, after the
copy-back, and before the output evaluation – and they differ only in which
phase they walk in. -/

/-- **A walk home**: from anywhere at or above the marker, back to it. The
rule-name injection is the parameter, so the three home sites of the outer
program instantiate it directly. -/
theorem reaches_home (ph : dt.PF)
    {rEmb : HomeKit.HomeRule → dt.RIx zero one hzo args}
    (hrules : ∀ ρ : HomeKit.HomeRule,
      (dt.prog zero one hzo args hpl).rules (rEmb ρ) =
        (HomeKit.mk (A := A) (Q := Q) (P := dt.PF) Slot.mir Slot.wk ph).rule
          one ρ)
    (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {v : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v)
    {s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt ph fc), Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt ph fc), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ :=
  HomeKit.reaches (PR := dt.prog zero one hzo args hpl)
    (κ := HomeKit.mk (A := A) (Q := Q) (P := dt.PF) Slot.mir Slot.wk ph)
    (wmSegFile hlin).toIx hrules hR hlin dt.wk_ne_mir (rest := dt.back wmSeg zero one dt.dd0Le st)
    (m := st.mir) (v := v) (fun r => by rw [back_wk, hwk]; rfl) (fc := fc) hle

/-- The walk home after a failed convergence sweep. -/
theorem reaches_homeCmp (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {v s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v) (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCmpP fc), Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCmpP fc), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ :=
  dt.reaches_home zero one hzo args hpl .homeCmpP
    (rEmb := fun ρ => ⟨OuterSite.homeCmp, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_homeCmp zero one hzo args hpl ρ) hR hlin hwk hle

/-- The walk home after the copy-back. -/
theorem reaches_homeCopy (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {v s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v) (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCopyP fc), Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeCopyP fc), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ :=
  dt.reaches_home zero one hzo args hpl .homeCopyP
    (rEmb := fun ρ => ⟨OuterSite.homeCopy, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_homeCopy zero one hzo args hpl ρ) hR hlin hwk hle

/-- The walk home before the output evaluation. -/
theorem reaches_homeOut (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    {fc : Q → A} {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {v s : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v) (hle : WMSetLe WMLe v s) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeOutP fc), Sum.inl s,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt .homeOutP fc), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ :=
  dt.reaches_home zero one hzo args hpl .homeOutP
    (rEmb := fun ρ => ⟨OuterSite.homeOut, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_homeOut zero one hzo args hpl ρ) hR hlin hwk hle

/-! ### One round of the outer sweep

ADVANCE is the round every sweep repeats: erase the marker, step on, write
it at the next address, walk up to the register file, increment the mirror
there so that it keeps mirroring the marker's address, and come back. Its
entry – the erasing step – is the caller's rule, exactly as the reset's is,
so the evaluation's boundary rule is what this leg takes as its `h₀`. -/

/-- The state with the marker erased: the middle of a marker move. -/
noncomputable def offSt {R' P' : Type} (st : TapeStD dt A R' P') :
    TapeStD dt A R' P' :=
  { st with wk := fun _ => False }

/-- **One round of the outer sweep**: the marker and the mirror both step
on, in lockstep. -/
theorem reaches_sweepAdv (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {gtop gbot : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd}
    (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
    {fc : Q → A} {p₀ : dt.PF}
    {st : TapeStD dt A (dt.RIx zero one hzo args) dt.PF}
    {v v' m' : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop}
    (hwk : st.wk = fun r => r = v) (hi : WMIncr WMLe v v')
    (hv' : WMSetLt WMLe v' (wmSeg gbot)) (him : WMIncr WMLe st.mir m')
    (h₀ : (dt.prog zero one hzo args hpl).HasRight p₀ fc
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le st) st.mir v)
      (.advP .a1) fc
      ((dt.prog zero one hzo args hpl).passTracksAt wmSeg Slot.mir
        (dt.back wmSeg zero one dt.dd0Le (dt.offSt st)) st.mir v)) :
    Relation.ReflTransGen (wideData (Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd)).Step
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt p₀ fc), Sum.inl v,
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le st) st.mir)
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩
      ⟨Sum.inr ((dt.prog zero one hzo args hpl).stElt (.advP .a4) fc),
        Sum.inl v',
        wideTape ((dt.prog zero one hzo args hpl).trackTapeAt wmSeg Slot.mir
          (dt.back wmSeg zero one dt.dd0Le
            { dt.atSt st v' with mir := m' }) m')
          ((dt.prog zero one hzo args hpl).syElt
            (dt.prog zero one hzo args hpl).blank)⟩ := by
  classical
  have htrip := AdvKit.reaches (F := (wmSegFile hlin).toIx) (PR := dt.prog zero one hzo args hpl)
    (κ := dt.advKit (A := A) (Q := Q) (P := dt.PF) OuterPh.advP)
    (rEmb := fun ρ => ⟨OuterSite.sweepAdv, Sum.inl ρ⟩)
    (fun ρ => dt.prog_rules_sweepAdv zero one hzo args hpl ρ)
    hR hlin hlin dt.mir_ne_reg dt.regLast_ne_mir dt.wk_ne_mir htop hbot hi hv'
    (m := st.mir) (m' := m') him
    (restA := dt.back wmSeg zero one dt.dd0Le st)
    (restN := dt.back wmSeg zero one dt.dd0Le (dt.offSt st))
    (restB := dt.back wmSeg zero one dt.dd0Le (dt.atSt st v'))
    (fun r hr => by
      funext s
      match s with
      | .wk =>
        rw [back_wk, back_wk, hwk]
        exact bitVal_congr ⟨False.elim, fun hc => absurd hc hr⟩
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fun r hr => by
      funext s
      match s with
      | .wk =>
        rw [back_wk, back_wk]
        exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (by simp only [advKit]; exact bitVal_neg not_false)
    (fun s hs => by
      simp only [advKit] at hs ⊢
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fun r => by simp only [advKit]; rw [back_wk]; rfl)
    (fun r => by
      simp only [advKit]
      exact dt.back_reg (zero := zero) (one := one) (hdd := dt.dd0Le) r)
    (fun r => by
      simp only [advKit]
      exact dt.back_regLast (zero := zero) (one := one) (hdd := dt.dd0Le)
        (st := dt.atSt st v') hlin htop hord r)
    (p₀ := p₀) (fc := fc) h₀
  simp only [advKit] at htrip
  refine htrip.trans ?_
  have hagree : ∀ (r : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd → Prop)
      (sl : dt.SlotIx), sl ≠ Slot.mir →
      dt.back wmSeg zero one dt.dd0Le (dt.atSt st v') r sl =
        dt.back wmSeg zero one dt.dd0Le { dt.atSt st v' with mir := m' } r sl := by
    intro r sl hsl
    match sl with
    | .mir => exact absurd rfl hsl
    | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
    | .sav | .val | .wk | .bot | .ltp | .old _ | .new _ => rfl
  have hmir : ∀ r, dt.back wmSeg zero one dt.dd0Le
      { dt.atSt st v' with mir := m' } r Slot.mir =
      bitVal zero one (regBit m' r) := fun _ => rfl
  rw [dt.trackTape_back zero one hzo args hpl hagree hmir,
    ← dt.trackTape_back zero one hzo args hpl (fun _ _ _ => rfl)
      (dt.back_mir zero one hzo args { dt.atSt st v' with mir := m' })]

end Data

end Draw

end DescriptiveComplexity
