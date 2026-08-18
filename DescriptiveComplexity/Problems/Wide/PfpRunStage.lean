/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpStageAtom
import DescriptiveComplexity.Problems.Wide.PfpBack
import DescriptiveComplexity.Problems.Wide.PfpRunElem

/-!
# The stage atom's run

The run theorem of `DescriptiveComplexity.Pfp.PfpData.stageRule` – the
random access. The tuple loops stay abstract (one hypothesis for the whole
chain, discharged by `DescriptiveComplexity.Pfp.tuple_run` at
instantiation); this file contributes the itinerary around them: save the
mirror, clear the target, run the loops, reset, clear the mirror, seek the
target, read the stage bit under the head, restore the target, and come
home the same way.

The statement is in the `DescriptiveComplexity.Pfp.TapeSt` idiom: the
machine's mutable state is a record, each leg one update, and every slot
equation a kit asks for is definitional in
`DescriptiveComplexity.Pfp.PfpData.ixBack`; the handoff between legs walking
different tracks is `DescriptiveComplexity.Pfp.PfpData.trackTape_back_gen`.

**The file is a parameter.** A clocked program has no register per element, so
the run is stated at an arbitrary `DescriptiveComplexity.Pfp.LaidFile` with the
address correspondence of `DescriptiveComplexity.Problems.Wide.IxAddr`: what the
mirror, the save and the target hold are the *marks* of their addresses
(`DescriptiveComplexity.ixMark`), and the seek's verdict is again an equality of
addresses because the correspondence carries the order. The elementwise file is
that at the identity (`DescriptiveComplexity.Pfp.PfpData.diagLaid`), which is
what `stageAtSt`, `stageEndSt` and `trackTape_back_gen_diag` are.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)
variable {A R P Q : Type} {k : ℕ}
variable [Fintype Q] [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P Q dt.SlotIx dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R P I)
variable {elt : I → Univ A R P dt.KIx dt.dd} {Use : I → Prop}
variable (hinj : Function.Injective elt)
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u → WMLt WMLe (elt u) x →
  ∃ u', Use u' ∧ elt u' = x)

/-- The state at the far end of the random access: marker and mirror on the
target, the mirror's address saved, the target built. -/
noncomputable def ixStageAtSt (st : TapeSt dt A R P I) (elt : I → Univ A R P dt.KIx dt.dd)
    (v mT : Univ A R P dt.KIx dt.dd → Prop) : TapeSt dt A R P I :=
  { st with sav := ixMark elt v, tgt := ixMark elt mT,
            wk := fun r => r = mT, mir := ixMark elt mT }

/-- The state the random access returns in: the target and the save both
holding the home address, everything else as at entry. -/
noncomputable def ixStageEndSt (st : TapeSt dt A R P I) (elt : I → Univ A R P dt.KIx dt.dd)
    (v : Univ A R P dt.KIx dt.dd → Prop) : TapeSt dt A R P I :=
  { st with sav := ixMark elt v, tgt := ixMark elt v }

omit [Finite A] [Finite R] [Finite P] [Finite I] in
/-- **A leg's after-tape, read against the state it produced**: the walked
track moves into the new state's background, whose other slots agree with
the old one's. The generic sibling of the concrete
`DescriptiveComplexity.Pfp.PfpData.trackTape_back`. -/
theorem trackTape_back_gen {stA stB : TapeSt dt A R P I} {t : dt.SlotIx}
    {m : I → Prop}
    (hagree : ∀ r s, s ≠ t →
      dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stA r s =
        dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stB r s)
    (ht : ∀ r, dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stB r t =
      bitVal PR.zero PR.one (bitAtOf F.cell m r)) :
    PR.trackTapeAt F.cell t (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stA) m =
      fun r => PR.syElt (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stB r) := by
  refine funext fun r => ?_
  change PR.syElt (fun s => if s = t
      then bitVal PR.zero PR.one (bitAtOf F.cell m r)
      else dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stA r s) =
    PR.syElt (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stB r)
  refine congrArg _ (funext fun s => ?_)
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, ht]
  · rw [if_neg hs]
    exact hagree r s hs

section StageRun

variable {emb : StagePh k → P}
variable {srcTrack : Fin k → dt.SlotIx}
variable {srcBlk dstBlk : Fin k → Fin dt.ko ⊕ Fin dt.ki}
variable {coord : Fin dt.dd0 → Q}
variable {bitFlag : (Q → A) → Prop}
variable {setBit : Bool → (Q → A) → (dt.SlotIx → A) → (Q → A)}
variable {initLv advLv : (Q → A) → (dt.SlotIx → A) → (Q → A)}
variable {IsMaxLv : (Q → A) → Prop}
variable {oldSlot : dt.SlotIx}
variable {setAv : Bool → (Q → A) → (dt.SlotIx → A) → (Q → A)}
variable {exitPh : P}
variable {rEmb : ∀ i : StageSite k, StageSh k i → R}
variable (hrules : ∀ (i : StageSite k) (ρ : StageSh k i),
  PR.rules (rEmb i ρ) = dt.stageRule PR.zero PR.one emb srcTrack srcBlk
    dstBlk coord bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ)

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : StageSite k} {ρ : StageSh k i}
    {f f' : Q → A} {g g' : dt.SlotIx → A} {p p' : P}
    (hg : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).guard f g)
    (hp : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).srcPh = p)
    (hp' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).dstPh = p')
    (hf' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).dstSt f g
        = f')
    (hg' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).wr f g
        = g')
    (hmr : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i
        ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] in
include hrules in
/-- A rule of the machinery with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : StageSite k} {ρ : StageSh k i}
    {f f' : Q → A} {g g' : dt.SlotIx → A} {p p' : P}
    (hg : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).guard f g)
    (hp : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).srcPh = p)
    (hp' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).dstPh = p')
    (hf' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).dstSt f g
        = f')
    (hg' : (dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i ρ).wr f g
        = g')
    (hml : ¬(dt.stageRule PR.zero PR.one emb srcTrack srcBlk dstBlk coord
      bitFlag setBit initLv advLv IsMaxLv oldSlot setAv exitPh i
        ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hix : IsLinOrd F.le)
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {st : TapeSt dt A R P I}
variable (hwkSt : st.wk = fun r => r = v)
variable (hmirSt : st.mir = ixMark elt v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable {mT : Univ A R P dt.KIx dt.dd → Prop}
variable (hTh : IxHolds elt Use mT) (hvh : IxHolds elt Use v)
variable (hT : WMSetLt WMLe mT (F.cell gbot))
variable {T' : Univ A R P dt.KIx dt.dd → Prop} (hTi : WMIncr WMLe mT T')
variable {f₀ fL : Q → A}
variable (hLoops : Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
  ⟨Sum.inr (PR.stElt (stageFirstTup emb)
      (initLv f₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := fun _ => False } v))), Sum.inl v',
    wideTape (PR.trackTapeAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := fun _ => False }) (ixMark elt v))
      (PR.syElt PR.blank)⟩
  ⟨Sum.inr (PR.stElt (emb .cR1) fL), Sum.inl v',
    wideTape (PR.trackTapeAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := ixMark elt mT }) (ixMark elt v))
      (PR.syElt PR.blank)⟩)
variable {b : Bool}
variable (hbT : dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageAtSt st elt v mT) mT
  oldSlot = PR.one ↔ b = true)
variable (holdmir : oldSlot ≠ Slot.mir)

/-- The itinerary's legs, added up: five passes of the file, two resets, two
seeks, the loops and thirteen dispatches. -/
private theorem legs_le (a b c e : ℕ) :
    a + (1 + (a + (1 + (e + (1 + (b + (1 + (a + (1 + (1 + (c +
      (1 + (a + (1 + (1 + (b + (1 + (a + (1 + (1 + (c + 1)))))))))))))))))))))
      ≤ 5 * a + 2 * b + 2 * c + e + 13 := by
  omega

section Clocked

variable {wG : ℕ} (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (wP wR wK wL : ℕ)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
-- The reset and the seek are charged against the *working area* alone: both are
-- applied at the marker and at the built TARGET, and the atom's own hypotheses
-- put those below the file (`hv`, `hT`). A clocked program cannot afford these
-- widths quantified over the whole tape.
variable (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe T (F.cell gbot) →
  wideRank T *
      (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) +
        (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
          wideRank (F.cell gbot) + 4)) + 1 +
    (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
      wideRank (F.cell gbot)) ≤ wK)
variable (hLoopsIn : (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn wL
  ⟨Sum.inr (PR.stElt (stageFirstTup emb)
      (initLv f₀ (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := fun _ => False } v))), Sum.inl v',
    wideTape (PR.trackTapeAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := fun _ => False }) (ixMark elt v))
      (PR.syElt PR.blank)⟩
  ⟨Sum.inr (PR.stElt (emb .cR1) fL), Sum.inl v',
    wideTape (PR.trackTapeAt F.cell Slot.mir
      (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
        { st with sav := ixMark elt v, tgt := ixMark elt mT }) (ixMark elt v))
      (PR.syElt PR.blank)⟩)

include hrules hR hlin hix hinj hmono hup htop hbot hv hvi hwkSt hmirSt hbotSt
  hTh hvh hT hTi hgap hwP hwR hwK
  hLoopsIn hbT holdmir in
/-- The atom's itinerary, leg by leg, in the order the assembly composes them:
what `DescriptiveComplexity.Pfp.PfpData.stage_reachesIn` adds up. -/
private theorem stage_reachesIn_legs :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (wP + (1 + (wP + (1 + (wL + (1 + (wR + (1 + (wP + (1 + (1 + (wK +
        (1 + (wP + (1 + (1 + (wR + (1 + (wP + (1 + (1 + (wK + 1))))))))))))))))))))))
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (setAv b fL (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixStageAtSt st elt v mT) mT))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  have hvnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hv
  have hTnr := not_reg_of_lt_bot F.toIxFile hlin hix hbot hT
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  -- the empty address, its successor, and its non-registerhood
  obtain ⟨e₁, h0i⟩ := exists_wmIncr hlin
    (s := fun _ => False) ⟨(F.cell_nonempty gbot).choose, not_false⟩
  have he1top : WMSetLe WMLe e₁ (F.cell gtop) :=
    F.toIxFile.le_cell_top_of_le hix hbot
      (wmSetLe_of_wmIncr_of_lt hlin h0i (F.toIxFile.wmSetLt_empty_cell gbot))
  have hT'top : WMSetLe WMLe T' (F.cell gtop) :=
    F.toIxFile.le_cell_top_of_le hix hbot (wmSetLe_of_wmIncr_of_lt hlin hTi hT)
  have hv'top : WMSetLe WMLe v' (F.cell gtop) :=
    F.toIxFile.le_cell_top_of_le hix hbot (wmSetLe_of_wmIncr_of_lt hlin hvi hv)
  have h0nr : ∀ u : I, (fun _ => False) ≠ F.cell u := by
    intro u hc
    have h := F.toIxFile.wmSetLt_empty_cell u
    rw [hc] at h
    exact ((wmSetLt_iff _ _).mp h).2 rfl
  have h0e₁ : (fun _ => False : Univ A R P dt.KIx dt.dd → Prop) ≠ e₁ :=
    ne_of_wmIncr h0i
  have hTT' : mT ≠ T' := ne_of_wmIncr hTi
  -- named slot disequalities
  have hne_wk_mir : (Slot.wk : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  have hne_reg_mir : (Slot.reg : dt.SlotIx) ≠ Slot.mir := fun h => nomatch h
  -- the states after each leg
  set st1 : TapeSt dt A R P I := { st with sav := ixMark elt v } with hst1
  set st2 : TapeSt dt A R P I := { st with sav := ixMark elt v, tgt := fun _ => False }
    with hst2
  set st3 : TapeSt dt A R P I := { st with sav := ixMark elt v, tgt := ixMark elt mT } with hst3
  set st4 : TapeSt dt A R P I := { st3 with wk := fun _ => False } with hst4
  set st5 : TapeSt dt A R P I :=
    { st3 with wk := fun r => r = (fun _ => False) } with hst5
  set st6 : TapeSt dt A R P I := { st5 with mir := fun _ => False } with hst6
  set st7 : TapeSt dt A R P I := dt.ixStageAtSt st elt v mT with hst7
  set st8 : TapeSt dt A R P I := { st7 with tgt := ixMark elt v } with hst8
  set st9 : TapeSt dt A R P I := { st8 with wk := fun _ => False } with hst9
  set st10 : TapeSt dt A R P I :=
    { st8 with wk := fun r => r = (fun _ => False) } with hst10
  set st11 : TapeSt dt A R P I := { st10 with mir := fun _ => False } with hst11
  -- shorthands
  let bk : TapeSt dt A R P I →
      (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A :=
    fun stX => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stX
  have hbkdef : ∀ stX, bk stX = dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stX :=
    fun _ => rfl
  -- background equations used throughout
  have hwk1 : ∀ (stX : TapeSt dt A R P I) (w : Univ A R P dt.KIx dt.dd → Prop),
      stX.wk = (fun r => r = w) →
      ∀ r, bk stX r Slot.wk = bitVal PR.zero PR.one (r = w) := by
    intro stX w hw r
    rw [hbkdef, ixBack_wk, hw]
  have hrgX : ∀ (stX : TapeSt dt A R P I) (r : Univ A R P dt.KIx dt.dd → Prop),
      bk stX r Slot.reg =
        bitVal PR.zero PR.one (∃ u : I, r = F.cell u) :=
    fun _ _ => rfl
  have hrlX : ∀ (stX : TapeSt dt A R P I) (r : Univ A R P dt.KIx dt.dd → Prop),
      bk stX r Slot.regLast = bitVal PR.zero PR.one (r = F.cell gtop) :=
    fun stX => dt.ixBack_regLast hix htop
  -- the exit guard at a marked, non-register cell
  have hexitG : ∀ (stX : TapeSt dt A R P I) (w : Univ A R P dt.KIx dt.dd → Prop)
      (m₂ : I → Prop),
      stX.wk = (fun r => r = w) → (∀ u : I, w ≠ F.cell u) →
      dt.exitG PR.one (PR.passTracksAt F.cell Slot.mir (bk stX) m₂ w) := by
    intro stX w m₂ hw hnr
    constructor
    · rw [Prog.passTracks_of_ne hne_wk_mir, hwk1 stX w hw]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_mir, hrgX,
        bitVal_neg (fun hc => hnr hc.choose hc.choose_spec)]
      exact hzo
  -- the wk slot is off at any other cell
  have hwkOff : ∀ (stX : TapeSt dt A R P I)
      (w r : Univ A R P dt.KIx dt.dd → Prop) (m₂ : I → Prop),
      stX.wk = (fun r => r = w) → r ≠ w →
      PR.passTracksAt F.cell Slot.mir (bk stX) m₂ r Slot.wk ≠ PR.one := by
    intro stX w r m₂ hw hr
    rw [Prog.passTracks_of_ne hne_wk_mir, hwk1 stX w hw,
      bitVal_neg hr]
    exact hzo
  -- leg 1: the save trip, sav := the mirror's content = the home address
  have hrulesSav : ∀ ρ : TrackRule,
      PR.rules (rEmb .sav (Sum.inl ρ)) =
        (CopyKit.mk (A := A) (Q := Q) Slot.sav Slot.mir Slot.reg Slot.regLast
          Slot.wk (fun t => emb (.savP t))).rule PR.one ρ :=
    fun ρ => hrules .sav (Sum.inl ρ)
  have hsavBitOr : ∀ u : I,
      bk st (F.cell u) Slot.mir = PR.zero ∨
        bk st (F.cell u) Slot.mir = PR.one := by
    intro u
    change bitVal PR.zero PR.one (bitAtOf F.cell st.mir (F.cell u)) = PR.zero ∨ _
    by_cases h : bitAtOf F.cell st.mir (F.cell u)
    · exact Or.inr (bitVal_pos h)
    · exact Or.inl (bitVal_neg h)
  have hsav := (CopyKit.reachesIn
    (κ := CopyKit.mk (A := A) (Q := Q) Slot.sav Slot.mir Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.savP t)))
    hrulesSav F.toIxFile hR hlin hix (fun h => nomatch h) (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) htop hbot hv
    (hrgX st) (hrlX st) (hwk1 st v hwkSt) hsavBitOr
    (fc := f₀) (s := v') (m := st.sav) (hsle := hv'top) (hgap := hgap)).mono hwP
  have hsavC : (fun u : I => bk st (F.cell u) Slot.mir = PR.one) = ixMark elt v := by
    funext u
    refine propext ?_
    refine Iff.trans ?_ (iff_of_eq (congrArg (· u) hmirSt))
    change bitVal PR.zero PR.one (bitAtOf F.cell st.mir (F.cell u)) = PR.one ↔ _
    exact (bitVal_iff hzo).trans (F.toIxFile.bitAt_cell hix st.mir u)
  rw [hsavC] at hsav
  -- present the entry tape as the save trip's, and its result at `st1`
  have hsavIn : PR.trackTapeAt F.cell Slot.mir (bk st) st.mir =
      PR.trackTapeAt F.cell Slot.sav (bk st) st.sav :=
    (trackTape_of_back F.toIxFile (t := Slot.mir) (rest := bk st) (m := st.mir)
      (fun _ => rfl)).trans
      (trackTape_of_back F.toIxFile (t := Slot.sav) (rest := bk st) (m := st.sav)
        (fun _ => rfl)).symm
  have hsavOut : PR.trackTapeAt F.cell Slot.sav (bk st) (ixMark elt v) =
      PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir := by
    refine (dt.trackTape_back_gen F (stB := st1) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st1) (stB := st1) (t := Slot.mir)
        (m := st1.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .sav => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 2: the save's exit into the target clear
  have hsavExit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.savP .run)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.clrP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .sav) (ρ := Sum.inr ())
      (hexitG st1 v st1.mir hwkSt hvnr) rfl rfl rfl rfl trivial
  -- leg 3: the target clear
  have hrulesClr : ∀ ρ : TrackRule,
      PR.rules (rEmb .clr (Sum.inl ρ)) =
        (ClearKit.mk (A := A) (Q := Q) Slot.tgt Slot.reg Slot.regLast
          Slot.wk (fun t => emb (.clrP t))).rule PR.zero PR.one ρ :=
    fun ρ => hrules .clr (Sum.inl ρ)
  have hclr := (ClearKit.reachesIn
    (κ := ClearKit.mk (A := A) (Q := Q) Slot.tgt Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.clrP t)))
    hrulesClr F.toIxFile hR hlin hix (fun h => nomatch h) (fun h => nomatch h)
    (fun h => nomatch h) htop hbot hv
    (hrgX st1) (hrlX st1) (hwk1 st1 v hwkSt)
    (fc := f₀) (s := v') (m := st1.tgt) (hsle := hv'top) (hgap := hgap)).mono hwP
  have hclrIn : PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir =
      PR.trackTapeAt F.cell Slot.tgt (bk st1) st1.tgt :=
    (trackTape_of_back F.toIxFile (t := Slot.mir) (rest := bk st1) (m := st1.mir)
      (fun _ => rfl)).trans
      (trackTape_of_back F.toIxFile (t := Slot.tgt) (rest := bk st1) (m := st1.tgt)
        (fun _ => rfl)).symm
  have hclrOut : PR.trackTapeAt F.cell Slot.tgt (bk st1) (fun _ => False) =
      PR.trackTapeAt F.cell Slot.mir (bk st2) st2.mir := by
    refine (dt.trackTape_back_gen F (stB := st2) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st2) (stB := st2) (t := Slot.mir)
        (m := st2.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .tgt => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
      | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 4: the clear's exit into the loops
  have hclrExit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.clrP .run)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st2) st2.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (stageFirstTup emb) (initLv f₀ (bk st2 v))),
        Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st2) st2.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule dt hrules (i := .clr) (ρ := Sum.inr ())
      (hexitG st2 v st2.mir hwkSt hvnr) rfl rfl ?_ rfl trivial
    change initLv f₀ (PR.passTracksAt F.cell Slot.mir (bk st2) st2.mir v) =
      initLv f₀ (bk st2 v)
    rw [passTracks_of_back F.toIxFile (t := Slot.mir) (rest := bk st2) (m := st2.mir)
      (fun _ => rfl) v]
  -- leg 6: the walk back at the first reset's checkpoint
  have hcR1back : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .cR1) fL), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st3) (ixMark elt v)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR1) fL), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st3) (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule dt hrules (i := .cR1) (ρ := .stay)
      (hwkOff st3 v v' (ixMark elt v) hwkSt (Ne.symm hvv')) rfl rfl rfl rfl not_false
  -- a reset's leg, shared by both resets: from the erasing checkpoint at the
  -- marked cell to the landing phase on the empty address
  have hreset : ∀ (stA' : TapeSt dt A R P I)
      (w : Univ A R P dt.KIx dt.dd → Prop) (m₂ : I → Prop)
      (rEmbR : ResetRule → R) (embR : ResetPh → P) (p₀ : P) (fc : Q → A),
      WMSetLt WMLe w (F.cell gbot) →
      (∀ ρ : ResetRule, PR.rules (rEmbR ρ) =
        (ResetKit.mk (A := A) (Q := Q) Slot.mir Slot.bot Slot.wk embR).rule
          PR.one ρ) →
      stA'.wk = (fun r => r = w) →
      (∃ x : Univ A R P dt.KIx dt.dd, ¬w x) →
      stA'.bot = (fun r => r = (fun _ => False)) →
      PR.HasRight p₀ fc (PR.passTracksAt F.cell Slot.mir (bk stA') m₂ w)
        (embR .scan) fc
        (PR.passTracksAt F.cell Slot.mir (bk { stA' with wk := fun _ => False }) m₂
          w) →
      (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn wR
        ⟨Sum.inr (PR.stElt p₀ fc), Sum.inl w,
          wideTape (PR.trackTapeAt F.cell Slot.mir (bk stA') m₂) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (embR .done) fc), Sum.inl (fun _ => False),
          wideTape (PR.trackTapeAt F.cell Slot.mir
            (bk { stA' with wk := fun r => r = (fun _ => False) }) m₂)
            (PR.syElt PR.blank)⟩ := by
    intro stA' w m₂ rEmbR embR p₀ fc hwbot hrulesR hwkA hwx hbotA h₀
    refine TMData.ReachesIn.mono (hwR w hwbot) (ResetKit.reachesIn
      (κ := ResetKit.mk (A := A) (Q := Q) Slot.mir Slot.bot Slot.wk embR)
      F.toIxFile hrulesR hR hlin (fun h => nomatch h) (fun h => nomatch h)
      (v := w) hwx (m := m₂)
      (restA := bk stA') (restN := bk { stA' with wk := fun _ => False })
      (restB := bk { stA' with wk := fun r => r = (fun _ => False) })
      ?_ ?_ ?_ ?_ ?_ h₀)
    · intro r hr
      funext s
      match s with
      | .wk =>
        refine bitVal_congr ⟨False.elim, fun hc => absurd ?_ hr⟩
        rw [hwkA] at hc
        exact hc
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
    · intro r hr
      funext s
      match s with
      | .wk => exact bitVal_congr ⟨fun hc => absurd hc hr, False.elim⟩
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
    · intro r
      change bitVal PR.zero PR.one (stA'.bot r) = _
      rw [hbotA]
    · exact fun _ => rfl
    · intro s hs
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
  -- the erasing step's written symbol, shared by both reset entries
  have herase : ∀ (stA' : TapeSt dt A R P I)
      (w : Univ A R P dt.KIx dt.dd → Prop) (m₂ : I → Prop),
      Function.update (PR.passTracksAt F.cell Slot.mir (bk stA') m₂ w) Slot.wk
          PR.zero =
        PR.passTracksAt F.cell Slot.mir (bk { stA' with wk := fun _ => False }) m₂
          w := by
    intro stA' w m₂
    funext s
    by_cases hs : s = Slot.wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hne_wk_mir]
      exact (bitVal_neg not_false).symm
    · rw [Function.update_of_ne hs]
      by_cases hm : s = Slot.mir
      · subst hm
        change (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _) =
          (if (Slot.mir : dt.SlotIx) = Slot.mir then _ else _)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hm, Prog.passTracks_of_ne hm]
        match s with
        | .wk => exact absurd rfl hs
        | .mir => exact absurd rfl hm
        | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
        | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
  -- leg 7: the first reset, entered by the erasing dispatch at `cR1`
  have hrst1 := hreset st3 v (ixMark elt v) (fun ρ => rEmb .rst1 (Sum.inl ρ))
    (fun t => emb (.rst1P t)) (emb .cR1) fL hv
    (fun ρ => hrules .rst1 (Sum.inl ρ)) hwkSt
    (by obtain ⟨u, hu, -, -⟩ := hvi; exact ⟨u, hu⟩) hbotSt
    (by
      have h : PR.HasRight (emb .cR1) fL
          (PR.passTracksAt F.cell Slot.mir (bk st3) (ixMark elt v) v) (emb (.rst1P .scan)) fL
          (Function.update (PR.passTracksAt F.cell Slot.mir (bk st3) (ixMark elt v) v) Slot.wk
            PR.zero) :=
        hasRight_of_rule dt hrules (i := .cR1) (ρ := .dspA)
          (hexitG st3 v (ixMark elt v) hwkSt hvnr) rfl rfl rfl rfl trivial
      rw [herase st3 v (ixMark elt v)] at h
      exact h)
  -- leg 8: the first reset's exit into the mirror clear
  have hrst1Exit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.rst1P .done)) fL), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st5) (ixMark elt v)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.cm1P .up)) fL), Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st5) (ixMark elt v)) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin h0i (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .rst1) (ρ := Sum.inr ())
      (hexitG st5 (fun _ => False) (ixMark elt v) rfl h0nr) rfl rfl rfl rfl trivial
  -- leg 9: the mirror clear before the seek out
  have hcm1 := (ClearKit.reachesIn
    (κ := ClearKit.mk (A := A) (Q := Q) Slot.mir Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.cm1P t)))
    (fun ρ => hrules .cm1 (Sum.inl ρ)) F.toIxFile hR hlin hix (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) htop hbot
    (F.toIxFile.wmSetLt_empty_cell gbot)
    (hrgX st5) (hrlX st5) (hwk1 st5 (fun _ => False) rfl)
    (fc := fL) (s := e₁) (m := st5.mir) (hsle := he1top) (hgap := hgap)).mono hwP
  have hcm1In : PR.trackTapeAt F.cell Slot.mir (bk st5) (ixMark elt v) =
      PR.trackTapeAt F.cell Slot.mir (bk st5) st5.mir := by
    have h : st5.mir = ixMark elt v := hmirSt
    rw [h]
  have hcm1Out : PR.trackTapeAt F.cell Slot.mir (bk st5) (fun _ => False) =
      PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir := by
    refine (dt.trackTape_back_gen F (stB := st6) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st6) (stB := st6) (t := Slot.mir)
        (m := st6.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .mir => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
      | .sav | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 10: the clear's exit into the seek, and the seek's walk back
  have hcm1Exit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.cm1P .run)) fL), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.skP .chk)) fL), Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin h0i (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .cm1) (ρ := Sum.inr ())
      (hexitG st6 (fun _ => False) st6.mir rfl h0nr) rfl rfl rfl rfl trivial
  have hskBack : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.skP .chk)) fL), Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.skP .chk)) fL), Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin h0i (fun _ _ => rfl) ?_
    exact hasLeft_of_rule dt hrules (i := .sk) (ρ := Sum.inl .stayChk)
      (Or.inr (hwkOff st6 (fun _ => False) e₁ st6.mir rfl (Ne.symm h0e₁)))
      rfl rfl rfl rfl not_false
  -- leg 11: the seek to the target
  have hsk := (SeekKit.reachesIn
    (κ := SeekKit.mk (A := A) (Q := Q) Slot.mir Slot.tgt Slot.reg
      Slot.regLast Slot.wk (fun p => emb (.skP p)))
    (fun ρ => hrules .sk (Sum.inl ρ)) F.toIxFile hR hlin hix hinj hmono hup
    (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
    htop hbot (T := mT) hTh hT
    (bg := fun w => bk { st6 with wk := fun r => r = w })
    (bgN := bk { st6 with wk := fun _ => False })
    (fun _ _ => rfl) (fun _ => bitVal_neg not_false)
    (fun w r s hs => by
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fun w r => rfl)
    (fun w => hrlX { st6 with wk := fun r => r = w })
    (fun w u => bitVal_congr (F.toIxFile.bitAt_cell hix (ixMark elt mT) u))
    (fc := fL) (hgap := hgap)).mono (hwK mT hT)
  -- present the seek's landing at the far state
  have hskOut : PR.trackTapeAt F.cell Slot.mir
      (bk { st6 with wk := fun r => r = mT }) (ixMark elt mT) =
      PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir := by
    refine (dt.trackTape_back_gen F (stB := st7) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st7) (stB := st7) (t := Slot.mir)
        (m := st7.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .mir => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
      | .sav | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 12: the read under the head
  have hst7wk : st7.wk = fun r => r = mT := rfl
  have hread : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.skP .ty)) fL), Sum.inl mT,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.resP .up)) (setAv b fL (bk st7 mT))),
        Sum.inl T',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hTi (fun _ _ => rfl) ?_
    refine hasRight_of_rule dt hrules (i := .sk) (ρ := Sum.inr b)
      ⟨hexitG st7 mT st7.mir hst7wk hTnr, ?_⟩ rfl rfl ?_ rfl trivial
    · rw [Prog.passTracks_of_ne holdmir]
      exact hbT
    · change setAv b fL (PR.passTracksAt F.cell Slot.mir (bk st7) st7.mir mT) =
        setAv b fL (bk st7 mT)
      rw [passTracks_of_back F.toIxFile (t := Slot.mir) (rest := bk st7) (m := st7.mir)
        (fun _ => rfl) mT]
  -- leg 13: the restore, tgt := the saved home address
  have hres := (CopyKit.reachesIn
    (κ := CopyKit.mk (A := A) (Q := Q) Slot.tgt Slot.sav Slot.reg
      Slot.regLast Slot.wk (fun t => emb (.resP t)))
    (fun ρ => hrules .res (Sum.inl ρ)) F.toIxFile hR hlin hix (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
    htop hbot hT (hrgX st7) (hrlX st7) (hwk1 st7 mT hst7wk)
    (fun u => by
      change bitVal PR.zero PR.one (bitAtOf F.cell st7.sav (F.cell u)) = PR.zero ∨ _
      by_cases h : bitAtOf F.cell st7.sav (F.cell u)
      · exact Or.inr (bitVal_pos h)
      · exact Or.inl (bitVal_neg h))
    (fc := setAv b fL (bk st7 mT)) (s := T') (m := st7.tgt) (hsle := hT'top)
      (hgap := hgap)).mono hwP
  have hresC : (fun u : I => bk st7 (F.cell u) Slot.sav = PR.one) = ixMark elt v := by
    funext u
    refine propext ?_
    change bitVal PR.zero PR.one (bitAtOf F.cell st7.sav (F.cell u)) = PR.one ↔ _
    exact (bitVal_iff hzo).trans (F.toIxFile.bitAt_cell hix (ixMark elt v) u)
  rw [hresC] at hres
  have hresIn : PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir =
      PR.trackTapeAt F.cell Slot.tgt (bk st7) st7.tgt :=
    (trackTape_of_back F.toIxFile (t := Slot.mir) (rest := bk st7) (m := st7.mir)
      (fun _ => rfl)).trans
      (trackTape_of_back F.toIxFile (t := Slot.tgt) (rest := bk st7) (m := st7.tgt)
        (fun _ => rfl)).symm
  have hresOut : PR.trackTapeAt F.cell Slot.tgt (bk st7) (ixMark elt v) =
      PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir := by
    refine (dt.trackTape_back_gen F (stB := st8) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st8) (stB := st8) (t := Slot.mir)
        (m := st8.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .tgt => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir
      | .sav | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 14: the restore's exit and the walk back at `cR2`
  have hst8wk : st8.wk = fun r => r = mT := rfl
  have hresExit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.resP .run)) (setAv b fL (bk st7 mT))),
        Sum.inl mT,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR2) (setAv b fL (bk st7 mT))), Sum.inl T',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hTi (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .res) (ρ := Sum.inr ())
      (hexitG st8 mT st8.mir hst8wk hTnr) rfl rfl rfl rfl trivial
  have hcR2back : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb .cR2) (setAv b fL (bk st7 mT))), Sum.inl T',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR2) (setAv b fL (bk st7 mT))), Sum.inl mT,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin hTi (fun _ _ => rfl) ?_
    exact hasLeft_of_rule dt hrules (i := .cR2) (ρ := .stay)
      (hwkOff st8 mT T' st8.mir hst8wk (Ne.symm hTT')) rfl rfl rfl rfl
      not_false
  -- leg 15: the second reset, entered by the erasing dispatch at `cR2`
  have hrst2 := hreset st8 mT st8.mir (fun ρ => rEmb .rst2 (Sum.inl ρ))
    (fun t => emb (.rst2P t)) (emb .cR2) (setAv b fL (bk st7 mT)) hT
    (fun ρ => hrules .rst2 (Sum.inl ρ)) hst8wk
    (by obtain ⟨u, hu, -, -⟩ := hTi; exact ⟨u, hu⟩) hbotSt
    (by
      have h : PR.HasRight (emb .cR2) (setAv b fL (bk st7 mT))
          (PR.passTracksAt F.cell Slot.mir (bk st8) st8.mir mT)
          (emb (.rst2P .scan)) (setAv b fL (bk st7 mT))
          (Function.update (PR.passTracksAt F.cell Slot.mir (bk st8) st8.mir mT)
            Slot.wk PR.zero) :=
        hasRight_of_rule dt hrules (i := .cR2) (ρ := .dspA)
          (hexitG st8 mT st8.mir hst8wk hTnr) rfl rfl rfl rfl trivial
      rw [herase st8 mT st8.mir] at h
      exact h)
  -- leg 16: the second reset's exit and the mirror clear before the way home
  have hrst2Exit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.rst2P .done)) (setAv b fL (bk st7 mT))),
        Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st10) st8.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.cm2P .up)) (setAv b fL (bk st7 mT))),
        Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st10) st8.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin h0i (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .rst2) (ρ := Sum.inr ())
      (hexitG st10 (fun _ => False) st8.mir rfl h0nr) rfl rfl rfl rfl trivial
  have hcm2 := (ClearKit.reachesIn
    (κ := ClearKit.mk (A := A) (Q := Q) Slot.mir Slot.reg Slot.regLast
      Slot.wk (fun t => emb (.cm2P t)))
    (fun ρ => hrules .cm2 (Sum.inl ρ)) F.toIxFile hR hlin hix (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) htop hbot
    (F.toIxFile.wmSetLt_empty_cell gbot)
    (hrgX st10) (hrlX st10) (hwk1 st10 (fun _ => False) rfl)
    (fc := setAv b fL (bk st7 mT)) (s := e₁) (m := st10.mir) (hsle := he1top)
      (hgap := hgap)).mono hwP
  have hcm2In : PR.trackTapeAt F.cell Slot.mir (bk st10) st8.mir =
      PR.trackTapeAt F.cell Slot.mir (bk st10) st10.mir := rfl
  have hcm2Out : PR.trackTapeAt F.cell Slot.mir (bk st10) (fun _ => False) =
      PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir := by
    refine (dt.trackTape_back_gen F (stB := st11) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := st11) (stB := st11) (t := Slot.mir)
        (m := st11.mir) (fun _ _ _ => rfl) (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .mir => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
      | .sav | .wk | .val | .bot | .ltp | .old _ | .new _ => rfl
    · exact fun _ => rfl
  -- leg 17: the clear's exit into the seek home, and its walk back
  have hcm2Exit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.cm2P .run)) (setAv b fL (bk st7 mT))),
        Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.sk2P .chk)) (setAv b fL (bk st7 mT))),
        Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin h0i (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .cm2) (ρ := Sum.inr ())
      (hexitG st11 (fun _ => False) st11.mir rfl h0nr) rfl rfl rfl rfl
      trivial
  have hsk2Back : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.sk2P .chk)) (setAv b fL (bk st7 mT))),
        Sum.inl e₁,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir)
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.sk2P .chk)) (setAv b fL (bk st7 mT))),
        Sum.inl (fun _ => False),
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir)
          (PR.syElt PR.blank)⟩ := by
    refine Prog.step_moveBack hR hlin h0i (fun _ _ => rfl) ?_
    exact hasLeft_of_rule dt hrules (i := .sk2) (ρ := Sum.inl .stayChk)
      (Or.inr (hwkOff st11 (fun _ => False) e₁ st11.mir rfl (Ne.symm h0e₁)))
      rfl rfl rfl rfl not_false
  -- leg 18: the seek home, its target the saved home address
  have hsk2 := (SeekKit.reachesIn
    (κ := SeekKit.mk (A := A) (Q := Q) Slot.mir Slot.tgt Slot.reg
      Slot.regLast Slot.wk (fun p => emb (.sk2P p)))
    (fun ρ => hrules .sk2 (Sum.inl ρ)) F.toIxFile hR hlin hix hinj hmono hup
    (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h)
    htop hbot (T := v) hvh hv
    (bg := fun w => bk { st11 with wk := fun r => r = w })
    (bgN := bk { st11 with wk := fun _ => False })
    (fun _ _ => rfl) (fun _ => bitVal_neg not_false)
    (fun w r s hs => by
      match s with
      | .wk => exact absurd rfl hs
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl)
    (fun w r => rfl)
    (fun w => hrlX { st11 with wk := fun r => r = w })
    (fun w u => bitVal_congr (F.toIxFile.bitAt_cell hix (ixMark elt v) u))
    (fc := setAv b fL (bk st7 mT)) (hgap := hgap)).mono (hwK v hv)
  -- present the landing at the end state
  have hsk2Out : PR.trackTapeAt F.cell Slot.mir
      (bk { st11 with wk := fun r => r = v }) (ixMark elt v) =
      PR.trackTapeAt F.cell Slot.mir (bk (dt.ixStageEndSt st elt v))
        (dt.ixStageEndSt st elt v).mir := by
    refine (dt.trackTape_back_gen F (stB := dt.ixStageEndSt st elt v) ?_ ?_).trans
      ((dt.trackTape_back_gen F (stA := dt.ixStageEndSt st elt v)
        (stB := dt.ixStageEndSt st elt v) (t := Slot.mir)
        (m := (dt.ixStageEndSt st elt v).mir) (fun _ _ _ => rfl)
        (fun _ => rfl)).symm)
    · intro r s hs
      match s with
      | .mir => exact absurd rfl hs
      | .wk =>
        refine bitVal_congr ?_
        change (r = v) ↔ st.wk r
        rw [hwkSt]
      | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .tgt
      | .sav | .val | .bot | .ltp | .old _ | .new _ => rfl
    · intro r
      change bitVal PR.zero PR.one (bitAtOf F.cell st.mir r) = _
      rw [hmirSt]
  -- leg 19: the exit into the caller
  have hendwk : (dt.ixStageEndSt st elt v).wk = fun r => r = v := hwkSt
  have hsk2Exit : (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.sk2P .ty)) (setAv b fL (bk st7 mT))),
        Sum.inl v,
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (setAv b fL (bk st7 mT))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir (bk (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩ := by
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    exact hasRight_of_rule dt hrules (i := .sk2) (ρ := Sum.inr ())
      (hexitG (dt.ixStageEndSt st elt v) v (dt.ixStageEndSt st elt v).mir hendwk hvnr)
      rfl rfl rfl rfl trivial
  -- assemble the itinerary
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st) st.mir)
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.sav (bk st) st.sav) (PR.syElt PR.blank) from
    congrArg (wideTape · (PR.syElt PR.blank)) hsavIn]
  refine hsav.trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.sav (bk st) (ixMark elt v)) (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hsavOut]
  refine (TMData.reachesIn_of_step hsavExit).trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st1) st1.mir)
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.tgt (bk st1) st1.tgt) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hclrIn]
  refine hclr.trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.tgt (bk st1) (fun _ => False))
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st2) st2.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hclrOut]
  refine (TMData.reachesIn_of_step hclrExit).trans ?_
  have hmir2 : st2.mir = ixMark elt v := hmirSt
  rw [show PR.trackTapeAt F.cell Slot.mir (bk st2) st2.mir =
    PR.trackTapeAt F.cell Slot.mir (bk st2) (ixMark elt v) from congrArg _ hmir2]
  refine hLoopsIn.trans ?_
  refine (TMData.reachesIn_of_step hcR1back).trans ?_
  refine hrst1.trans ?_
  refine (TMData.reachesIn_of_step hrst1Exit).trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st5) (ixMark elt v)) (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st5) st5.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hcm1In]
  refine hcm1.trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st5) (fun _ => False))
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st6) st6.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hcm1Out]
  refine (TMData.reachesIn_of_step hcm1Exit).trans ?_
  refine (TMData.reachesIn_of_step hskBack).trans ?_
  refine TMData.ReachesIn.trans hsk ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir
      (bk { st6 with wk := fun r => r = mT }) (ixMark elt mT)) (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hskOut]
  refine (TMData.reachesIn_of_step hread).trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st7) st7.mir)
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.tgt (bk st7) st7.tgt) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hresIn]
  refine hres.trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.tgt (bk st7) (ixMark elt v)) (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st8) st8.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hresOut]
  refine (TMData.reachesIn_of_step hresExit).trans ?_
  refine (TMData.reachesIn_of_step hcR2back).trans ?_
  refine hrst2.trans ?_
  refine (TMData.reachesIn_of_step hrst2Exit).trans ?_
  refine hcm2.trans ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir (bk st10) (fun _ => False))
      (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk st11) st11.mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hcm2Out]
  refine (TMData.reachesIn_of_step hcm2Exit).trans ?_
  refine (TMData.reachesIn_of_step hsk2Back).trans ?_
  refine TMData.ReachesIn.trans hsk2 ?_
  rw [show wideTape (PR.trackTapeAt F.cell Slot.mir
      (bk { st11 with wk := fun r => r = v }) (ixMark elt v)) (PR.syElt PR.blank) =
    wideTape (PR.trackTapeAt F.cell Slot.mir (bk (dt.ixStageEndSt st elt v))
      (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)
    from congrArg (wideTape · (PR.syElt PR.blank)) hsk2Out]
  exact TMData.reachesIn_of_step hsk2Exit

include hrules hR hlin hix hinj hmono hup htop hbot hv hvi hwkSt hmirSt hbotSt
  hTh hvh hT hTi hgap hwP hwR hwK
  hLoopsIn hbT holdmir in
/-- **The stage atom's run, on a clock**: from its entry phase one cell to the
right of the marker – save, clear, the loops, the reset–clear–seek out, the
read under the head, the restore, and the reset–clear–seek home – to the exit
phase, the verdict `setAv b` in the control and the marker, mirror and save
restored at the home address. Five passes of the file, two resets, two seeks,
the loops, and the thirteen dispatches between them. -/
theorem stage_reachesIn :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn
      (5 * wP + 2 * wR + 2 * wK + wL + 13)
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (setAv b fL (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixStageAtSt st elt v mT) mT))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩ := by
  refine TMData.ReachesIn.mono ?_
    (dt.stage_reachesIn_legs (F := F) (hrules := hrules) (hR := hR) (hlin := hlin)
      (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (htop := htop)
      (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt)
      (hbotSt := hbotSt) (hTh := hTh) (hvh := hvh) (hT := hT) (hTi := hTi)
      (hgap := hgap) (wP := wP) (wR := wR) (wK := wK) (wL := wL) (hwP := hwP)
      (hwR := hwR) (hwK := hwK) (hLoopsIn := hLoopsIn) (hbT := hbT)
      (holdmir := holdmir))
  exact legs_le wP wR wK wL

end Clocked

include hrules hR hlin hix hinj hmono hup htop hbot hv hvi hwkSt hmirSt hbotSt
  hTh hvh hT hTi
  hLoops hbT holdmir in
/-- **The stage atom's run**, the budget forgotten: what a space-bounded caller
reads. The width of a trip is then the largest of the finitely many the atom
takes. -/
theorem stage_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.savP .up)) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (setAv b fL (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixStageAtSt st elt v mT) mT))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixStageEndSt st elt v))
          (dt.ixStageEndSt st elt v).mir) (PR.syElt PR.blank)⟩ := by
  obtain ⟨wL, hwL⟩ := TMData.exists_reachesIn_of_reflTransGen hLoops
  exact (dt.stage_reachesIn (F := F) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hix := hix) (hinj := hinj) (hmono := hmono) (hup := hup) (htop := htop)
    (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt) (hmirSt := hmirSt)
    (hbotSt := hbotSt) (hTh := hTh) (hvh := hvh) (hT := hT) (hTi := hTi)
    (wG := Nat.card {q : WPoint (Univ A R P dt.KIx dt.dd) //
      (wideData (Univ A R P dt.KIx dt.dd)).Posn q})
    (hgap := fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))
    (hwP := Nat.le_refl _) (wR := Nat.card {q : WPoint (Univ A R P dt.KIx dt.dd) //
      (wideData (Univ A R P dt.KIx dt.dd)).Posn q} + 4)
    (hwR := fun s _ => by
      have h := wideRank_lt_card (A := Univ A R P dt.KIx dt.dd) s
      omega)
    (hwK := fun T _ =>
      Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _
          (Nat.le_of_lt (wideRank_lt_card (A := Univ A R P dt.KIx dt.dd) T))) _) _)
    (hLoopsIn := hwL) (hbT := hbT) (holdmir := holdmir)).reflTransGen

/-! ### The chain of the copy loops

The `k` tuple loops run head to tail – position `ℓ`'s exit is
`DescriptiveComplexity.Pfp.PfpData.stageNextTup emb ℓ` – so their chain is
one induction over the positions, each round an abstract per-position run
(discharged by the copy loop's instantiation) between the walk-backs this
file's rules provide. -/

/-- The phase before the `n`-th copy loop – the first reset's checkpoint
once the positions are exhausted. -/
def stagePhaseAt (emb : StagePh k → P) (n : ℕ) : P :=
  if h : n < k then emb (.tupP ⟨n, h⟩ (.chk ⟨0, by omega⟩)) else emb .cR1

section StageChain

variable (trkOf : Fin (k + 1) → dt.SlotIx)
variable (restOf : Fin (k + 1) →
  (Univ A R P dt.KIx dt.dd → Prop) → dt.SlotIx → A)
variable (mOf : Fin (k + 1) → I → Prop)
variable (hwkOf : ∀ ℓ r, restOf ℓ r Slot.wk =
  bitVal PR.zero PR.one (r = v))
variable (hwkTrk : ∀ ℓ, (Slot.wk : dt.SlotIx) ≠ trkOf ℓ)
variable (fAt : Fin (k + 1) → Q → A)
variable (hLoop : ∀ ℓ : Fin k,
  Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
    ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
        (fAt ℓ.castSucc)), Sum.inl v,
      wideTape (PR.trackTapeAt F.cell (trkOf ℓ.castSucc) (restOf ℓ.castSucc)
        (mOf ℓ.castSucc)) (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (stageNextTup emb ℓ) (fAt ℓ.succ)), Sum.inl v',
      wideTape (PR.trackTapeAt F.cell (trkOf ℓ.succ) (restOf ℓ.succ) (mOf ℓ.succ))
        (PR.syElt PR.blank)⟩)

/-- One position of the chain: its walk-back and its loop, ahead of the
positions left. -/
private theorem chain_le (a c : ℕ) : 1 + a + c ≤ c + (a + 1) := by omega

section ClockedChain

variable (wT : ℕ)
variable (hLoopIn : ∀ ℓ : Fin k,
  (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn wT
    ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
        (fAt ℓ.castSucc)), Sum.inl v,
      wideTape (PR.trackTapeAt F.cell (trkOf ℓ.castSucc) (restOf ℓ.castSucc)
        (mOf ℓ.castSucc)) (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (stageNextTup emb ℓ) (fAt ℓ.succ)), Sum.inl v',
      wideTape (PR.trackTapeAt F.cell (trkOf ℓ.succ) (restOf ℓ.succ) (mOf ℓ.succ))
        (PR.syElt PR.blank)⟩)

omit [Finite I] in
include hrules hR hlin hvi hwkOf hwkTrk hLoopIn in
/-- **The copy loops, chained, on a clock**: from the phase entering the first
loop – one cell to the marker's right, as every dispatch leaves it – to the
first reset's checkpoint, each position's run handed to the next by its own
walk-back, and one walk-back and one loop paid per position. -/
theorem stage_loops_reachesIn :
    (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn ((wT + 1) * k)
      ⟨Sum.inr (PR.stElt (stageFirstTup emb) (fAt 0)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell (trkOf 0) (restOf 0) (mOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR1) (fAt (Fin.last k))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell (trkOf (Fin.last k)) (restOf (Fin.last k))
          (mOf (Fin.last k))) (PR.syElt PR.blank)⟩ := by
  classical
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  suffices h : ∀ (n : ℕ) (hn : n ≤ k),
      (wideData (Univ A R P dt.KIx dt.dd)).ReachesIn ((wT + 1) * (k - n))
        ⟨Sum.inr (PR.stElt (stagePhaseAt emb n)
            (fAt ⟨n, Nat.lt_succ_of_le hn⟩)), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell (trkOf ⟨n, Nat.lt_succ_of_le hn⟩)
            (restOf ⟨n, Nat.lt_succ_of_le hn⟩)
            (mOf ⟨n, Nat.lt_succ_of_le hn⟩)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb .cR1) (fAt (Fin.last k))), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell (trkOf (Fin.last k)) (restOf (Fin.last k))
            (mOf (Fin.last k))) (PR.syElt PR.blank)⟩ by
    have h0 := h 0 (Nat.zero_le k)
    rw [show stagePhaseAt emb 0 = stageFirstTup emb from rfl, Nat.sub_zero] at h0
    exact h0
  intro n hn
  induction hd : k - n generalizing n with
  | zero =>
    have hkn : n = k := by omega
    subst hkn
    have hph : stagePhaseAt emb n = emb .cR1 := dif_neg (lt_irrefl n)
    have hfk : (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (n + 1)) = Fin.last n :=
      Fin.ext rfl
    rw [hph, hfk, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | succ m ih =>
    have hkl : n < k := by omega
    set ℓ : Fin k := ⟨n, hkl⟩ with hℓ
    have hph : stagePhaseAt emb n = emb (.tupP ℓ (.chk ⟨0, by omega⟩)) :=
      dif_pos hkl
    have hcast : (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (k + 1)) = ℓ.castSucc :=
      Fin.ext rfl
    rw [hph, hcast]
    -- the walk back into the loop's entry checkpoint
    have hback : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
            (fAt ℓ.castSucc)), Sum.inl v',
          wideTape (PR.trackTapeAt F.cell (trkOf ℓ.castSucc) (restOf ℓ.castSucc)
            (mOf ℓ.castSucc)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.tupP ℓ (.chk ⟨0, by omega⟩)))
            (fAt ℓ.castSucc)), Sum.inl v,
          wideTape (PR.trackTapeAt F.cell (trkOf ℓ.castSucc) (restOf ℓ.castSucc)
            (mOf ℓ.castSucc)) (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracksAt F.cell (trkOf ℓ.castSucc) (restOf ℓ.castSucc)
          (mOf ℓ.castSucc) v' Slot.wk ≠ PR.one := by
        rw [Prog.passTracks_of_ne (hwkTrk ℓ.castSucc), hwkOf,
          bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      exact hasLeft_of_rule dt hrules
        (i := .tup ℓ (.chk ⟨0, by omega⟩)) (ρ := .stay)
        hwkv' rfl rfl rfl rfl not_false
    have hkm : k - (n + 1) = m := by omega
    rw [Nat.mul_succ]
    refine TMData.ReachesIn.mono (chain_le wT ((wT + 1) * m))
      (((TMData.reachesIn_of_step hback).trans (hLoopIn ℓ)).trans ?_)
    have hnx : stageNextTup emb ℓ = stagePhaseAt emb (n + 1) := rfl
    have hsucc : ℓ.succ = (⟨n + 1, Nat.lt_succ_of_le (by omega)⟩ :
        Fin (k + 1)) := Fin.ext rfl
    rw [hnx, hsucc]
    exact hkm ▸ ih (n + 1) (by omega) hkm


end ClockedChain

omit [Finite I] in
include hrules hR hlin hvi hwkOf hwkTrk hLoop in
/-- **The copy loops, chained**, the budget forgotten: from the phase entering
the first loop – one cell to the marker's right, as every dispatch leaves it –
to the first reset's checkpoint, each position's run handed to the next by its
own walk-back. -/
theorem stage_loops_run :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (stageFirstTup emb) (fAt 0)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell (trkOf 0) (restOf 0) (mOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb .cR1) (fAt (Fin.last k))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell (trkOf (Fin.last k)) (restOf (Fin.last k))
          (mOf (Fin.last k))) (PR.syElt PR.blank)⟩ := by
  classical
  choose wOf hwOf using fun ℓ : Fin k =>
    TMData.exists_reachesIn_of_reflTransGen (hLoop ℓ)
  exact (dt.stage_loops_reachesIn (F := F) (hrules := hrules) (hR := hR)
    (hlin := hlin) (hvi := hvi) (trkOf := trkOf) (restOf := restOf) (mOf := mOf)
    (hwkOf := hwkOf) (hwkTrk := hwkTrk) (fAt := fAt) (wT := Finset.univ.sup wOf)
    (hLoopIn := fun ℓ =>
      (hwOf ℓ).mono (Finset.le_sup (Finset.mem_univ ℓ)))).reflTransGen

end StageChain

/-! ### The elementwise instantiation

The space-bounded program's file is the input channel's ruler, one register per
element: the runs above are that file at the identity embedding, and these are
the statements their callers had before the file became a parameter.
-/


end StageRun

section Diag

variable {L : Language.{0, 0}} {dt : PfpData L} {A R P Q : Type} {k : ℕ}
variable [Fintype Q] [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P Q dt.SlotIx dt.KIx dt.dd}
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)

omit [Finite A] [Finite R] [Finite P] in
/-- **The far state of the random access at the elementwise file.** -/
noncomputable def stageAtSt (st : TapeStD dt A R P)
    (v mT : Univ A R P dt.KIx dt.dd → Prop) : TapeStD dt A R P :=
  dt.ixStageAtSt st id v mT

/-- **The state the random access returns in, at the elementwise file.** -/
noncomputable def stageEndSt (st : TapeStD dt A R P)
    (v : Univ A R P dt.KIx dt.dd → Prop) : TapeStD dt A R P :=
  dt.ixStageEndSt st id v

omit [Finite A] [Finite R] [Finite P] in
include hord in
/-- **A leg's after-tape at the elementwise file.** -/
theorem trackTape_back_gen_diag {stA stB : TapeStD dt A R P} {t : dt.SlotIx}
    {m : Univ A R P dt.KIx dt.dd → Prop}
    (hagree : ∀ r s, s ≠ t →
      dt.back RF.cell PR.zero PR.one dt.dd0Le stA r s =
        dt.back RF.cell PR.zero PR.one dt.dd0Le stB r s)
    (ht : ∀ r, dt.back RF.cell PR.zero PR.one dt.dd0Le stB r t =
      bitVal PR.zero PR.one (bitAtOf RF.cell m r)) :
    PR.trackTapeAt RF.cell t (dt.back RF.cell PR.zero PR.one dt.dd0Le stA) m =
      fun r => PR.syElt (dt.back RF.cell PR.zero PR.one dt.dd0Le stB r) :=
  dt.trackTape_back_gen (dt.diagLaid RF hord) hagree ht

end Diag

end PfpData

end Pfp

end DescriptiveComplexity
