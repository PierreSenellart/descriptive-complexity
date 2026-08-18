/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRunVar

/-!
# The evaluation spine's run

The run theorem of `DescriptiveComplexity.Draw.Data.evalRule`: from the
checkpoint before the first variable to the checkpoint after the last, one
abstract sub-machinery run per position – the spine contributes only its
dispatches and walk-backs, so it needs to know nothing about a machinery's
internals beyond its entry phase, its control transform and its tape
transform.

The run comes **with its cost** (`eval_reachesIn`): one machinery's width plus
its dispatch and its walk back, once per variable. `eval_run` is it with the
budget forgotten.

The two boundary steps at the last checkpoint – erase the marker rightwards
into the sweep's advance, or into the post-sweep reset at the `ltp` cell –
are separate single-step lemmas, consumed by the outer composition.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L)
variable {A R Q PM SM : Type} {nv : ℕ}
variable [Fintype Q] [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R]
variable [LinearOrder (OuterPh (EvalPh nv PM))]
variable [Language.wide.Structure
  (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite (OuterPh (EvalPh nv PM))]
variable {ShM : SM → Type}
variable {PR : Prog A R (OuterPh (EvalPh nv PM)) Q dt.SlotIx dt.KIx dt.dd}
variable {I : Type} {ile : I → I → Prop}
variable (RF : IxFile (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd) I ile)

section EvalRun

variable {ruleM : ∀ s : SM, ShM s →
  Rule A Q dt.SlotIx (OuterPh (EvalPh nv PM))}
variable {subEntry : Fin nv → PM}
variable {rEmb : ∀ i : EvalSite nv SM, EvalSh nv SM ShM i → R}
variable (hrules : ∀ (i : EvalSite nv SM) (ρ : EvalSh nv SM ShM i),
  PR.rules (rEmb i ρ) = dt.evalRule PR.zero PR.one ruleM subEntry i ρ)

omit [LinearOrder A] [LinearOrder R] [LinearOrder (OuterPh (EvalPh nv PM))]
  [Language.wide.Structure (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh nv PM))] in
include hrules in
/-- A spine rule with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : EvalSite nv SM} {ρ : EvalSh nv SM ShM i}
    {f f' : Q → A} {g g' : dt.SlotIx → A}
    {p p' : OuterPh (EvalPh nv PM)}
    (hg : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).guard f g)
    (hp : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).srcPh = p)
    (hp' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).dstPh = p')
    (hf' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).dstSt f g = f')
    (hg' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).wr f g = g')
    (hmr : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [LinearOrder A] [LinearOrder R] [LinearOrder (OuterPh (EvalPh nv PM))]
  [Language.wide.Structure (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (OuterPh (EvalPh nv PM))] in
include hrules in
/-- A spine rule with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : EvalSite nv SM} {ρ : EvalSh nv SM ShM i}
    {f f' : Q → A} {g g' : dt.SlotIx → A}
    {p p' : OuterPh (EvalPh nv PM)}
    (hg : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).guard f g)
    (hp : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).srcPh = p)
    (hp' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).dstPh = p')
    (hf' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).dstSt f g = f')
    (hg' : (dt.evalRule PR.zero PR.one ruleM subEntry i ρ).wr f g = g')
    (hml : ¬(dt.evalRule PR.zero PR.one ruleM subEntry i ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)))
variable (hix : IsLinOrd ile)
variable {gbot : I}
variable (hbot : ∀ y, ile gbot y)
-- The program's working area lies below its file. Which addresses count as
-- working ones is the caller's to say – at the elementwise file it is «misses
-- the least element» (`wmSetLt_wmSeg_of_not_bot`) – so the predicate is a
-- parameter, and the one thing asked of it is that its addresses lie below
-- every register.
variable {WorkAddr : (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd → Prop) → Prop}
variable (hwork : ∀ {r : Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd → Prop}, WorkAddr r →
  ∀ u, WMSetLt WMLe r (RF.cell u))
variable {v v' : Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (RF.cell gbot)) (hvi : WMIncr WMLe v v')
variable {restOf : Fin (nv + 1) →
  (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable {mvOf : Fin (nv + 1) → I → Prop}
variable (hwkOf : ∀ k r, restOf k r Slot.wk = bitVal PR.zero PR.one (r = v))
variable (hrgOf : ∀ k r, restOf k r Slot.reg = bitVal PR.zero PR.one
  (∃ u : I, r = RF.cell u))
variable (fs : Fin (nv + 1) → Q → A)
-- The width of one variable's machinery: a clocked caller supplies it, a
-- space-bounded one takes the largest of the finitely many runs it has.
variable (w : ℕ)
variable (hVar : ∀ k : Fin nv,
  (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn w
    ⟨Sum.inr (PR.stElt (.evalP (.sub (subEntry k))) (fs k.castSucc)),
      Sum.inl v',
      wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.castSucc) (mvOf k.castSucc))
        (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (.evalP (.chk k.succ)) (fs k.succ)), Sum.inl v',
      wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.succ) (mvOf k.succ))
        (PR.syElt PR.blank)⟩)

include hrules hR hlin hix hbot hv hvi hwkOf hrgOf hVar in
/-- **The spine's run, on a clock**: from the checkpoint before the first
variable at the marker to the checkpoint after the last, one machinery run per
position, each with its dispatch and its walk back. -/
theorem eval_reachesIn :
    (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn
      ((w + 2) * nv)
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf 0) (mvOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
          (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  suffices h : ∀ (k : ℕ) (hk : k ≤ nv),
      (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).ReachesIn
        ((w + 2) * (nv - k))
        ⟨Sum.inr (PR.stElt (.evalP (.chk ⟨k, Nat.lt_succ_of_le hk⟩))
            (fs ⟨k, Nat.lt_succ_of_le hk⟩)), Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf ⟨k, Nat.lt_succ_of_le hk⟩)
            (mvOf ⟨k, Nat.lt_succ_of_le hk⟩)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
          Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
            (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ by
    have h0 := h 0 (Nat.zero_le nv)
    rw [Nat.sub_zero] at h0
    exact h0
  intro k hk
  induction hd : nv - k generalizing k with
  | zero =>
    have hkn : k = nv := by omega
    subst hkn
    have hfk : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (k + 1)) = Fin.last k :=
      Fin.ext rfl
    rw [hfk, Nat.mul_zero]
    exact TMData.reachesIn_refl
  | succ n ih =>
    have hkl : k < nv := by omega
    set j : Fin nv := ⟨k, hkl⟩ with hj
    have hcast : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (nv + 1)) = j.castSucc :=
      Fin.ext rfl
    rw [hcast]
    -- the dispatch into variable `j`'s machinery
    have hdsp : (wideData
        (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (.evalP (.chk j.castSucc)) (fs j.castSucc)),
          Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.castSucc)
            (mvOf j.castSucc)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (.evalP (.sub (subEntry j))) (fs j.castSucc)),
          Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.castSucc)
            (mvOf j.castSucc)) (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule dt hrules (i := .chk j.castSucc) (ρ := .dspA)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        constructor
        · rw [Prog.passTracks_of_ne hne_wk_val, hwkOf]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne hne_reg_val, hrgOf,
            bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
          exact PR.zero_ne_one
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        rfl
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
      · rw [evalRule, dif_pos (show ((j.castSucc : Fin (nv + 1)) : ℕ) < nv
          from hkl)]
        trivial
    -- the machinery's run, and the walk back at the next checkpoint
    have hback : (wideData
        (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ)) (fs j.succ)), Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (.evalP (.chk j.succ)) (fs j.succ)), Sum.inl v,
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ))
            (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracksAt RF.cell Slot.val (restOf j.succ) (mvOf j.succ) v'
          Slot.wk ≠ PR.one := by
        rw [Prog.passTracks_of_ne hne_wk_val, hwkOf,
          bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      exact hasLeft_of_rule dt hrules (i := .chk j.succ) (ρ := .stay)
        hwkv' rfl rfl rfl rfl not_false
    have hsucc : j.succ = (⟨k + 1, Nat.lt_succ_of_le (by omega)⟩ :
        Fin (nv + 1)) := Fin.ext rfl
    refine TMData.ReachesIn.mono
      (show 1 + (w + (1 + (w + 2) * n)) ≤ (w + 2) * (n + 1) by
        rw [Nat.mul_succ]; omega) ?_
    refine (TMData.reachesIn_of_step hdsp).trans ?_
    refine (hVar j).trans ?_
    refine (TMData.reachesIn_of_step hback).trans ?_
    rw [hsucc]
    exact ih (k + 1) (by omega) (by omega)

omit hVar in
include hrules hR hlin hix hbot hv hvi hwkOf hrgOf in
/-- **The spine's run**, the budget forgotten: what a space-bounded caller
reads, its machineries' runs carrying no count. -/
theorem eval_run
    (hVarR : ∀ k : Fin nv,
      Relation.ReflTransGen
        (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (.evalP (.sub (subEntry k))) (fs k.castSucc)),
          Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.castSucc)
            (mvOf k.castSucc)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (.evalP (.chk k.succ)) (fs k.succ)), Sum.inl v',
          wideTape (PR.trackTapeAt RF.cell Slot.val (restOf k.succ) (mvOf k.succ))
            (PR.syElt PR.blank)⟩) :
    Relation.ReflTransGen
      (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf 0) (mvOf 0))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) (fs (Fin.last nv))),
        Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val (restOf (Fin.last nv))
          (mvOf (Fin.last nv))) (PR.syElt PR.blank)⟩ := by
  classical
  choose wOf hwOf using fun k : Fin nv =>
    TMData.exists_reachesIn_of_reflTransGen (hVarR k)
  exact (dt.eval_reachesIn RF hrules hR hlin hix hbot hv hvi hwkOf hrgOf fs
    (Finset.univ.sup wOf)
    (fun k => (hwOf k).mono (Finset.le_sup (Finset.mem_univ k)))).reflTransGen

variable {mvT : I → Prop}
variable {restT restT' :
  (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd → Prop) → dt.SlotIx → A}
variable (hwkT : ∀ r, restT r Slot.wk = bitVal PR.zero PR.one (r = v))
variable (hrgT : ∀ r, restT r Slot.reg = bitVal PR.zero PR.one
  (∃ u : I, r = RF.cell u))
variable (hoffT : ∀ r, r ≠ v → restT' r = restT r)
variable (hupdT : restT' v = Function.update (restT v) Slot.wk PR.zero)

omit hrules hbot hv hwkT hrgT in
include hlin hvi hoffT hupdT in
/-- **The written marker-erasing step**, shared by the two boundary
dispatches: the guard facts, and the after-tape read against the erased
background. -/
private theorem boundary_step {ρ : EvalChkRule} {f : Q → A}
    {p' : OuterPh (EvalPh nv PM)}
    (hR : PR.table.Reads)
    (hrules : ∀ (i : EvalSite nv SM) (ρ : EvalSh nv SM ShM i),
      PR.rules (rEmb i ρ) = dt.evalRule PR.zero PR.one ruleM subEntry i ρ)
    (hg : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).guard f (PR.passTracksAt RF.cell Slot.val restT mvT v))
    (hp' : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).dstPh = p')
    (hf' : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).dstSt f (PR.passTracksAt RF.cell Slot.val restT mvT v) = f)
    (hg' : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).wr f (PR.passTracksAt RF.cell Slot.val restT mvT v) =
        Function.update (PR.passTracksAt RF.cell Slot.val restT mvT v) Slot.wk PR.zero)
    (hsp : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).srcPh = .evalP (.chk (Fin.last nv)))
    (hmr : (dt.evalRule PR.zero PR.one ruleM subEntry (.chk (Fin.last nv))
      ρ).moveRight) :
    (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val restT mvT) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt p' f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val restT' mvT) (PR.syElt PR.blank)⟩ := by
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hupd : Function.update (PR.passTracksAt RF.cell Slot.val restT mvT v)
      Slot.wk PR.zero = PR.passTracksAt RF.cell Slot.val restT' mvT v := by
    funext s
    by_cases hs : s = Slot.wk
    · subst hs
      rw [Function.update_self, Prog.passTracks_of_ne hne_wk_val, hupdT,
        Function.update_self]
    · rw [Function.update_of_ne hs]
      by_cases hsv : s = Slot.val
      · rw [hsv]
        change (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (bitAtOf RF.cell mvT v) else restT v Slot.val) =
          (if (Slot.val : dt.SlotIx) = Slot.val
            then bitVal PR.zero PR.one (bitAtOf RF.cell mvT v) else restT' v Slot.val)
        rw [if_pos rfl, if_pos rfl]
      · rw [Prog.passTracks_of_ne hsv, Prog.passTracks_of_ne hsv, hupdT,
          Function.update_of_ne hs]
  refine Prog.step_move hR hlin hvi hoffT ?_
  have h := hasRight_of_rule dt hrules (i := .chk (Fin.last nv)) (ρ := ρ)
    hg hsp hp' hf' hg' hmr
  rw [hupd] at h
  exact h

include hrules hR hlin hix hbot hv hvi hwkT hrgT hoffT hupdT in
/-- **The boundary step into the sweep's advance**: at the last checkpoint,
below the `ltp` cell, erase the marker and step right. -/
theorem step_eval_adv {f : Q → A}
    (hltp : PR.passTracksAt RF.cell Slot.val restT mvT v Slot.ltp ≠ PR.one) :
    (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val restT mvT) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.advP .a1) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val restT' mvT) (PR.syElt PR.blank)⟩ := by
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hnl : ¬((Fin.last nv : Fin (nv + 1)) : ℕ) < nv := by
    simp [Fin.last]
  refine boundary_step dt RF hlin hvi hoffT hupdT
    (ρ := .dspA) hR hrules ?_ ?_ ?_ ?_ ?_ ?_
  · rw [evalRule, dif_neg hnl]
    refine ⟨⟨?_, ?_⟩, hltp⟩
    · rw [Prog.passTracks_of_ne hne_wk_val, hwkT]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_val, hrgT,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact PR.zero_ne_one
  · rw [evalRule, dif_neg hnl]
  · rw [evalRule, dif_neg hnl]
  · rw [evalRule, dif_neg hnl]
  · rw [evalRule, dif_neg hnl]
  · rw [evalRule, dif_neg hnl]
    trivial

include hrules hR hlin hix hbot hv hvi hwkT hrgT hoffT hupdT in
/-- **The boundary step into the post-sweep reset**: at the last checkpoint,
on the `ltp` cell, erase the marker and step right. -/
theorem step_eval_reset {f : Q → A}
    (hltp : PR.passTracksAt RF.cell Slot.val restT mvT v Slot.ltp = PR.one) :
    (wideData (Univ A R (OuterPh (EvalPh nv PM)) dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (.evalP (.chk (Fin.last nv))) f), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell Slot.val restT mvT) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (.reset2P .scan) f), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell Slot.val restT' mvT) (PR.syElt PR.blank)⟩ := by
  have hvnr := not_reg_of_lt_bot RF hlin hix hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_reg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hnl : ¬((Fin.last nv : Fin (nv + 1)) : ℕ) < nv := by
    simp [Fin.last]
  refine boundary_step dt RF hlin hvi hoffT hupdT
    (ρ := .dspB) hR hrules ?_ ?_ ?_ ?_ ?_ ?_
  · rw [evalRule, if_neg hnl]
    refine ⟨⟨?_, ?_⟩, hltp⟩
    · rw [Prog.passTracks_of_ne hne_wk_val, hwkT]
      exact bitVal_pos rfl
    · rw [Prog.passTracks_of_ne hne_reg_val, hrgT,
        bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
      exact PR.zero_ne_one
  · rw [evalRule, if_neg hnl]
  · rw [evalRule, if_neg hnl]
  · rw [evalRule, if_neg hnl]
  · rw [evalRule, if_neg hnl]
  · rw [evalRule, if_neg hnl]
    trivial

end EvalRun

end Data

end Draw

end DescriptiveComplexity
