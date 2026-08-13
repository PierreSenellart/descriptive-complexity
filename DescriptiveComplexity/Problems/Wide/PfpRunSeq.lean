/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpSeq
import DescriptiveComplexity.Problems.Wide.PfpRunElem

/-!
# The sequencer's run

The run theorem of `DescriptiveComplexity.Pfp.seqRule`: from the checkpoint
before the first stage at the marker, one abstract stage run per position,
to the exit phase one cell to the marker's right after the last – the
matrix runs its classified atoms with it, the gates their blocks, and
neither needs to know a stage's internals beyond its entry phase and its
control and tape transforms.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

section SeqRun

variable {A R P Q W K : Type} {dd : ℕ} {n : ℕ}
variable {PA : Fin n → Type} {SA : Fin n → Type}
variable {ShA : ∀ a : Fin n, SA a → Type}
variable [Fintype Q] [Fintype W] [DecidableEq W]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {PR : Prog A R P Q W K dd}
variable {wk rg : W} {emb : SeqPh n PA → P}
variable {ruleA : ∀ (a : Fin n) (s : SA a), ShA a s → Rule A Q W P}
variable {entry : ∀ a : Fin n, PA a}
variable {enterSt : Fin n → (Q → A) → (W → A) → (Q → A)}
variable {exitPh : P}
variable {rEmb : ∀ i : SeqSite n SA, SeqSh n ShA i → R}
variable (hrules : ∀ (i : SeqSite n SA) (ρ : SeqSh n ShA i),
  PR.rules (rEmb i ρ) = seqRule PR.one wk rg emb ruleA entry enterSt exitPh
    i ρ)

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the sequence with a true guard is a `HasRight` witness. -/
private theorem hasRight_of_rule {i : SeqSite n SA} {ρ : SeqSh n ShA i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).guard f g)
    (hp : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).srcPh = p)
    (hp' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).dstPh = p')
    (hf' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).dstSt f g
      = f')
    (hg' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).wr f g
      = g')
    (hmr : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i
      ρ).moveRight) :
    PR.HasRight p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'], by rw [hrules]; exact hmr⟩

omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [LinearOrder K] [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A rule of the sequence with a true guard is a `HasLeft` witness. -/
private theorem hasLeft_of_rule {i : SeqSite n SA} {ρ : SeqSh n ShA i}
    {f f' : Q → A} {g g' : W → A} {p p' : P}
    (hg : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).guard f g)
    (hp : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).srcPh = p)
    (hp' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).dstPh = p')
    (hf' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).dstSt f g
      = f')
    (hg' : (seqRule PR.one wk rg emb ruleA entry enterSt exitPh i ρ).wr f g
      = g')
    (hml : ¬(seqRule PR.one wk rg emb ruleA entry enterSt exitPh i
      ρ).moveRight) :
    PR.HasLeft p f g p' f' g' :=
  ⟨rEmb i ρ, by rw [hrules]; exact hg, by rw [hrules, hp], by rw [hrules, hp'],
    by rw [hrules, hf'], by rw [hrules, hg'],
    fun hc => hml (by rw [hrules] at hc; exact hc)⟩

variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))
variable {gbot : Univ A R P K dd} (hbot : ∀ y, WMLe gbot y)
variable {v v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (wmSeg gbot))
variable (hvi : WMIncr WMLe v v')
variable {t₀ : W}
variable {restOf : Fin (n + 1) → (Univ A R P K dd → Prop) → W → A}
variable {mOf : Fin (n + 1) → Univ A R P K dd → Prop}
variable (hwkOf : ∀ k r, restOf k r wk = bitVal PR.zero PR.one (r = v))
variable (hrgOf : ∀ k r, restOf k r rg = bitVal PR.zero PR.one
  (∃ u : Univ A R P K dd, r = wmSeg u))
variable (hmOf : ∀ k r, restOf k r t₀ =
  bitVal PR.zero PR.one (regBit (mOf k) r))
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)
variable (fs : Fin (n + 1) → Q → A)
variable (hStage : ∀ a : Fin n,
  Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
    ⟨Sum.inr (PR.stElt (emb (.sub a (entry a)))
        (enterSt a (fs a.castSucc) (restOf a.castSucc v))), Sum.inl v',
      wideTape (PR.trackTape t₀ (restOf a.castSucc) (mOf a.castSucc))
        (PR.syElt PR.blank)⟩
    ⟨Sum.inr (PR.stElt (emb (.chk a.succ)) (fs a.succ)), Sum.inl v',
      wideTape (PR.trackTape t₀ (restOf a.succ) (mOf a.succ))
        (PR.syElt PR.blank)⟩)

include hrules hR hlin hbot hv hvi hwkOf hrgOf hmOf hwkt₀ hrgt₀ hStage in
/-- **The sequencer's run**: from the checkpoint before the first stage at
the marker to the exit phase one cell to its right after the last stage. -/
theorem seq_run :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTape t₀ (restOf 0) (mOf 0)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (fs (Fin.last n))), Sum.inl v',
        wideTape (PR.trackTape t₀ (restOf (Fin.last n)) (mOf (Fin.last n)))
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  -- guard facts at the marker
  have hgwk : ∀ k : Fin (n + 1),
      PR.passTracks t₀ (restOf k) (mOf k) v wk = PR.one := by
    intro k
    rw [Prog.passTracks_of_ne hwkt₀, hwkOf]
    exact bitVal_pos rfl
  have hgrg : ∀ k : Fin (n + 1),
      PR.passTracks t₀ (restOf k) (mOf k) v rg ≠ PR.one := by
    intro k
    rw [Prog.passTracks_of_ne hrgt₀, hrgOf,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  -- the chain up to the last checkpoint
  have hchain : ∀ (k : ℕ) (hk : k ≤ n),
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk ⟨k, Nat.lt_succ_of_le hk⟩))
            (fs ⟨k, Nat.lt_succ_of_le hk⟩)), Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf ⟨k, Nat.lt_succ_of_le hk⟩)
            (mOf ⟨k, Nat.lt_succ_of_le hk⟩)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk (Fin.last n))) (fs (Fin.last n))),
          Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf (Fin.last n)) (mOf (Fin.last n)))
            (PR.syElt PR.blank)⟩ := by
    intro k hk
    induction hd : n - k generalizing k with
    | zero =>
      have hkn : k = n := by omega
      subst hkn
      have hfk : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (k + 1)) = Fin.last k :=
        Fin.ext rfl
      rw [hfk]
    | succ m ih =>
      have hkl : k < n := by omega
      set j : Fin n := ⟨k, hkl⟩ with hj
      have hcast : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) = j.castSucc :=
        Fin.ext rfl
      rw [hcast]
      have hdsp : (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (emb (.chk j.castSucc)) (fs j.castSucc)),
            Sum.inl v,
            wideTape (PR.trackTape t₀ (restOf j.castSucc) (mOf j.castSucc))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (emb (.sub j (entry j)))
              (enterSt j (fs j.castSucc) (restOf j.castSucc v))), Sum.inl v',
            wideTape (PR.trackTape t₀ (restOf j.castSucc) (mOf j.castSucc))
              (PR.syElt PR.blank)⟩ := by
        refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
        refine hasRight_of_rule hrules (i := .chk j.castSucc) (ρ := .dspA)
          ?_ ?_ ?_ ?_ ?_ ?_
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
          exact ⟨hgwk j.castSucc, hgrg j.castSucc⟩
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
          rfl
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
          change enterSt j (fs j.castSucc)
            (PR.passTracks t₀ (restOf j.castSucc) (mOf j.castSucc) v) = _
          rw [passTracks_of_back (hmOf j.castSucc) v]
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
        · rw [seqRule, dif_pos (show ((j.castSucc : Fin (n + 1)) : ℕ) < n
            from hkl)]
          trivial
      have hback : (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (emb (.chk j.succ)) (fs j.succ)), Sum.inl v',
            wideTape (PR.trackTape t₀ (restOf j.succ) (mOf j.succ))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (emb (.chk j.succ)) (fs j.succ)), Sum.inl v,
            wideTape (PR.trackTape t₀ (restOf j.succ) (mOf j.succ))
              (PR.syElt PR.blank)⟩ := by
        have hwkv' : PR.passTracks t₀ (restOf j.succ) (mOf j.succ) v' wk ≠
            PR.one := by
          rw [Prog.passTracks_of_ne hwkt₀, hwkOf, bitVal_neg (Ne.symm hvv')]
          exact PR.zero_ne_one
        refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
        exact hasLeft_of_rule hrules (i := .chk j.succ) (ρ := .stay)
          hwkv' rfl rfl rfl rfl not_false
      have hsucc : j.succ = (⟨k + 1, Nat.lt_succ_of_le (by omega)⟩ :
          Fin (n + 1)) := Fin.ext rfl
      refine ((Relation.ReflTransGen.single hdsp).trans
        ((hStage j).trans (Relation.ReflTransGen.single hback))).trans ?_
      rw [hsucc]
      exact ih (k + 1) (by omega) (by omega)
  -- the exit dispatch after the last stage
  have hexit : (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk (Fin.last n))) (fs (Fin.last n))),
        Sum.inl v,
        wideTape (PR.trackTape t₀ (restOf (Fin.last n)) (mOf (Fin.last n)))
          (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh (fs (Fin.last n))), Sum.inl v',
        wideTape (PR.trackTape t₀ (restOf (Fin.last n)) (mOf (Fin.last n)))
          (PR.syElt PR.blank)⟩ := by
    have hnl : ¬((Fin.last n : Fin (n + 1)) : ℕ) < n := by
      simp [Fin.last]
    refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
    refine hasRight_of_rule hrules (i := .chk (Fin.last n)) (ρ := .dspA)
      ?_ ?_ ?_ ?_ ?_ ?_
    · rw [seqRule, dif_neg hnl]
      exact ⟨hgwk (Fin.last n), hgrg (Fin.last n)⟩
    · rw [seqRule, dif_neg hnl]
    · rw [seqRule, dif_neg hnl]
    · rw [seqRule, dif_neg hnl]
    · rw [seqRule, dif_neg hnl]
    · rw [seqRule, dif_neg hnl]
      trivial
  exact (hchain 0 (Nat.zero_le n)).trans (Relation.ReflTransGen.single hexit)

omit hStage in
include hrules hR hlin hbot hv hvi hwkOf hrgOf hmOf hwkt₀ hrgt₀ in
/-- **The sequencer's prefix**: from the checkpoint before the first stage
to any later checkpoint, given the stages strictly below it – what a run
that leaves the sequence early (a failing gate block) composes with. -/
theorem seq_run_prefix (j : Fin (n + 1))
    (hStageLt : ∀ a : Fin n, (a : ℕ) < (j : ℕ) →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.sub a (entry a)))
            (enterSt a (fs a.castSucc) (restOf a.castSucc v))), Sum.inl v',
          wideTape (PR.trackTape t₀ (restOf a.castSucc) (mOf a.castSucc))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk a.succ)) (fs a.succ)), Sum.inl v',
          wideTape (PR.trackTape t₀ (restOf a.succ) (mOf a.succ))
            (PR.syElt PR.blank)⟩) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) (fs 0)), Sum.inl v,
        wideTape (PR.trackTape t₀ (restOf 0) (mOf 0)) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (emb (.chk j)) (fs j)), Sum.inl v,
        wideTape (PR.trackTape t₀ (restOf j) (mOf j)) (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hvv' : v ≠ v' := ne_of_wmIncr hvi
  have hgwk : ∀ k : Fin (n + 1),
      PR.passTracks t₀ (restOf k) (mOf k) v wk = PR.one := by
    intro k
    rw [Prog.passTracks_of_ne hwkt₀, hwkOf]
    exact bitVal_pos rfl
  have hgrg : ∀ k : Fin (n + 1),
      PR.passTracks t₀ (restOf k) (mOf k) v rg ≠ PR.one := by
    intro k
    rw [Prog.passTracks_of_ne hrgt₀, hrgOf,
      bitVal_neg (fun hc => hvnr hc.choose hc.choose_spec)]
    exact PR.zero_ne_one
  suffices h : ∀ (m : ℕ) (hm : m ≤ n),
      (∀ a : Fin n, (a : ℕ) < m →
        Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
          ⟨Sum.inr (PR.stElt (emb (.sub a (entry a)))
              (enterSt a (fs a.castSucc) (restOf a.castSucc v))), Sum.inl v',
            wideTape (PR.trackTape t₀ (restOf a.castSucc) (mOf a.castSucc))
              (PR.syElt PR.blank)⟩
          ⟨Sum.inr (PR.stElt (emb (.chk a.succ)) (fs a.succ)), Sum.inl v',
            wideTape (PR.trackTape t₀ (restOf a.succ) (mOf a.succ))
              (PR.syElt PR.blank)⟩) →
      Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk 0)) (fs 0)), Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf 0) (mOf 0)) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk ⟨m, Nat.lt_succ_of_le hm⟩))
            (fs ⟨m, Nat.lt_succ_of_le hm⟩)), Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf ⟨m, Nat.lt_succ_of_le hm⟩)
            (mOf ⟨m, Nat.lt_succ_of_le hm⟩)) (PR.syElt PR.blank)⟩ by
    have hj := h (j : ℕ) (Nat.lt_succ_iff.mp j.isLt) hStageLt
    have hfj : (⟨(j : ℕ), Nat.lt_succ_of_le (Nat.lt_succ_iff.mp j.isLt)⟩ :
        Fin (n + 1)) = j := Fin.ext rfl
    rw [hfj] at hj
    exact hj
  intro m
  induction m with
  | zero =>
    intro hm hSt
    exact Relation.ReflTransGen.refl
  | succ m ih =>
    intro hm hSt
    have hml : m < n := by omega
    set a : Fin n := ⟨m, hml⟩ with ha
    have haval : (a : ℕ) = m := rfl
    have hcast : (⟨m, Nat.lt_succ_of_le (by omega)⟩ : Fin (n + 1)) =
        a.castSucc := Fin.ext rfl
    refine (ih (by omega) (fun a' ha' => hSt a' (by omega))).trans ?_
    rw [hcast]
    have hdsp : (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk a.castSucc)) (fs a.castSucc)),
          Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf a.castSucc) (mOf a.castSucc))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub a (entry a)))
            (enterSt a (fs a.castSucc) (restOf a.castSucc v))), Sum.inl v',
          wideTape (PR.trackTape t₀ (restOf a.castSucc) (mOf a.castSucc))
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      refine hasRight_of_rule hrules (i := .chk a.castSucc) (ρ := .dspA)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
        exact ⟨hgwk a.castSucc, hgrg a.castSucc⟩
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
        rfl
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
        change enterSt a (fs a.castSucc)
          (PR.passTracks t₀ (restOf a.castSucc) (mOf a.castSucc) v) = _
        rw [passTracks_of_back (hmOf a.castSucc) v]
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
      · rw [seqRule, dif_pos (show ((a.castSucc : Fin (n + 1)) : ℕ) < n
          from hml)]
        trivial
    have hback : (wideData (Univ A R P K dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk a.succ)) (fs a.succ)), Sum.inl v',
          wideTape (PR.trackTape t₀ (restOf a.succ) (mOf a.succ))
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.chk a.succ)) (fs a.succ)), Sum.inl v,
          wideTape (PR.trackTape t₀ (restOf a.succ) (mOf a.succ))
            (PR.syElt PR.blank)⟩ := by
      have hwkv' : PR.passTracks t₀ (restOf a.succ) (mOf a.succ) v' wk ≠
          PR.one := by
        rw [Prog.passTracks_of_ne hwkt₀, hwkOf, bitVal_neg (Ne.symm hvv')]
        exact PR.zero_ne_one
      refine Prog.step_moveBack hR hlin hvi (fun _ _ => rfl) ?_
      exact hasLeft_of_rule hrules (i := .chk a.succ) (ρ := .stay)
        hwkv' rfl rfl rfl rfl not_false
    have hsucc : a.succ = (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (n + 1)) :=
      Fin.ext rfl
    rw [← hsucc]
    exact ((Relation.ReflTransGen.single hdsp).trans
      (hSt a (by omega))).trans (Relation.ReflTransGen.single hback)

end SeqRun

end Pfp

end DescriptiveComplexity
