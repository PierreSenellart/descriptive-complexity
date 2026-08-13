/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpInstMat
import DescriptiveComplexity.Problems.Wide.PfpRunSeq
import DescriptiveComplexity.Problems.Wide.PfpCmp

/-!
# The atom kinds, dispatched: one stage interface for the matrix

The matrix's sequencer treats every classified atom alike; this file makes
that literal. `DescriptiveComplexity.Pfp.PfpData.KindSem` carries the one
piece of semantic data a kind's run needs (the encoded points, for an
expansion atom – the others need none),
`DescriptiveComplexity.Pfp.PfpData.kindExitCtl` is the control each kind's
machinery leaves behind, and
`DescriptiveComplexity.Pfp.PfpData.kind_hStage` is the uniform stage
discharge: whatever the kind, from the machinery's entry phase one cell
right of the marker to the exit phase back there, at the `Slot.val`-walked
presentation – the shape `DescriptiveComplexity.Pfp.seq_run` consumes.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### Generic slot-preservation through the generated families -/

section FamApply

variable {A R P Q W K : Type} {dd : ℕ}
variable {ι : Type} [LinearOrder ι] [Finite ι]

/-- **A within-round chain preserving a control value preserves it end to
end.** -/
theorem chainSt_apply_of (q : Q) {nr : ℕ} (bit : Fin nr → Prop)
    (upd : Fin nr → Bool → (Q → A) → Q → A)
    (hupd : ∀ (i : Fin nr) (bb : Bool) (f : Q → A), upd i bb f q = f q)
    (base : Q → A) (n : ℕ) :
    chainSt bit upd base n q = base q := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < nr
    · by_cases hb : bit ⟨n, h⟩
      · rw [chainSt_succ_pos h hb, hupd, ih]
      · rw [chainSt_succ_neg h hb, hupd, ih]
    · have hskip : chainSt bit upd base (n + 1) = chainSt bit upd base n := by
        simp only [chainSt]
        rw [dif_neg h]
      rw [hskip, ih]

/-- **A control value the loop's operations never write survives the whole
generated element family.** -/
theorem elemFam_apply_of (q : Q) {nr : ℕ}
    {setFlag : Fin nr → Bool → (Q → A) → (W → A) → Q → A}
    {initEl advEl : (Q → A) → (W → A) → Q → A}
    {rest : (Univ A R P K dd → Prop) → W → A}
    {v : Univ A R P K dd → Prop}
    {m : Fin nr → Univ A R P K dd → Prop}
    (hSet : ∀ (k : Fin nr) (bb : Bool) (f : Q → A) (g : W → A),
      setFlag k bb f g q = f q)
    (hInit : ∀ (f : Q → A) (g : W → A), initEl f g q = f q)
    (hAdv : ∀ (f : Q → A) (g : W → A), advEl f g q = f q)
    (xOf : ι → Fin nr → Univ A R P K dd) (f₀ : Q → A) (a : ι)
    (j : Fin (nr + 1)) :
    elemFam setFlag initEl advEl rest v m xOf f₀ a j q = f₀ q := by
  classical
  have hchain : ∀ (a' : ι) (f : Q → A) (n : ℕ),
      chainSt (fun j' => m j' (xOf a' j'))
        (fun j' b q' => setFlag j' b q' (rest v)) f n q = f q :=
    fun a' f n => chainSt_apply_of q _ _ (fun i bb f' => hSet i bb f' _) f n
  have hiter : ∀ a' : ι,
      elemIter setFlag initEl advEl rest v m xOf f₀ a' q = f₀ q := by
    intro a'
    induction a' using order_induction with
    | hmin z hz =>
      rw [elemIter, iterOrd_bot hz, hInit]
    | hstep w z hwz hnb ih =>
      have hz2 := iterOrd_covers
        (init := initEl f₀ (rest v))
        (step := fun a' fq => advEl (chainSt (fun j' => m j' (xOf a' j'))
          (fun j' b q' => setFlag j' b q' (rest v)) fq nr) (rest v))
        hwz hnb
      rw [elemIter] at ih ⊢
      rw [hz2, hAdv, hchain]
      exact ih
  rw [elemFam, hchain]
  exact hiter a

/-- **A control value the copy loop's operations never write survives the
generated tuple family.** -/
theorem tupleIter1_apply_of (q : Q)
    {setBit : Bool → (Q → A) → (W → A) → Q → A}
    {initLv advLv : (Q → A) → (W → A) → Q → A}
    {mSrc : Univ A R P K dd → Prop}
    {v : Univ A R P K dd → Prop}
    {restF : (Univ A R P K dd → Prop) → (Univ A R P K dd → Prop) → W → A}
    (hSet : ∀ (bb : Bool) (f : Q → A) (g : W → A), setBit bb f g q = f q)
    (hInit : ∀ (f : Q → A) (g : W → A), initLv f g q = f q)
    (hAdv : ∀ (f : Q → A) (g : W → A), advLv f g q = f q)
    (xS xD : ι → Univ A R P K dd) (mD₀ : Univ A R P K dd → Prop)
    (f₀ : Q → A) (a : ι) :
    tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a q = f₀ q := by
  classical
  have hiter : ∀ a' : ι,
      tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a' q =
        f₀ q := by
    intro a'
    induction a' using order_induction with
    | hmin z hz =>
      rw [tupleIter0, iterOrd_bot hz, hInit]
    | hstep w z hwz hnb ih =>
      have hz2 := iterOrd_covers
        (init := initLv f₀ (restF mD₀ v))
        (step := fun a' fq =>
          advLv (if mSrc (xS a') then setBit true fq
              (restF (tupleIterD mSrc xS xD mD₀ a') v)
            else setBit false fq (restF (tupleIterD mSrc xS xD mD₀ a') v))
            (restF (tupleIterD mSrc xS xD mD₀ a') v))
        hwz hnb
      rw [tupleIter0] at ih ⊢
      rw [hz2, hAdv]
      by_cases hb : mSrc (xS w)
      · rw [if_pos hb, hSet]
        exact ih
      · rw [if_neg hb, hSet]
        exact ih
  rw [tupleIter1]
  by_cases hb : mSrc (xS a)
  · rw [if_pos hb, hSet]
    exact hiter a
  · rw [if_neg hb, hSet]
    exact hiter a

end FamApply

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}
variable [Nonempty A] [L.IsRelational] [L.Structure A]

section KindStage

variable (zero one : A)
variable (vi : dt.VarIx) (av : Fin dt.natMax)
variable (st : TapeSt dt A R P) (v : Univ A R P dt.KIx dt.dd → Prop)

/-- **The semantic data of one atom's run**: an expansion atom needs the
points its levels' registers encode; the other kinds need nothing. -/
noncomputable def KindSem : MatAtom dt.X dt.d (dt.nOf vi) → Type
  | .eq _ _ => PUnit
  | .ord _ _ => PUnit
  | .stage _ _ => PUnit
  | @MatAtom.exp _ _ _ _ k _ ts =>
    { pts : Fin k → dt.X.Map A //
      ∀ ℓ : Fin k,
        wmBlk (dt.lvSet st vi (ts ℓ))
          (PfpTag.arg (toLex (dt.lvBlk vi (ts ℓ))) : PfpTag R P dt.KIx) =
          encMap dt.ly zero one (pts ℓ) }

open Classical in
/-- **The control one atom's machinery leaves behind**, by kind: the fold's
exit at the comparison's or the expansion atom's family, the verdict store
at the stage atom's read bit. -/
noncomputable def kindExitCtl :
    ∀ κ : MatAtom dt.X dt.d (dt.nOf vi),
      dt.KindSem zero one vi st κ →
      dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim →
      dt.kindDepth κ ≤ dt.eDim → dt.kindReads κ ≤ dt.nfDim →
      (dt.CtlIx → A) → dt.CtlIx → A
  | .eq j₁ j₂, _, _, _, hrd, f =>
    (dt.cmpArgs zero one vi av hrd true j₁ j₂).exitSt
      (dt.cmpFam zero one vi av hrd true j₁ j₂ st v f (toLex topTup)
        (Fin.last 2))
      (dt.back zero one dt.dd0Le st v)
  | .ord j₁ j₂, _, _, _, hrd, f =>
    (dt.cmpArgs zero one vi av hrd false j₁ j₂).exitSt
      (dt.cmpFam zero one vi av hrd false j₁ j₂ st v f (toLex topTup)
        (Fin.last 2))
      (dt.back zero one dt.dd0Le st v)
  | .stage i ts, _, _, _, _, f =>
    (dt.stageArgs zero one vi i ts av).setAv
      (if st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i))
        then true else false)
      (dt.stageFAt zero one vi i ts av st v f (dt.d.B.arity i))
      (dt.back zero one dt.dd0Le
        (dt.stageAtSt st v
          (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i)))
        (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i)))
  | @MatAtom.exp _ _ _ _ k e ts, sem, hk, hn, hrd, f =>
    letI := Fintype.ofFinite dt.X.Tag
    (dt.expArgs zero one vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)).exitSt
      (fun ℓ => (sem.1 ℓ).1.1)
      (dt.expFam zero one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd) v
        (dt.expTagFam zero one vi ts e av st hk
          (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (dt.relPk e τ').n) (Finset.mem_univ τ)) hn)
          (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
          v f (Fin.last (k * Fintype.card dt.X.Tag)))
        (toLex topTup)
        (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1))))
      (dt.back zero one dt.dd0Le st v)

variable {dt zero one vi av st v}

section Run

variable [Finite dt.KIx]
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = v) (htgt : st.tgt = v)

/-- **The state an atom leaves**: a stage atom normalizes SAV and TARGET to
the home address (its random access writes them whatever they held), every
other kind leaves the state alone. -/
noncomputable def kindEndSt (dt : PfpData L) {A R P : Type}
    (vi : dt.VarIx) (v : Univ A R P dt.KIx dt.dd → Prop)
    (κ : MatAtom dt.X dt.d (dt.nOf vi)) (st : TapeSt dt A R P) :
    TapeSt dt A R P :=
  match κ with
  | .stage _ _ => dt.stageEndSt st v
  | _ => st

include hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt in
/-- **The uniform stage discharge, threaded**: as
`DescriptiveComplexity.Pfp.PfpData.kind_hStage` but with no boundary
discipline assumed — the atom's exit state is
`DescriptiveComplexity.Pfp.PfpData.kindEndSt`, which normalizes SAV and
TARGET exactly when the atom is a stage atom. -/
theorem kind_hStage_thread
    (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.KindSem PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.kindExitCtl PR.zero PR.one vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le (dt.kindEndSt vi v κ st))
          (dt.kindEndSt vi v κ st).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact dt.cmp_hStage vi av hrd true j₁ j₂ hrules hR hlin hbot hv hvi
      hwkSt f
  | ord j₁ j₂ =>
    exact dt.cmp_hStage vi av hrd false j₁ j₂ hrules hR hlin hbot hv hvi
      hwkSt f
  | stage i ts =>
    refine dt.stage_hStage_thread vi i ts av hrules hR hlin hord htop hbot
      hv hvi hwkSt hmirSt hbotSt _ ?_ f
    by_cases hbb : st.old i
      (dt.stageTgtD PR.zero vi i ts st v (dt.d.B.arity i))
    · rw [if_pos hbb]
      exact ⟨fun _ => rfl, fun _ => hbb⟩
    · rw [if_neg hbb]
      exact ⟨fun h => absurd h hbb, fun h => nomatch h⟩
  | @exp k e ts =>
    obtain ⟨pts, hENC⟩ := sem
    have hent : emb (dt.kindEntry (MatAtom.exp e ts)) = tagFirstRd emb := by
      by_cases h : 0 < k * Fintype.card dt.X.Tag
      · rw [show dt.kindEntry (MatAtom.exp e ts) =
            TagPh.tagRdP ⟨0, h⟩ ReadPh.start from by
            rw [kindEntry]; exact dif_pos h,
          show (tagFirstRd emb : P) =
            emb (TagPh.tagRdP ⟨0, h⟩ ReadPh.start) from dif_pos h]
      · rw [show dt.kindEntry (MatAtom.exp e ts) = TagPh.brP from by
            rw [kindEntry]; exact dif_neg h,
          show (tagFirstRd emb : P) = emb TagPh.brP from dif_neg h]
    rw [hent]
    exact dt.exp_hStage vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
      hrules hR hlin hbot hv hvi hwkSt pts hENC f

include hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt hsav htgt in
/-- **The uniform stage discharge**: whatever the kind, the atom's machinery
runs from its entry phase one cell right of the marker to the exit phase
back there, leaving `DescriptiveComplexity.Pfp.PfpData.kindExitCtl` in the
control and the tape untouched. -/
theorem kind_hStage
    (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (sem : dt.KindSem PR.zero PR.one vi st κ)
    {emb : dt.KindPh κ → P} {exitPh : P}
    {rEmb : ∀ s : dt.KindSite κ, dt.KindSh κ s → R}
    (hrules : ∀ (s : dt.KindSite κ) (ρ : dt.KindSh κ s),
      PR.rules (rEmb s ρ) = dt.kindRule PR.zero PR.one κ
        (dt.kindArgsOf PR.zero PR.one vi av κ hk hnd hrd) emb exitPh s ρ)
    (f : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (dt.kindEntry κ)) f), Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.kindExitCtl PR.zero PR.one vi av st v κ sem hk hnd hrd f)),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact dt.cmp_hStage vi av hrd true j₁ j₂ hrules hR hlin hbot hv hvi
      hwkSt f
  | ord j₁ j₂ =>
    exact dt.cmp_hStage vi av hrd false j₁ j₂ hrules hR hlin hbot hv hvi
      hwkSt f
  | stage i ts =>
    refine dt.stage_hStage vi i ts av hrules hR hlin hord htop hbot hv hvi
      hwkSt hmirSt hbotSt hsav htgt _ ?_ f
    by_cases hbb : st.old i
      (dt.stageTgtD PR.zero vi i ts st v (dt.d.B.arity i))
    · rw [if_pos hbb]
      exact ⟨fun _ => rfl, fun _ => hbb⟩
    · rw [if_neg hbb]
      exact ⟨fun h => absurd h hbb, fun h => nomatch h⟩
  | @exp k e ts =>
    obtain ⟨pts, hENC⟩ := sem
    have hent : emb (dt.kindEntry (MatAtom.exp e ts)) = tagFirstRd emb := by
      by_cases h : 0 < k * Fintype.card dt.X.Tag
      · rw [show dt.kindEntry (MatAtom.exp e ts) =
            TagPh.tagRdP ⟨0, h⟩ ReadPh.start from by
            rw [kindEntry]; exact dif_pos h,
          show (tagFirstRd emb : P) =
            emb (TagPh.tagRdP ⟨0, h⟩ ReadPh.start) from dif_pos h]
      · rw [show dt.kindEntry (MatAtom.exp e ts) = TagPh.brP from by
            rw [kindEntry]; exact dif_neg h,
          show (tagFirstRd emb : P) = emb TagPh.brP from dif_neg h]
    rw [hent]
    exact dt.exp_hStage vi ts e av hk
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
      (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
        (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
      hrules hR hlin hbot hv hvi hwkSt pts hENC f

end Run

/-! ### The matrix, assembled -/

variable (dt zero one vi st v) in
/-- **The control thread across the matrix's atoms**: each atom's machinery
entered through the dispatch's `enterSt`, its exit control the next
atom's input. -/
noncomputable def matFs
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (sem : ∀ a : Fin (dt.natOf vi),
      dt.KindSem zero one vi st (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.kindExitCtl zero one vi
        (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, h⟩) st v
        (dt.kindOf vi ⟨n, h⟩) (sem ⟨n, h⟩)
        (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, h⟩)
        (dt.kindDepth_le_eDim vi ⟨n, h⟩)
        (dt.kindReads_le_nfDim vi ⟨n, h⟩)
        (enterSt ⟨n, h⟩ (matFs enterSt sem f₀ n)
          (dt.back zero one dt.dd0Le st v))
    else matFs enterSt sem f₀ n

/-! ### The threaded states of the matrix -/

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- An atom's exit state keeps the marker, the mirror, the bottom mark and
the VAL register: only SAV and TARGET can move. -/
theorem kindEndSt_fields (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (st : TapeSt dt A R P) :
    (dt.kindEndSt vi v κ st).wk = st.wk ∧
      (dt.kindEndSt vi v κ st).mir = st.mir ∧
      (dt.kindEndSt vi v κ st).bot = st.bot ∧
      (dt.kindEndSt vi v κ st).val = st.val ∧
      (dt.kindEndSt vi v κ st).old = st.old := by
  cases κ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable (dt vi st v) in
/-- **The state after the matrix's first `n` atoms**: each stage atom
normalizes SAV and TARGET, the other kinds change nothing. -/
noncomputable def matSt : ℕ → TapeSt dt A R P
  | 0 => st
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.kindEndSt vi v (dt.kindOf vi ⟨n, h⟩) (matSt n)
    else matSt n

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The threaded states differ from the entry state in SAV and TARGET
alone** — so every hypothesis the atoms need at them is the entry state's.
-/
theorem matSt_fields (n : ℕ) :
    (dt.matSt vi st v n).wk = st.wk ∧ (dt.matSt vi st v n).mir = st.mir ∧
      (dt.matSt vi st v n).bot = st.bot ∧
      (dt.matSt vi st v n).val = st.val ∧
      (dt.matSt vi st v n).old = st.old := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [matSt]
    split
    · obtain ⟨h1, h2, h3, h4, h5⟩ :=
        dt.kindEndSt_fields (v := v) (dt.kindOf vi _) (dt.matSt vi st v n)
      exact ⟨h1.trans ih.1, h2.trans ih.2.1, h3.trans ih.2.2.1,
        h4.trans ih.2.2.2.1, h5.trans ih.2.2.2.2⟩
    · exact ih

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **A tape state is determined by its two scratch registers**, given the
other seven — the shape every threaded state of the machinery has against
the state it started from. -/
theorem tapeSt_eq_savTgt {X Y : TapeSt dt A R P} (hmir : X.mir = Y.mir)
    (hval : X.val = Y.val) (hold : X.old = Y.old) (hnew : X.new = Y.new)
    (hwk : X.wk = Y.wk) (hbot : X.bot = Y.bot) (hltp : X.ltp = Y.ltp) :
    X = { Y with sav := X.sav, tgt := X.tgt } := by
  obtain ⟨mir, tgt, sav, val, old, new, wk, bot, ltp⟩ := X
  obtain ⟨mir', tgt', sav', val', old', new', wk', bot', ltp'⟩ := Y
  simp only at hmir hval hold hnew hwk hbot hltp
  subst hmir; subst hval; subst hold; subst hnew; subst hwk; subst hbot
  subst hltp
  rfl

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The remaining registers an atom leaves alone** — the three
`DescriptiveComplexity.Pfp.PfpData.kindEndSt_fields` does not list, so
that the seven together pin the state down to its SAV and TARGET. -/
theorem kindEndSt_fields' (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (st : TapeSt dt A R P) :
    (dt.kindEndSt vi v κ st).new = st.new ∧
      (dt.kindEndSt vi v κ st).ltp = st.ltp := by
  cases κ <;> exact ⟨rfl, rfl⟩

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- The same two, along the matrix's whole chain of atoms. -/
theorem matSt_fields' (n : ℕ) :
    (dt.matSt vi st v n).new = st.new ∧ (dt.matSt vi st v n).ltp = st.ltp := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [matSt]
    split
    · obtain ⟨h1, h2⟩ :=
        dt.kindEndSt_fields' (v := v) (dt.kindOf vi _) (dt.matSt vi st v n)
      exact ⟨h1.trans ih.1, h2.trans ih.2⟩
    · exact ih

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational]
  [L.Structure A] in
/-- **The matrix's threaded state is its entry state with the two scratch
registers rewritten** — the sharpening of
`DescriptiveComplexity.Pfp.PfpData.matSt_fields` that lets the loop above
thread the two registers instead of the whole state, and with them keep
every semantic pack at the state it was built for. -/
theorem matSt_eq (n : ℕ) :
    dt.matSt vi st v n =
      { st with
        sav := (dt.matSt vi st v n).sav
        tgt := (dt.matSt vi st v n).tgt } :=
  dt.tapeSt_eq_savTgt (dt.matSt_fields (v := v) (st := st) n).2.1
    (dt.matSt_fields (v := v) (st := st) n).2.2.2.1
    (dt.matSt_fields (v := v) (st := st) n).2.2.2.2
    (dt.matSt_fields' (v := v) (st := st) n).1
    (dt.matSt_fields (v := v) (st := st) n).1
    (dt.matSt_fields (v := v) (st := st) n).2.2.1
    (dt.matSt_fields' (v := v) (st := st) n).2

section AvcRide

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **A foreign verdict slot survives one atom's machinery**: whatever the
kind, its exit control writes its own verdict slot and scratch, never
another atom's. -/
theorem kindExitCtl_apply_avC
    (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (sem : dt.KindSem zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) {a' : Fin dt.natMax}
    (hne : dt.avC a' ≠ dt.avC av) :
    dt.kindExitCtl zero one vi av st v κ sem hk hnd hrd f (dt.avC a') =
      f (dt.avC a') := by
  classical
  have hAcc : dt.avC a' ≠ dt.cmpAccC := fun h => nomatch h
  have hDec : dt.avC a' ≠ dt.cmpDecC := fun h => nomatch h
  have hVal : dt.avC a' ≠ dt.cmpValC := fun h => nomatch h
  have hSub : dt.avC a' ≠ dt.subLeafC := fun h => nomatch h
  have hBit : dt.avC a' ≠ dt.bitFlagC := fun h => nomatch h
  have hNotSac : ∀ j : Fin dt.eDim, dt.avC a' ≠ dt.sacC j :=
    fun j h => nomatch h
  have hcmpFold : ∀ (hnf : 2 ≤ dt.nfDim) (fc : dt.CtlIx → A),
      dt.cmpFold zero one hnf fc (dt.avC a') = fc (dt.avC a') := by
    intro hnf fc
    rw [cmpFold, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal]
  have hcmpFam : ∀ (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
      (j₁ j₂ : Fin (dt.nOf vi)) (fc : dt.CtlIx → A),
      dt.cmpFam zero one vi av hnf isEq j₁ j₂ st v fc (toLex topTup)
        (Fin.last 2) (dt.avC a') = fc (dt.avC a') := by
    intro hnf isEq j₁ j₂ fc
    rw [cmpFam]
    refine elemFam_apply_of (dt.avC a') ?_ ?_ ?_ _ _ _ _
    · intro k bb fd g
      change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) fd
        (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.cmpRdC hnf k from fun h => nomatch h) _ _
    · intro fd g
      change dt.cmpInit zero one (dt.initLvN fd) (dt.avC a') = _
      rw [cmpInit, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal,
        initLvN, putLv_av]
    · intro fd g
      change dt.advLvN (dt.cmpFold zero one hnf fd) (dt.avC a') = _
      rw [advLvN, putLv_av]
      exact hcmpFold hnf fd
  cases κ with
  | eq j₁ j₂ =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.cmpFold zero one hrd
        (dt.cmpFam zero one vi av hrd true j₁ j₂ st v f (toLex topTup)
          (Fin.last 2))) (dt.avC a') = _
    rw [setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd true j₁ j₂ f)
  | ord j₁ j₂ =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.cmpFold zero one hrd
        (dt.cmpFam zero one vi av hrd false j₁ j₂ st v f (toLex topTup)
          (Fin.last 2))) (dt.avC a') = _
    rw [setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd false j₁ j₂ f)
  | stage i ts =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.stageFAt zero one vi i ts av st v f (dt.d.B.arity i))
      (dt.avC a') = _
    rw [setCtl_of_ne hne]
    have hstage : ∀ n : ℕ,
        dt.stageFAt zero one vi i ts av st v f n (dt.avC a') =
          f (dt.avC a') := by
      intro n
      induction n with
      | zero =>
        change dt.initLvN f (dt.avC a') = _
        rw [initLvN, putLv_av]
      | succ n ih =>
        by_cases h : n < dt.d.B.arity i
        · have hstep : dt.stageFAt zero one vi i ts av st v f (n + 1) =
              tupleIter1 (dt.stageArgs zero one vi i ts av).setBit
                (dt.stageArgs zero one vi i ts av).initLv
                (dt.stageArgs zero one vi i ts av).advLv
                (dt.lvSet { st with sav := v } vi (ts ⟨n, h⟩)) v
                (dt.stageRestF zero one { st with sav := v })
                (dt.stageXS zero vi i ts ⟨n, h⟩) (dt.stageXD zero i ⟨n, h⟩)
                (dt.stageTgtD zero vi i ts st v n)
                (dt.stageFAt zero one vi i ts av st v f n)
                (toLex topTup) := by
            simp only [stageFAt]
            rw [dif_pos h]
          rw [hstep]
          refine (tupleIter1_apply_of (dt.avC a') ?_ ?_ ?_ _ _ _ _ _).trans ih
          · intro bb fd g
            change dt.setCtl zero one dt.bitFlagC (bb = true) fd
              (dt.avC a') = _
            exact setCtl_of_ne hBit _ _
          · intro fd g
            change dt.initLvN fd (dt.avC a') = _
            rw [initLvN, putLv_av]
          · intro fd g
            change dt.advLvN fd (dt.avC a') = _
            rw [advLvN, putLv_av]
        · have hstep : dt.stageFAt zero one vi i ts av st v f (n + 1) =
              dt.stageFAt zero one vi i ts av st v f n := by
            simp only [stageFAt]
            rw [dif_neg h]
          rw [hstep]
          exact ih
    exact hstage _
  | @exp k e ts =>
    change dt.setCtl zero one (dt.avC av) _
      (dt.setSubLeaf zero one _
        (dt.expFam zero one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk _ _ v
          (dt.expTagFam zero one vi ts e av st hk _ _ v f
            (Fin.last (k * Fintype.card dt.X.Tag)))
          (toLex topTup)
          (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))))
      (dt.avC a') = _
    rw [setCtl_of_ne hne, setSubLeaf, setCtl_of_ne hSub]
    refine Eq.trans (elemFam_apply_of (dt.avC a') ?_ ?_ ?_
      (dt.expECell zero one vi ts e (fun ℓ => (sem.1 ℓ).1.1)
        (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n)
          (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd))
      (dt.expTagFam zero one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))
      (toLex topTup)
      (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) ?_
    · intro r bb fd g
      change dt.setCtl zero one
        (dt.rdfC (Fin.castLE
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd) r))
        (bb = true) fd (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.rdfC _ from fun h => nomatch h) _ _
    · intro fd g
      change dt.expInit zero one e (fun ℓ => (sem.1 ℓ).1.1) fd (dt.avC a')
        = _
      rw [expInit, initSac, putSac_of_not_sac hNotSac, initLvE, putLvE_av]
    · intro fd g
      change dt.expAdv zero one e (fun ℓ => (sem.1 ℓ).1.1) _ _ fd
        (dt.avC a') = _
      rw [expAdv, advLvE, putLvE_av, carrySac, putSac_of_not_sac hNotSac,
        setSubLeaf, setCtl_of_ne hSub]
    · refine chainSt_apply_of (dt.avC a') _ _ ?_ f
        ((Fin.last (k * Fintype.card dt.X.Tag) :
          Fin (k * Fintype.card dt.X.Tag + 1)) : ℕ)
      intro i bb fd
      change dt.setCtl zero one
        (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (bb = true) fd
        (dt.avC a') = _
      exact setCtl_of_ne
        (show dt.avC a' ≠ dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 from
          fun h => nomatch h) _ _

omit [Fintype dt.SlotIx] [Finite A] [Finite R] [Finite P] [Nonempty A] in
/-- An expansion atom's exit at a foreign slot: the value rides through. -/
private theorem expExit_apply_of {k : ℕ} {e : dt.X.E.Relations k}
    {τ : Fin k → dt.X.Tag} {hn' : (dt.relPk e τ).n ≤ dt.eDim}
    {hrd' : dt.relNr e τ ≤ dt.nfDim} {a : Fin dt.natMax}
    {f' : dt.CtlIx → A} {q : dt.CtlIx}
    (hqa : q ≠ dt.avC a) (hqs : q ≠ dt.subLeafC) :
    dt.expExit zero one e τ hn' hrd' a f' q = f' q := by
  rw [expExit, setCtl_of_ne hqa, setSubLeaf, setCtl_of_ne hqs]

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An accumulator slot survives one atom's machinery**: no atom's exit
control ever writes the inner fold's vector. -/
theorem kindExitCtl_apply_accC
    (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (sem : dt.KindSem zero one vi st κ)
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) (jj : Fin dt.naDim) :
    dt.kindExitCtl zero one vi av st v κ sem hk hnd hrd f (dt.accC jj) =
      f (dt.accC jj) := by
  classical
  have hne : dt.accC jj ≠ dt.avC av := fun h => nomatch h
  have hAcc : dt.accC jj ≠ dt.cmpAccC := fun h => nomatch h
  have hDec : dt.accC jj ≠ dt.cmpDecC := fun h => nomatch h
  have hVal : dt.accC jj ≠ dt.cmpValC := fun h => nomatch h
  have hSub : dt.accC jj ≠ dt.subLeafC := fun h => nomatch h
  have hBit : dt.accC jj ≠ dt.bitFlagC := fun h => nomatch h
  have hNotSac : ∀ j : Fin dt.eDim, dt.accC jj ≠ dt.sacC j :=
    fun j h => nomatch h
  have hcmpFold : ∀ (hnf : 2 ≤ dt.nfDim) (fc : dt.CtlIx → A),
      dt.cmpFold zero one hnf fc (dt.accC jj) = fc (dt.accC jj) := by
    intro hnf fc
    rw [cmpFold, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal]
  have hcmpFam : ∀ (hnf : 2 ≤ dt.nfDim) (isEq : Bool)
      (j₁ j₂ : Fin (dt.nOf vi)) (fc : dt.CtlIx → A),
      dt.cmpFam zero one vi av hnf isEq j₁ j₂ st v fc (toLex topTup)
        (Fin.last 2) (dt.accC jj) = fc (dt.accC jj) := by
    intro hnf isEq j₁ j₂ fc
    rw [cmpFam]
    refine elemFam_apply_of (dt.accC jj) ?_ ?_ ?_ _ _ _ _
    · intro k bb fd g
      change dt.setCtl zero one (dt.cmpRdC hnf k) (bb = true) fd
        (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.cmpRdC hnf k from fun h => nomatch h) _ _
    · intro fd g
      change dt.cmpInit zero one (dt.initLvN fd) (dt.accC jj) = _
      rw [cmpInit, setCtl_of_ne hAcc, setCtl_of_ne hDec, setCtl_of_ne hVal,
        initLvN, putLv_acc]
    · intro fd g
      change dt.advLvN (dt.cmpFold zero one hnf fd) (dt.accC jj) = _
      rw [advLvN, putLv_acc]
      exact hcmpFold hnf fd
  cases κ with
  | eq j₁ j₂ =>
    have hK : dt.kindExitCtl zero one vi av st v (.eq j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one true (dt.cmpFold zero one hrd
            (dt.cmpFam zero one vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam zero one vi av hrd true j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd true j₁ j₂ f)
  | ord j₁ j₂ =>
    have hK : dt.kindExitCtl zero one vi av st v (.ord j₁ j₂) sem hk hnd hrd
        f =
        dt.setCtl zero one (dt.avC av)
          (dt.cmpVerdict one false (dt.cmpFold zero one hrd
            (dt.cmpFam zero one vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))))
          (dt.cmpFold zero one hrd
            (dt.cmpFam zero one vi av hrd false j₁ j₂ st v f (toLex topTup)
              (Fin.last 2))) := rfl
    rw [hK, setCtl_of_ne hne]
    exact (hcmpFold hrd _).trans (hcmpFam hrd false j₁ j₂ f)
  | stage i ts =>
    have hstage : ∀ n : ℕ,
        dt.stageFAt zero one vi i ts av st v f n (dt.accC jj) =
          f (dt.accC jj) := by
      intro n
      induction n with
      | zero =>
        change dt.initLvN f (dt.accC jj) = _
        rw [initLvN, putLv_acc]
      | succ n ih =>
        by_cases h : n < dt.d.B.arity i
        · have hstep : dt.stageFAt zero one vi i ts av st v f (n + 1) =
              tupleIter1 (dt.stageArgs zero one vi i ts av).setBit
                (dt.stageArgs zero one vi i ts av).initLv
                (dt.stageArgs zero one vi i ts av).advLv
                (dt.lvSet { st with sav := v } vi (ts ⟨n, h⟩)) v
                (dt.stageRestF zero one { st with sav := v })
                (dt.stageXS zero vi i ts ⟨n, h⟩) (dt.stageXD zero i ⟨n, h⟩)
                (dt.stageTgtD zero vi i ts st v n)
                (dt.stageFAt zero one vi i ts av st v f n)
                (toLex topTup) := by
            simp only [stageFAt]
            rw [dif_pos h]
          rw [hstep]
          refine (tupleIter1_apply_of (dt.accC jj) ?_ ?_ ?_ _ _ _ _ _).trans ih
          · intro bb fd g
            change dt.setCtl zero one dt.bitFlagC (bb = true) fd
              (dt.accC jj) = _
            exact setCtl_of_ne hBit _ _
          · intro fd g
            change dt.initLvN fd (dt.accC jj) = _
            rw [initLvN, putLv_acc]
          · intro fd g
            change dt.advLvN fd (dt.accC jj) = _
            rw [advLvN, putLv_acc]
        · have hstep : dt.stageFAt zero one vi i ts av st v f (n + 1) =
              dt.stageFAt zero one vi i ts av st v f n := by
            simp only [stageFAt]
            rw [dif_neg h]
          rw [hstep]
          exact ih
    have hK : dt.kindExitCtl zero one vi av st v (.stage i ts) sem hk hnd
        hrd f =
        dt.setCtl zero one (dt.avC av)
          ((if st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i))
            then true else false) = true)
          (dt.stageFAt zero one vi i ts av st v f (dt.d.B.arity i)) := rfl
    rw [hK, setCtl_of_ne hne]
    exact hstage _
  | @exp k e ts =>
    have hK : dt.kindExitCtl zero one vi av st v (.exp e ts) sem hk hnd hrd
        f =
        dt.expExit zero one e (fun ℓ => (sem.1 ℓ).1.1)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (dt.relPk e τ').n)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd)
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd)
          av
          (dt.expFam zero one vi ts e av st (fun ℓ => (sem.1 ℓ).1.1) hk
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
              (Finset.mem_univ τ')) hnd)
            (fun τ' => le_trans (Finset.le_sup
              (f := fun τ'' : Fin k → dt.X.Tag =>
                (blkAtoms (dt.relPk e τ'').mat).length)
              (Finset.mem_univ τ')) hrd) v
            (dt.expTagFam zero one vi ts e av st hk
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag => (dt.relPk e τ'').n)
                (Finset.mem_univ τ')) hnd)
              (fun τ' => le_trans (Finset.le_sup
                (f := fun τ'' : Fin k → dt.X.Tag =>
                  (blkAtoms (dt.relPk e τ'').mat).length)
                (Finset.mem_univ τ')) hrd)
              v f (Fin.last (k * Fintype.card dt.X.Tag)))
            (toLex topTup)
            (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) := rfl
    rw [hK, expExit_apply_of hne hSub]
    refine Eq.trans (elemFam_apply_of (dt.accC jj) ?_ ?_ ?_
      (dt.expECell zero one vi ts e (fun ℓ => (sem.1 ℓ).1.1)
        (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n)
          (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hnd))
      (dt.expTagFam zero one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (dt.relPk e τ').n) (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length) (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))
      (toLex topTup)
      (Fin.last (dt.relNr e (fun ℓ => (sem.1 ℓ).1.1)))) ?_
    · intro r bb fd g
      change dt.setCtl zero one
        (dt.rdfC (Fin.castLE
          (le_trans (Finset.le_sup (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
            (Finset.mem_univ (fun ℓ => (sem.1 ℓ).1.1))) hrd) r))
        (bb = true) fd (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.rdfC _ from fun h => nomatch h) _ _
    · intro fd g
      change dt.expInit zero one e (fun ℓ => (sem.1 ℓ).1.1) fd (dt.accC jj)
        = _
      rw [expInit, initSac, putSac_of_not_sac hNotSac, initLvE, putLvE_acc]
    · intro fd g
      change dt.expAdv zero one e (fun ℓ => (sem.1 ℓ).1.1) _ _ fd
        (dt.accC jj) = _
      rw [expAdv, advLvE, putLvE_acc, carrySac, putSac_of_not_sac hNotSac,
        setSubLeaf, setCtl_of_ne hSub]
    · refine chainSt_apply_of (dt.accC jj) _ _ ?_ f
        ((Fin.last (k * Fintype.card dt.X.Tag) :
          Fin (k * Fintype.card dt.X.Tag + 1)) : ℕ)
      intro i bb fd
      change dt.setCtl zero one
        (dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2) (bb = true) fd
        (dt.accC jj) = _
      exact setCtl_of_ne
        (show dt.accC jj ≠ dt.tagIx hk (dt.wIx i).1 (dt.wIx i).2 from
          fun h => nomatch h) _ _

omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **The inner fold's vector survives the whole matrix**: no atom writes
it, so the thread's accumulators after all atoms are the entry's. -/
theorem matFs_apply_accC
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAcc : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (jj : Fin dt.naDim),
      enterSt b f g (dt.accC jj) = f (dt.accC jj))
    (sem : ∀ b : Fin (dt.natOf vi),
      dt.KindSem zero one vi st (dt.kindOf vi b))
    (f₀ : dt.CtlIx → A) (jj : Fin dt.naDim) (n : ℕ) :
    dt.matFs zero one vi st v enterSt sem f₀ n (dt.accC jj) =
      f₀ (dt.accC jj) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < dt.natOf vi
    · have hFa : dt.matFs zero one vi st v enterSt sem f₀ (n + 1) =
          dt.kindExitCtl zero one vi
            (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) st v
            (dt.kindOf vi ⟨n, hn⟩) (sem ⟨n, hn⟩)
            (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, hn⟩)
            (dt.kindDepth_le_eDim vi ⟨n, hn⟩)
            (dt.kindReads_le_nfDim vi ⟨n, hn⟩)
            (enterSt ⟨n, hn⟩
              (dt.matFs zero one vi st v enterSt sem f₀ n)
              (dt.back zero one dt.dd0Le st v)) := by
        simp only [matFs]
        rw [dif_pos hn]
      rw [hFa, kindExitCtl_apply_accC _ _ _ _ _ _ jj, hEnterAcc]
      exact ih
    · have hFa : dt.matFs zero one vi st v enterSt sem f₀ (n + 1) =
          dt.matFs zero one vi st v enterSt sem f₀ n := by
        simp only [matFs]
        rw [dif_neg hn]
      rw [hFa]
      exact ih


omit [Fintype dt.SlotIx] [Finite R] [Finite P] in
/-- **An atom's verdict bit survives the rest of the matrix**: the thread's
value at atom `a`'s slot after all atoms is what atom `a`'s own machinery
wrote. -/
theorem matFs_apply_avC
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAv : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (a' : Fin dt.natMax),
      enterSt b f g (dt.avC a') = f (dt.avC a'))
    (sem : ∀ b : Fin (dt.natOf vi),
      dt.KindSem zero one vi st (dt.kindOf vi b))
    (f₀ : dt.CtlIx → A) (a : Fin (dt.natOf vi)) :
    dt.matFs zero one vi st v enterSt sem f₀ (dt.natOf vi)
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) =
      dt.kindExitCtl zero one vi
        (Fin.castLE (dt.natOf_le_natMax vi) a) st v
        (dt.kindOf vi a) (sem a)
        (dt.kindArgs_mul_card_le_ntgDim vi a)
        (dt.kindDepth_le_eDim vi a)
        (dt.kindReads_le_nfDim vi a)
        (enterSt a (dt.matFs zero one vi st v enterSt sem f₀ (a : ℕ))
          (dt.back zero one dt.dd0Le st v))
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) := by
  classical
  suffices h : ∀ n : ℕ, (a : ℕ) + 1 ≤ n → n ≤ dt.natOf vi →
      dt.matFs zero one vi st v enterSt sem f₀ n
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) =
      dt.matFs zero one vi st v enterSt sem f₀ ((a : ℕ) + 1)
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) by
    rw [h (dt.natOf vi) a.isLt le_rfl]
    simp only [matFs]
    rw [dif_pos a.isLt]
  intro n h1 h2
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hstep : (a : ℕ) + 1 ≤ n
    · have hn : n < dt.natOf vi := by omega
      have hne : dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a) ≠
          dt.avC (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) := by
        intro h
        have hcast : Fin.castLE (dt.natOf_le_natMax vi) a =
            Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩ := by
          injection h
        have hval := congrArg Fin.val hcast
        simp only [Fin.val_castLE] at hval
        omega
      have hFa : dt.matFs zero one vi st v enterSt sem f₀ (n + 1) =
          dt.kindExitCtl zero one vi
            (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, hn⟩) st v
            (dt.kindOf vi ⟨n, hn⟩) (sem ⟨n, hn⟩)
            (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, hn⟩)
            (dt.kindDepth_le_eDim vi ⟨n, hn⟩)
            (dt.kindReads_le_nfDim vi ⟨n, hn⟩)
            (enterSt ⟨n, hn⟩
              (dt.matFs zero one vi st v enterSt sem f₀ n)
              (dt.back zero one dt.dd0Le st v)) := by
        simp only [matFs]
        rw [dif_pos hn]
      rw [hFa, kindExitCtl_apply_avC _ _ _ _ _ _ hne, hEnterAv]
      exact ih hstep (by omega)
    · have hn : n = (a : ℕ) := by omega
      subst hn
      rfl

end AvcRide

section PointVerdict

variable (dt zero one vi st) in
/-- **The semantic data of every atom, from one encoded valuation**: the
expansion atoms' points are the valuation's, everything else needs
nothing. -/
noncomputable def mkKindSem (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (dt.lvSet st vi j)
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (w j)) :
    ∀ κ : MatAtom dt.X dt.d (dt.nOf vi), dt.KindSem zero one vi st κ
  | .eq _ _ => PUnit.unit
  | .ord _ _ => PUnit.unit
  | .stage _ _ => PUnit.unit
  | @MatAtom.exp _ _ _ _ _ _ ts => ⟨fun ℓ => w (ts ℓ), fun ℓ => hENC (ts ℓ)⟩

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **One round's agreement is the padded bits'**: given the two registers
hold encodings, the machine's per-tuple question is the encodings'. -/
theorem cmpAgr_iff_padBits {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (dt.lvSet st vi j₁)
      (PfpTag.arg (toLex (dt.lvBlk vi j₁)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (dt.lvSet st vi j₂)
      (PfpTag.arg (toLex (dt.lvBlk vi j₂)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one q)
    (u : Lex (Fin dt.dd0 → A)) :
    dt.CmpAgr zero vi j₁ j₂ st u ↔
      (dt.padBits zero (encMap dt.ly zero one p) (ofLex u) ↔
        dt.padBits zero (encMap dt.ly zero one q) (ofLex u)) :=
  iff_congr (iff_of_eq (congrFun h1 (pad zero (ofLex u))))
    (iff_of_eq (congrFun h2 (pad zero (ofLex u))))

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **The equality atom's verdict is point equality**: agreement at every
tuple decides the two encoded points. -/
theorem cmpAgr_all_iff (hzo : zero ≠ one)
    {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (dt.lvSet st vi j₁)
      (PfpTag.arg (toLex (dt.lvBlk vi j₁)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (dt.lvSet st vi j₂)
      (PfpTag.arg (toLex (dt.lvBlk vi j₂)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one q) :
    (∀ u : Lex (Fin dt.dd0 → A), dt.CmpAgr zero vi j₁ j₂ st u) ↔ p = q := by
  rw [dt.encMap_eq_iff_padBits (zero := zero) (one := one) hzo]
  exact ⟨fun h w' => (dt.cmpAgr_iff_padBits h1 h2 (toLex w')).mp (h _),
    fun h u => (dt.cmpAgr_iff_padBits h1 h2 u).mpr (h _)⟩

omit [Fintype dt.SlotIx] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]
  [Finite R] [Finite P] [Nonempty A] [L.IsRelational] in
/-- **The order atom's verdict is the chosen order**: agreement everywhere,
or a first difference with the second block holding the cell, is exactly
the binary order of the two encodings – the order the reduction puts on the
points. -/
theorem cmp_ord_iff (hzo : zero ≠ one)
    {j₁ j₂ : Fin (dt.nOf vi)} {p q : dt.X.Map A}
    (h1 : wmBlk (dt.lvSet st vi j₁)
      (PfpTag.arg (toLex (dt.lvBlk vi j₁)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one p)
    (h2 : wmBlk (dt.lvSet st vi j₂)
      (PfpTag.arg (toLex (dt.lvBlk vi j₂)) : PfpTag R P dt.KIx) =
      encMap dt.ly zero one q) :
    ((∀ u : Lex (Fin dt.dd0 → A), dt.CmpAgr zero vi j₁ j₂ st u) ∨
      ∃ u : Lex (Fin dt.dd0 → A), dt.CmpFst zero vi j₁ j₂ st u) ↔
      (encOrder dt.ly zero one hzo).le p q := by
  rw [dt.encOrder_le_iff_padBits hzo]
  refine or_congr
    ⟨fun h w' => (dt.cmpAgr_iff_padBits h1 h2 (toLex w')).mp (h _),
      fun h u => (dt.cmpAgr_iff_padBits h1 h2 u).mpr (h _)⟩ ?_
  constructor
  · rintro ⟨u, ⟨hne, hlt⟩, hall⟩
    refine ⟨ofLex u, fun w' hw' => ?_, ?_, ?_⟩
    · have hlex : toLex w' < u := lex_lt_iff.mpr hw'
      exact (dt.cmpAgr_iff_padBits h1 h2 (toLex w')).mp (hall _ hlex)
    · exact fun hc => hne ((iff_of_eq
        (congrFun h1 (pad zero (ofLex u)))).mpr hc)
    · exact (iff_of_eq (congrFun h2 (pad zero (ofLex u)))).mp hlt
  · rintro ⟨w', hall, hnp, hq⟩
    refine ⟨toLex w', ⟨?_, ?_⟩, fun u' hu' => ?_⟩
    · exact fun hc => hnp ((iff_of_eq
        (congrFun h1 (pad zero w'))).mp hc)
    · exact (iff_of_eq (congrFun h2 (pad zero w'))).mpr hq
    · exact (dt.cmpAgr_iff_padBits h1 h2 u').mpr
        (hall (ofLex u') (lex_lt_iff.mp hu'))

section SelfRead

variable [LinearOrder (dt.X.Map A)]

set_option maxHeartbeats 1000000 in
-- the `exp` branch's defeq, the kind dispatch against the pack, is deep
omit [Fintype dt.SlotIx] in
/-- **One atom's own verdict bit is its truth**: whatever the kind, the bit
the exit control writes in the atom's slot is `MatAtom.holds` at the
encoded valuation. -/
theorem ctlBit_kindExitCtl_self (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (dt.lvSet st vi j)
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (w j))
    (hOld : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i)) ↔
        σ i fun q => w (ts q))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (κ : MatAtom dt.X dt.d (dt.nOf vi))
    (hk : dt.kindArgs κ * Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnd : dt.kindDepth κ ≤ dt.eDim) (hrd : dt.kindReads κ ≤ dt.nfDim)
    (f : dt.CtlIx → A) :
    dt.ctlBit one
        (dt.kindExitCtl zero one vi av st v κ
          (dt.mkKindSem zero one vi st w hENC κ) hk hnd hrd f)
        (dt.avC av) ↔
      κ.holds σ w := by
  classical
  cases κ with
  | eq j₁ j₂ =>
    exact (dt.ctlBit_avC_cmp_exit hrd hzo f _).trans
      (dt.cmpAgr_all_iff hzo (hENC j₁) (hENC j₂))
  | ord j₁ j₂ =>
    refine (dt.ctlBit_avC_cmp_exit hrd hzo f _).trans ?_
    exact (cmp_ord_iff (dt := dt) hzo (hENC j₁) (hENC j₂)).trans
      (hordP (w j₁) (w j₂)).symm
  | stage i ts =>
    change dt.ctlBit one (dt.setCtl zero one (dt.avC av)
      ((if st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i))
        then true else false) = true)
      (dt.stageFAt zero one vi i ts av st v f (dt.d.B.arity i)))
      (dt.avC av) ↔ _
    rw [ctlBit_setCtl_self hzo]
    refine Iff.trans ?_ (hOld i ts)
    by_cases hb : st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i))
    · rw [if_pos hb]
      exact ⟨fun _ => hb, fun _ => rfl⟩
    · rw [if_neg hb]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h hb⟩
  | @exp k e ts =>
    simp only [mkKindSem, kindExitCtl, MatAtom.holds]
    exact dt.ctlBit_avC_exp_relMap (vi := vi) (ts := ts) (e := e)
      (av := av) (st := st) (hk := hk)
      (hn := fun τ => le_trans (Finset.le_sup
        (f := fun τ' : Fin k → dt.X.Tag => (dt.relPk e τ').n)
        (Finset.mem_univ τ)) hnd)
      (hrd := fun τ => le_trans (Finset.le_sup
        (f := fun τ' : Fin k → dt.X.Tag =>
          (blkAtoms (dt.relPk e τ').mat).length)
        (Finset.mem_univ τ)) hrd)
      (vAdr := v) hzo hlin (fun ℓ => w (ts ℓ))
      (fun ℓ => hENC (ts ℓ))
      (dt.expTagFam zero one vi ts e av st hk
        (fun τ => le_trans (Finset.le_sup
          (f := fun τ' : Fin k → dt.X.Tag => (dt.relPk e τ').n)
          (Finset.mem_univ τ)) hnd)
        (fun τ => le_trans (Finset.le_sup
          (f := fun τ' : Fin k → dt.X.Tag =>
            (blkAtoms (dt.relPk e τ').mat).length)
          (Finset.mem_univ τ)) hrd)
        v f (Fin.last (k * Fintype.card dt.X.Tag)))

omit [Fintype dt.SlotIx] in
/-- **The matrix's verdicts, at the points**: after the whole matrix, atom
`a`'s slot holds `MatAtom.holds` of its kind at the encoded valuation –
the `hav` input of `DescriptiveComplexity.Pfp.PfpData.postLeaf_iff_qfValue`
on the nose. -/
theorem ctlBit_avC_matFs_holds (hzo : zero ≠ one)
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (w : Fin (dt.nOf vi) → dt.X.Map A)
    (hENC : ∀ j : Fin (dt.nOf vi),
      wmBlk (dt.lvSet st vi j)
        (PfpTag.arg (toLex (dt.lvBlk vi j)) : PfpTag R P dt.KIx) =
        encMap dt.ly zero one (w j))
    (hOld : ∀ (i : dt.d.B.ι) (ts : Fin (dt.d.B.arity i) → Fin (dt.nOf vi)),
      st.old i (dt.stageTgtD zero vi i ts st v (dt.d.B.arity i)) ↔
        σ i fun q => w (ts q))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (hEnterAv : ∀ (b : Fin (dt.natOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A) (a' : Fin dt.natMax),
      enterSt b f g (dt.avC a') = f (dt.avC a'))
    (f₀ : dt.CtlIx → A) (a : Fin (dt.natOf vi)) :
    dt.ctlBit one
        (dt.matFs zero one vi st v enterSt
          (fun b => dt.mkKindSem zero one vi st w hENC (dt.kindOf vi b))
          f₀ (dt.natOf vi))
        (dt.avC (Fin.castLE (dt.natOf_le_natMax vi) a)) ↔
      (dt.kindOf vi a).holds σ w := by
  rw [ctlBit, matFs_apply_avC enterSt hEnterAv
    (fun b => dt.mkKindSem zero one vi st w hENC (dt.kindOf vi b)) f₀ a]
  exact dt.ctlBit_kindExitCtl_self hzo hlin σ w hENC hOld hordP
    (dt.kindOf vi a)
    (dt.kindArgs_mul_card_le_ntgDim vi a)
    (dt.kindDepth_le_eDim vi a)
    (dt.kindReads_le_nfDim vi a)
    (enterSt a (dt.matFs zero one vi st v enterSt
      (fun b => dt.mkKindSem zero one vi st w hENC (dt.kindOf vi b))
      f₀ (a : ℕ))
      (dt.back zero one dt.dd0Le st v))

end SelfRead

end PointVerdict

section MatrixRun

variable [Finite dt.KIx]
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v) (hmirSt : st.mir = v)
variable (hbotSt : st.bot = fun r => r = (fun _ => False))
variable (hsav : st.sav = v) (htgt : st.tgt = v)
variable {emb : dt.MatrixPh vi → P} {exitPh : P}
variable {rEmb : ∀ i : dt.MatrixSite vi, dt.MatrixSh vi i → R}
variable (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
  dt.CtlIx → A)
variable (hrules : ∀ (i : dt.MatrixSite vi) (ρ : dt.MatrixSh vi i),
  PR.rules (rEmb i ρ) = dt.matrixRule PR.zero PR.one vi emb
    (fun a => dt.atomArgs PR.zero PR.one vi a) enterSt exitPh i ρ)
variable (sem : ∀ a : Fin (dt.natOf vi),
  dt.KindSem PR.zero PR.one vi st (dt.kindOf vi a))

variable (dt zero one vi st v) in
/-- **The control thread across the matrix's atoms, threaded**: as
`DescriptiveComplexity.Pfp.PfpData.matFs`, with each atom's exit control
computed at the state that atom actually runs at. -/
noncomputable def matFsT
    (enterSt : Fin (dt.natOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (sem : ∀ a : Fin (dt.natOf vi),
      dt.KindSem zero one vi (dt.matSt vi st v (a : ℕ)) (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.natOf vi then
      dt.kindExitCtl zero one vi
        (Fin.castLE (dt.natOf_le_natMax vi) ⟨n, h⟩)
        (dt.matSt vi st v n) v
        (dt.kindOf vi ⟨n, h⟩) (sem ⟨n, h⟩)
        (dt.kindArgs_mul_card_le_ntgDim vi ⟨n, h⟩)
        (dt.kindDepth_le_eDim vi ⟨n, h⟩)
        (dt.kindReads_le_nfDim vi ⟨n, h⟩)
        (enterSt ⟨n, h⟩ (matFsT enterSt sem f₀ n)
          (dt.back zero one dt.dd0Le (dt.matSt vi st v n) v))
    else matFsT enterSt sem f₀ n

include hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt hrules in
/-- **The matrix's run, threaded**: as
`DescriptiveComplexity.Pfp.PfpData.matrix_run` with no boundary discipline
assumed — the tape ends in the threaded state
`DescriptiveComplexity.Pfp.PfpData.matSt`, which differs from the entry
state in SAV and TARGET alone, and only if the matrix has a stage atom. -/
theorem matrix_run_thread
    (semT : ∀ a : Fin (dt.natOf vi),
      dt.KindSem PR.zero PR.one vi (dt.matSt vi st v (a : ℕ))
        (dt.kindOf vi a))
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.matFsT PR.zero PR.one vi st v enterSt semT f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le
            (dt.matSt vi st v (dt.natOf vi)))
          (dt.matSt vi st v (dt.natOf vi)).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ (n : ℕ) r,
      dt.back PR.zero PR.one dt.dd0Le (dt.matSt vi st v n) r Slot.wk =
        bitVal PR.zero PR.one (r = v) := by
    intro n r
    rw [back_wk, (dt.matSt_fields (v := v) (st := st) n).1, hwkSt]
  have hchain := seq_run hrules hR hlin hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun k => dt.back PR.zero PR.one dt.dd0Le
      (dt.matSt vi st v (k : ℕ)))
    (mOf := fun k => (dt.matSt vi st v (k : ℕ)).val)
    (fun k r => hwkOf (k : ℕ) r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.matFsT PR.zero PR.one vi st v enterSt semT f₀ (j : ℕ))
    ?_
  · exact hchain
  · intro a
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.matFsT PR.zero PR.one vi st v enterSt semT f₀
          ((a : ℕ) + 1) =
        dt.kindExitCtl PR.zero PR.one vi
          (Fin.castLE (dt.natOf_le_natMax vi) a)
          (dt.matSt vi st v (a : ℕ)) v
          (dt.kindOf vi a) (semT a)
          (dt.kindArgs_mul_card_le_ntgDim vi a)
          (dt.kindDepth_le_eDim vi a)
          (dt.kindReads_le_nfDim vi a)
          (enterSt a (dt.matFsT PR.zero PR.one vi st v enterSt semT f₀
              (a : ℕ))
            (dt.back PR.zero PR.one dt.dd0Le (dt.matSt vi st v (a : ℕ)) v)) := by
      simp only [matFsT]
      rw [dif_pos a.isLt]
    have hSt : dt.matSt vi st v ((a : ℕ) + 1) =
        dt.kindEndSt vi v (dt.kindOf vi a) (dt.matSt vi st v (a : ℕ)) := by
      simp only [matSt]
      rw [dif_pos a.isLt]
    rw [hFa, hSt]
    obtain ⟨hw, hm, hb, -, -⟩ := dt.matSt_fields (v := v) (st := st) (a : ℕ)
    exact dt.kind_hStage_thread hR hlin hord htop hbot hv hvi
      (hw.trans hwkSt) (hm.trans hmirSt) (hb.trans hbotSt)
      (dt.kindOf vi a)
      (dt.kindArgs_mul_card_le_ntgDim vi a)
      (dt.kindDepth_le_eDim vi a)
      (dt.kindReads_le_nfDim vi a) (semT a)
      (fun s ρ => hrules (.sub a s) ρ)
      (enterSt a (dt.matFsT PR.zero PR.one vi st v enterSt semT f₀ (a : ℕ))
        (dt.back PR.zero PR.one dt.dd0Le (dt.matSt vi st v (a : ℕ)) v))

include hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt hsav htgt hrules in
/-- **The matrix's run**: from the checkpoint before the first atom at the
marker to the exit phase one cell to its right after the last, the verdict
slots holding each atom's fold, the tape untouched. -/
theorem matrix_run (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.matFs PR.zero PR.one vi st v enterSt sem f₀ (dt.natOf vi))),
        Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.back PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hchain := seq_run hrules hR hlin hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.back PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.matFs PR.zero PR.one vi st v enterSt sem f₀ (j : ℕ))
    ?_
  · exact hchain
  · intro a
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.matFs PR.zero PR.one vi st v enterSt sem f₀ ((a : ℕ) + 1) =
        dt.kindExitCtl PR.zero PR.one vi
          (Fin.castLE (dt.natOf_le_natMax vi) a) st v
          (dt.kindOf vi a) (sem a)
          (dt.kindArgs_mul_card_le_ntgDim vi a)
          (dt.kindDepth_le_eDim vi a)
          (dt.kindReads_le_nfDim vi a)
          (enterSt a (dt.matFs PR.zero PR.one vi st v enterSt sem f₀ (a : ℕ))
            (dt.back PR.zero PR.one dt.dd0Le st v)) := by
      simp only [matFs]
      rw [dif_pos a.isLt]
    rw [hFa]
    exact dt.kind_hStage hR hlin hord htop hbot hv hvi hwkSt hmirSt hbotSt
      hsav htgt (dt.kindOf vi a)
      (dt.kindArgs_mul_card_le_ntgDim vi a)
      (dt.kindDepth_le_eDim vi a)
      (dt.kindReads_le_nfDim vi a) (sem a)
      (fun s ρ => hrules (.sub a s) ρ)
      (enterSt a (dt.matFs PR.zero PR.one vi st v enterSt sem f₀ (a : ℕ))
        (dt.back PR.zero PR.one dt.dd0Le st v))

end MatrixRun

/-! ### The gates, assembled -/

section GatesRun

variable (dt zero one vi st v) in
/-- **The control thread across the gates' blocks** (the all-pass path):
each block's machinery entered through the dispatch's `enterSt`, its
conjoining exit the next block's input. -/
noncomputable def gatesFs
    (bOf : Fin (dt.arOf vi) → Fin dt.ko ⊕ Fin dt.ki)
    (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
    (hnG : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
    (hrdG : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
    (tOf : Fin (dt.arOf vi) → dt.X.Tag)
    (enterSt : Fin (dt.arOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
      dt.CtlIx → A)
    (f₀ : dt.CtlIx → A) : ℕ → dt.CtlIx → A
  | 0 => f₀
  | n + 1 =>
    if h : n < dt.arOf vi then
      (dt.gateArgs zero one (bOf ⟨n, h⟩) hc hnG hrdG).exitSt (tOf ⟨n, h⟩)
        (dt.gateFam zero one (bOf ⟨n, h⟩) st (tOf ⟨n, h⟩) hc hnG hrdG v
          (dt.gateTagFam zero one (bOf ⟨n, h⟩) st hc hnG hrdG v
            (enterSt ⟨n, h⟩ (gatesFs bOf hc hnG hrdG tOf enterSt f₀ n)
              (dt.back zero one dt.dd0Le st v))
            (Fin.last (Fintype.card dt.X.Tag)))
          (toLex topTup) (Fin.last (dt.domNr (tOf ⟨n, h⟩))))
        (dt.back zero one dt.dd0Le st v)
    else gatesFs bOf hc hnG hrdG tOf enterSt f₀ n

variable [Finite dt.KIx]
variable (bOf : Fin (dt.arOf vi) → Fin dt.ko ⊕ Fin dt.ki)
variable (hc : Fintype.card dt.X.Tag ≤ dt.ntgDim)
variable (hnG : ∀ t' : dt.X.Tag, (dt.domPk t').n ≤ dt.eDim)
variable (hrdG : ∀ t' : dt.X.Tag, dt.domNr t' ≤ dt.nfDim)
variable (wellGOf : Fin (dt.arOf vi) → (dt.SlotIx → A) → Prop)
variable (setFail : (dt.CtlIx → A) → (dt.SlotIx → A) → dt.CtlIx → A)
variable {emb : dt.GatesPh vi → P} {failPh exitPh : P}
variable {rEmb : ∀ i : dt.GatesSite vi, dt.GatesSh vi i → R}
variable (enterSt : Fin (dt.arOf vi) → (dt.CtlIx → A) → (dt.SlotIx → A) →
  dt.CtlIx → A)
variable (hrules : ∀ (i : dt.GatesSite vi) (ρ : dt.GatesSh vi i),
  PR.rules (rEmb i ρ) = dt.gatesRule (one := PR.one) (v := vi) (emb := emb)
    (argsG := fun ℓ => dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
    (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
    (failPh := failPh) (exitPh := exitPh) i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
variable {gtop gbot : Univ A R P dt.KIx dt.dd}
variable (htop : ∀ y, WMLe y gtop) (hbot : ∀ y, WMLe gbot y)
variable {v' : Univ A R P dt.KIx dt.dd → Prop}
variable (hv : WMSetLt WMLe v (wmSeg gbot)) (hvi : WMIncr WMLe v v')
variable (hwkSt : st.wk = fun r => r = v)
variable (TestOf : Fin (dt.arOf vi) → Univ A R P dt.KIx dt.dd → Prop)
variable (hcompatOf : ∀ (ℓ : Fin (dt.arOf vi)) (u : Univ A R P dt.KIx dt.dd),
  wellGOf ℓ (PR.passTracks Slot.mir (dt.back PR.zero PR.one dt.dd0Le st)
    st.mir (wmSeg u)) ↔ TestOf ℓ u)
variable (tOf : Fin (dt.arOf vi) → dt.X.Tag)
variable (htagOf : ∀ ℓ : Fin (dt.arOf vi),
  dt.dspTagOf PR.zero PR.one
    (wmBlk st.mir (PfpTag.arg (toLex (bOf ℓ)) : PfpTag R P dt.KIx)) =
  tOf ℓ)

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The gates' run at a gated address**: every block passes its shape
test, every domain evaluation runs on its block's decoded tag, and the
sequence exits with the conjoined verdict in the flag. -/
theorem gates_run (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt f₀
            (dt.arOf vi))), Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.back PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  have hchain := seq_run hrules hR hlin hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.back PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
      f₀ (j : ℕ))
    ?_
  · exact hchain
  · intro ℓ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
        f₀ ((ℓ : ℕ) + 1) =
        (dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG).exitSt (tOf ℓ)
          (dt.gateFam PR.zero PR.one (bOf ℓ) st (tOf ℓ) hc hnG hrdG v
            (dt.gateTagFam PR.zero PR.one (bOf ℓ) st hc hnG hrdG v
              (enterSt ℓ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG
                tOf enterSt f₀ (ℓ : ℕ))
                (dt.back PR.zero PR.one dt.dd0Le st v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr (tOf ℓ))))
          (dt.back PR.zero PR.one dt.dd0Le st v) := by
      simp only [gatesFs]
      rw [dif_pos ℓ.isLt]
    rw [hFa]
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
            (wellG := wellGOf ℓ) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ i) ρ
    exact dt.gateBlock_hStage_pos (bOf ℓ) hc hnG hrdG (wellGOf ℓ) setFail
      hrules' hR hlin hord htop hbot hv hvi hwkSt
      (TestOf ℓ) (hcompatOf ℓ) (tOf ℓ) (htagOf ℓ) (hTestOf ℓ)
      (enterSt ℓ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf
        enterSt f₀ (ℓ : ℕ)) (dt.back PR.zero PR.one dt.dd0Le st v))

include hrules hR hlin hord htop hbot hv hvi hwkSt hcompatOf htagOf in
/-- **The gates' run at a junk address**: the blocks below `ℓ₀` pass, block
`ℓ₀`'s shape test fails, and the run leaves the whole gate sequence through
the failing exit with the fail store applied. -/
theorem gates_run_fail (ℓ₀ : Fin (dt.arOf vi))
    (hTestLt : ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < (ℓ₀ : ℕ) → ∀ u, TestOf ℓ u)
    {u₀ : Univ A R P dt.KIx dt.dd} (hfail : ¬TestOf ℓ₀ u₀)
    (f₀ : dt.CtlIx → A) :
    Relation.ReflTransGen (wideData (Univ A R P dt.KIx dt.dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk 0)) f₀), Sum.inl v,
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt failPh
          (setFail
            (enterSt ℓ₀ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG
              tOf enterSt f₀ (ℓ₀ : ℕ))
              (dt.back PR.zero PR.one dt.dd0Le st v))
            (dt.back PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
        wideTape (PR.trackTape Slot.val
          (dt.back PR.zero PR.one dt.dd0Le st) st.val)
          (PR.syElt PR.blank)⟩ := by
  classical
  have hvnr := not_reg_of_lt_bot hlin hbot hv
  have hne_wk_val : (Slot.wk : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hne_rg_val : (Slot.reg : dt.SlotIx) ≠ Slot.val := fun h => nomatch h
  have hwkOf : ∀ r, dt.back PR.zero PR.one dt.dd0Le st r Slot.wk =
      bitVal PR.zero PR.one (r = v) := by
    intro r
    rw [back_wk, hwkSt]
  -- the passing prefix, up to the failing block's checkpoint
  have hpre := seq_run_prefix hrules hR hlin hbot hv hvi
    (t₀ := Slot.val)
    (restOf := fun _ => dt.back PR.zero PR.one dt.dd0Le st)
    (mOf := fun _ => st.val)
    (fun _ r => hwkOf r) (fun _ r => rfl) (fun _ r => rfl)
    hne_wk_val hne_rg_val
    (fun j => dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
      f₀ (j : ℕ))
    ℓ₀.castSucc ?_
  · refine hpre.trans ?_
    -- the dispatch into the failing block
    have hdsp : (wideData (Univ A R P dt.KIx dt.dd)).Step
        ⟨Sum.inr (PR.stElt (emb (.chk ℓ₀.castSucc))
            (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
              f₀ ((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ))), Sum.inl v,
          wideTape (PR.trackTape Slot.val
            (dt.back PR.zero PR.one dt.dd0Le st) st.val)
            (PR.syElt PR.blank)⟩
        ⟨Sum.inr (PR.stElt (emb (.sub ℓ₀ (Sum.inl .up)))
            (enterSt ℓ₀ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG
              tOf enterSt f₀ (ℓ₀ : ℕ))
              (dt.back PR.zero PR.one dt.dd0Le st v))), Sum.inl v',
          wideTape (PR.trackTape Slot.val
            (dt.back PR.zero PR.one dt.dd0Le st) st.val)
            (PR.syElt PR.blank)⟩ := by
      refine Prog.step_move hR hlin hvi (fun _ _ => rfl) ?_
      have h := hrules (.chk ℓ₀.castSucc) .dspA
      have hlt : ((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ) < dt.arOf vi :=
        ℓ₀.isLt
      have hrule : dt.gatesRule (one := PR.one) (v := vi) (emb := emb)
          (argsG := fun ℓ => dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
          (wellGOf := wellGOf) (setFail := setFail) (enterSt := enterSt)
          (failPh := failPh) (exitPh := exitPh) (.chk ℓ₀.castSucc) .dspA =
          { guard := fun _ g => g Slot.wk = PR.one ∧ g Slot.reg ≠ PR.one
            srcPh := emb (.chk ℓ₀.castSucc)
            dstPh := emb (.sub
              ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩
              (Sum.inl .up))
            dstSt := enterSt
              ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩
            wr := fun _ g => g
            moveRight := True } := dif_pos hlt
      rw [hrule] at h
      refine ⟨rEmb (.chk ℓ₀.castSucc) .dspA, ?_, by rw [h], by rw [h]; rfl,
        ?_, by rw [h], by rw [h]; trivial⟩
      · rw [h]
        constructor
        · rw [Prog.passTracks_of_ne hne_wk_val, hwkOf]
          exact bitVal_pos rfl
        · rw [Prog.passTracks_of_ne hne_rg_val,
            show dt.back PR.zero PR.one dt.dd0Le st v Slot.reg =
              bitVal PR.zero PR.one
                (∃ u : Univ A R P dt.KIx dt.dd, v = wmSeg u) from rfl,
            bitVal_neg (fun hcx => hvnr hcx.choose hcx.choose_spec)]
          exact PR.zero_ne_one
      · rw [h]
        change enterSt ⟨((ℓ₀.castSucc : Fin (dt.arOf vi + 1)) : ℕ), hlt⟩ _
          (PR.passTracks Slot.val
            (dt.back PR.zero PR.one dt.dd0Le st) st.val v) = _
        rw [passTracks_of_back (t := Slot.val)
          (rest := dt.back PR.zero PR.one dt.dd0Le st) (m := st.val)
          (fun r => rfl) v]
        rfl
    refine (Relation.ReflTransGen.single hdsp).trans ?_
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ₀ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ₀ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ₀) hc hnG hrdG)
            (wellG := wellGOf ℓ₀) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ₀.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ₀ i) ρ
    exact dt.gateBlock_hStage_neg (bOf ℓ₀) hc hnG hrdG (wellGOf ℓ₀) setFail
      hrules' hR hlin hord htop hbot hv hvi hwkSt
      (TestOf ℓ₀) (hcompatOf ℓ₀) hfail
      (enterSt ℓ₀ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf
        enterSt f₀ (ℓ₀ : ℕ)) (dt.back PR.zero PR.one dt.dd0Le st v))
  · -- the passing stages strictly below the failing block
    intro ℓ hℓ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hFa : dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
        f₀ ((ℓ : ℕ) + 1) =
        (dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG).exitSt (tOf ℓ)
          (dt.gateFam PR.zero PR.one (bOf ℓ) st (tOf ℓ) hc hnG hrdG v
            (dt.gateTagFam PR.zero PR.one (bOf ℓ) st hc hnG hrdG v
              (enterSt ℓ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG
                tOf enterSt f₀ (ℓ : ℕ))
                (dt.back PR.zero PR.one dt.dd0Le st v))
              (Fin.last (Fintype.card dt.X.Tag)))
            (toLex topTup) (Fin.last (dt.domNr (tOf ℓ))))
          (dt.back PR.zero PR.one dt.dd0Le st v) := by
      simp only [gatesFs]
      rw [dif_pos ℓ.isLt]
    rw [hFa]
    have hrules' : ∀ (i : dt.GateBlockSite) (ρ : dt.GateBlockSh i),
        PR.rules (rEmb (.sub ℓ i) ρ) =
          dt.gateBlockRule (one := PR.one)
            (emb := fun p => emb (.sub ℓ p))
            (args := dt.gateArgs PR.zero PR.one (bOf ℓ) hc hnG hrdG)
            (wellG := wellGOf ℓ) (setFail := setFail)
            (failPh := failPh) (exitPh := emb (.chk ℓ.succ)) i ρ :=
      fun i ρ => hrules (.sub ℓ i) ρ
    exact dt.gateBlock_hStage_pos (bOf ℓ) hc hnG hrdG (wellGOf ℓ) setFail
      hrules' hR hlin hord htop hbot hv hvi hwkSt
      (TestOf ℓ) (hcompatOf ℓ) (tOf ℓ) (htagOf ℓ) (hTestLt ℓ hℓ)
      (enterSt ℓ (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf
        enterSt f₀ (ℓ : ℕ)) (dt.back PR.zero PR.one dt.dd0Le st v))

omit [Finite dt.KIx] [Finite R] [Finite P] hrules hR hlin hord htop hbot hv
  hvi hwkSt hcompatOf htagOf in
/-- **The gates' verdict, characterized**: after the first `n` blocks of
the all-pass path, the flag holds exactly when it held at entry and every
gated block's decoded assignment satisfies its tag's domain sentence. -/
theorem ctlBit_gateFlagC_gatesFs (hzo : PR.zero ≠ PR.one)
    (hEnter : ∀ (ℓ : Fin (dt.arOf vi)) (f : dt.CtlIx → A)
      (g : dt.SlotIx → A),
      dt.ctlBit PR.one (enterSt ℓ f g) dt.gateFlagC ↔
        dt.ctlBit PR.one f dt.gateFlagC)
    (f₀ : dt.CtlIx → A) (n : ℕ) :
    dt.ctlBit PR.one
        (dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt f₀ n)
        dt.gateFlagC ↔
      (dt.ctlBit PR.one f₀ dt.gateFlagC ∧
        ∀ ℓ : Fin (dt.arOf vi), (ℓ : ℕ) < n →
          ((∀ t' : dt.X.Tag,
            wmBlk st.mir (PfpTag.arg (toLex (bOf ℓ)) : PfpTag R P dt.KIx)
              (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ) ∧
          ExpExpansion.DomHolds (X := dt.X)
            (tOf ℓ, decRho dt.ly PR.zero PR.one
              (wmBlk st.mir
                (PfpTag.arg (toLex (bOf ℓ)) : PfpTag R P dt.KIx))))) := by
  induction n with
  | zero =>
    exact ⟨fun h => ⟨h, fun ℓ hℓ => absurd hℓ (Nat.not_lt_zero _)⟩,
      fun h => h.1⟩
  | succ n ih =>
    by_cases hlt : n < dt.arOf vi
    · have hstep : dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf
          enterSt f₀ (n + 1) =
          (dt.gateArgs PR.zero PR.one (bOf ⟨n, hlt⟩) hc hnG hrdG).exitSt
            (tOf ⟨n, hlt⟩)
            (dt.gateFam PR.zero PR.one (bOf ⟨n, hlt⟩) st (tOf ⟨n, hlt⟩) hc
              hnG hrdG v
              (dt.gateTagFam PR.zero PR.one (bOf ⟨n, hlt⟩) st hc hnG hrdG v
                (enterSt ⟨n, hlt⟩ (dt.gatesFs PR.zero PR.one vi st v bOf hc
                  hnG hrdG tOf enterSt f₀ n)
                  (dt.back PR.zero PR.one dt.dd0Le st v))
                (Fin.last (Fintype.card dt.X.Tag)))
              (toLex topTup) (Fin.last (dt.domNr (tOf ⟨n, hlt⟩))))
            (dt.back PR.zero PR.one dt.dd0Le st v) := by
        simp only [gatesFs]
        rw [dif_pos hlt]
      rw [hstep, dt.ctlBit_gateFlagC_gate_domHolds hzo _, hEnter, ih]
      constructor
      · rintro ⟨⟨h0, hall⟩, hn⟩
        refine ⟨h0, fun ℓ hℓ => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hℓn | hℓn
        · exact hall ℓ hℓn
        · have hℓeq : ℓ = ⟨n, hlt⟩ := Fin.ext hℓn
          rw [hℓeq]
          exact hn
      · rintro ⟨h0, hall⟩
        exact ⟨⟨h0, fun ℓ hℓ => hall ℓ (Nat.lt_succ_of_lt hℓ)⟩,
          hall ⟨n, hlt⟩ (Nat.lt_succ_self n)⟩
    · have hstep : dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf
          enterSt f₀ (n + 1) =
          dt.gatesFs PR.zero PR.one vi st v bOf hc hnG hrdG tOf enterSt
            f₀ n := by
        simp only [gatesFs]
        rw [dif_neg hlt]
      rw [hstep, ih]
      refine and_congr Iff.rfl (forall_congr' fun ℓ => ?_)
      constructor
      · intro h hℓ
        exact h (lt_of_lt_of_le ℓ.isLt (Nat.le_of_not_lt hlt))
      · intro h hℓ
        exact h (Nat.lt_succ_of_lt hℓ)

end GatesRun

end KindStage

end PfpData

end Pfp

end DescriptiveComplexity
